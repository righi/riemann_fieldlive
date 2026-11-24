/-
fieldlive (in-process port of fieldlive.cpp): field-level liveness over the loaded environment,
instead of over a lean4export dump. Same algorithm; see fieldlive.cpp for the rules.

Usage (from the project root, so LEAN_PATH points at its oleans):
  lake env fieldlive OUTDIR PROJECT_ROOTS_FILE [ROOT...]
PROJECT_ROOTS_FILE lists top-level module names (e.g. `Development`), one per line; a structure is a
candidate only if it is defined in a module under one of them.
-/
import Lean
open Lean

structure Cand where
  ind : Name
  ctor : Name
  nParams : Nat
  nFields : Nat
  prop : Bool
  read : Array Bool
  pend : Array (Array Expr)
  fieldNames : Array Name
  deriving Inhabited

structure Ctx where
  env : Environment
  candOfInd : Std.HashMap Name Nat
  candOfCtor : Std.HashMap Name Nat
  candOfRec : Std.HashMap Name Nat
  fieldMode : Bool

structure St where
  live : Std.HashSet Name := {}
  vis : Std.HashSet USize
  st : Array Expr := #[]
  cands : Array Cand
  doneInd : Std.HashSet Name := {}
  nVis : Nat := 0

abbrev M := ReaderT Ctx (StateT St IO)

@[inline] def push (e : Expr) : M Unit := modify fun s => { s with st := s.st.push e }

def readField (i k : Nat) : M Unit := do
  let done := (← get).cands[i]!.read[k]!
  if done = true then return
  modify fun s =>
    let p := s.cands[i]!.pend[k]!
    { s with
      st := s.st ++ p
      cands := s.cands.modify i fun c => { c with read := c.read.set! k true, pend := c.pend.set! k #[] } }

def readAll (i : Nat) : M Unit := do
  for k in [0:(← get).cands[i]!.nFields] do readField i k

def markLive (n : Name) : M Unit := modify fun s => { s with live := s.live.insert n }

def ctorType (ci : Option Nat) (ct : ConstructorVal) : M Unit := do
  let fm := (← read).fieldMode
  let mut e := ct.type
  let mut i := 0
  repeat
    match e with
    | .forallE _ ty b _ =>
      let f := i - ct.numParams
      let held ← match ci with
        | some c =>
          if fm && i ≥ ct.numParams && f < ct.numFields then
            pure !(← get).cands[c]!.read[f]!
          else pure false
        | none => pure false
      if held then
        modify fun s => { s with cands := s.cands.modify ci.get! fun c => { c with pend := c.pend.modify f (·.push ty) } }
      else push ty
      e := b; i := i + 1
    | _ => break
  push e

def reachInd (n : Name) : M Unit := do
  let ctx ← read
  let some (.inductInfo I) := ctx.env.find? n | return
  markLive n
  if (← get).doneInd.contains n then return
  modify fun s => { s with doneInd := s.doneInd.insert n }
  push I.type
  for a in I.all do
    if a != n then
      -- reach a (inlined below to avoid mutual recursion): mutual inductives are never candidates
      unless (← get).live.contains a do
        markLive a
        if let some (.inductInfo J) := ctx.env.find? a then
          push J.type
          for cn in J.ctors do
            markLive cn
            if let some (.ctorInfo ct) := ctx.env.find? cn then ctorType none ct
  for cn in I.ctors do
    markLive cn
    if let some (.ctorInfo ct) := ctx.env.find? cn then
      ctorType (ctx.candOfCtor[cn]?) ct

def reach (n : Name) : M Unit := do
  if (← get).live.contains n then return
  markLive n
  let ctx ← read
  let some ci := ctx.env.find? n | return
  match ci with
  | .inductInfo _ => reachInd n
  | .ctorInfo v => reachInd v.induct
  | .recInfo v =>
    push v.type
    for r in v.rules do push r.rhs
    for a in v.all do reachInd a
    if ctx.fieldMode then
      if let some c := ctx.candOfRec[n]? then readAll c
  | _ =>
    push ci.type
    if let some val := ci.value? (allowOpaque := true) then push val

unsafe def run : M Unit := do
  let ctx ← read
  repeat
    let some e := (← get).st.back? | break
    modify fun s => { s with st := s.st.pop }
    if e.approxDepth > 4 then
      if (← get).vis.contains (ptrAddrUnsafe e) then continue
      modify fun s => { s with vis := s.vis.insert (ptrAddrUnsafe e) }
    modify fun s => { s with nVis := s.nVis + 1 }
    let nv := (← get).nVis
    if nv % 50000000 == 0 then
      IO.eprintln s!"  visited {nv / 1000000}M nodes, {(← get).live.size} live, stack {(← get).st.size}"
    match e with
    | .const n _ =>
      reach n
      if ctx.fieldMode then
        if let some c := ctx.candOfCtor[n]? then readAll c
    | .app .. =>
      let h := e.getAppFn
      let args := e.getAppArgs
      let ci : Option Nat := if ctx.fieldMode then
          match h with
          | .const n _ => ctx.candOfCtor[n]?
          | _ => none
        else none
      match ci with
      | some c =>
        let cd := (← get).cands[c]!
        if args.size == cd.nParams + cd.nFields then
          reach h.constName!
          for k in [0:args.size] do
            if k < cd.nParams then push args[k]!
            else
              let f := k - cd.nParams
              if (← get).cands[c]!.read[f]! then push args[k]!
              else modify fun s => { s with cands := s.cands.modify c fun c => { c with pend := c.pend.modify f (·.push args[k]!) } }
        else
          push h; for a in args do push a
      | none => push h; for a in args do push a
    | .lam _ t b _ | .forallE _ t b _ => push t; push b
    | .letE _ t v b _ => push t; push v; push b
    | .proj tn idx s =>
      push s
      reach tn
      if ctx.fieldMode then
        if let some c := ctx.candOfInd[tn]? then
          if idx < (← get).cands[c]!.nFields then readField c idx
    | .mdata _ b => push b
    | _ => pure ()

def nm (n : Name) : String := n.toString (escape := false)

def resultIsProp : Expr → Bool
  | .forallE _ _ b _ => resultIsProp b
  | .sort .zero => true
  | _ => false

unsafe def mainImpl (args : List String) : IO UInt32 := do
  let outdir :: rootsFile :: rest := args | IO.eprintln "usage: fieldlive OUTDIR PROJECT_ROOTS_FILE [ROOT...]"; return 2
  let roots : List Name := if rest.isEmpty then
      [`riemannHypothesis, `riemannZeta_eq_zero_re, `LFunction_ne_zero_of_half_lt_re,
       `LFunction_eq_zero_re, `LFunction_eq_zero_re_of_isPrimitive]
    else rest.map String.toName
  let projRoots : Std.HashSet Name := (← IO.FS.lines rootsFile).foldl
    (fun s l => if l.isEmpty then s else s.insert l.toName) {}
  initSearchPath (← findSysroot)
  IO.eprintln "importing Main ..."
  let env ← importModules #[{ module := `Main }] {} (leakEnv := true)
  let modNames := env.allImportedModuleNames
  IO.eprintln s!"imported {modNames.size} modules"
  let isProject (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => projRoots.contains (modNames[i.toNat]!).getRoot
    | none => true
  -- candidates
  let mut cands : Array Cand := #[]
  let mut candOfInd : Std.HashMap Name Nat := {}
  let mut candOfCtor : Std.HashMap Name Nat := {}
  let mut candOfRec : Std.HashMap Name Nat := {}
  let inds := env.constants.fold (init := #[]) fun acc _ ci =>
    match ci with | .inductInfo v => acc.push v | _ => acc
  for I in inds do
    if I.ctors.length != 1 || I.numIndices != 0 || I.isRec || I.all.length != 1 then continue
    if !isProject I.name then continue
    let some (.ctorInfo ct) := env.find? I.ctors.head! | continue
    if ct.numFields == 0 then continue
    let mut read := Array.replicate ct.numFields false
    let mut ftypes : Array Expr := #[]
    let mut names : Array Name := #[]
    let mut e := ct.type
    let mut k := 0
    repeat
      match e with
      | .forallE bn ty b _ =>
        if k ≥ ct.numParams then ftypes := ftypes.push ty; names := names.push bn
        e := b; k := k + 1
      | _ => break
    -- a later field's type mentioning an earlier field reads it
    for f in [0:ftypes.size] do
      let ty := ftypes[f]!
      if ty.hasLooseBVars then
        for g in [0:f] do
          if ty.hasLooseBVar (f - 1 - g) then read := read.set! g true
    let ci := cands.size
    candOfInd := candOfInd.insert I.name ci
    candOfCtor := candOfCtor.insert ct.name ci
    candOfRec := candOfRec.insert (mkRecName I.name) ci
    cands := cands.push { ind := I.name, ctor := ct.name, nParams := ct.numParams, nFields := ct.numFields,
                          prop := resultIsProp I.type, read, pend := Array.replicate ct.numFields #[],
                          fieldNames := names }
  IO.eprintln s!"candidate structures: {cands.size}"
  -- FIELDLIVE_ONLY=file of "Structure<TAB>field" lines: only those fields may be dropped
  if let some only ← IO.getEnv "FIELDLIVE_ONLY" then
    let allow : Std.HashSet String := (← IO.FS.lines only).foldl (fun s l => if l.isEmpty then s else s.insert l) {}
    let mut kept := 0
    for i in [0:cands.size] do
      let c := cands[i]!
      for k in [0:c.nFields] do
        if allow.contains s!"{nm c.ind}\t{nm c.fieldNames[k]!}" then kept := kept + 1
        else cands := cands.modify i fun c => { c with read := c.read.set! k true }
    IO.eprintln s!"FIELDLIVE_ONLY: {kept} fields may be dropped"
  let rootsFound := roots.filter env.contains
  IO.eprintln s!"roots found: {rootsFound.length} of {roots.length}"
  let mkCtx (fm : Bool) : Ctx := { env, candOfInd, candOfCtor, candOfRec, fieldMode := fm }
  let go : M Unit := do for r in rootsFound do reach r; run
  -- baseline
  let ((), sb) ← (go.run (mkCtx false)).run { vis := Std.HashSet.emptyWithCapacity (1 <<< 20), cands }
  let liveBase := sb.live
  IO.eprintln s!"baseline live constants: {liveBase.size} (visited {sb.nVis} nodes)"
  let ((), sf) ← (go.run (mkCtx true)).run { vis := Std.HashSet.emptyWithCapacity (1 <<< 20), cands }
  let live := sf.live
  IO.eprintln s!"field-mode live constants: {live.size} (visited {sf.nVis} nodes)"
  -- outputs
  IO.FS.createDirAll outdir
  let mut deadFields := 0
  let mut deadStructs := 0
  let df ← IO.FS.Handle.mk (outdir ++ "/dead-fields.tsv") .write
  df.putStrLn "structure\tfield\tprop\tfield_index\tnum_fields\tconstructor_sites_held"
  for c in sf.cands do
    if !live.contains c.ind then continue
    let mut any := false
    for k in [0:c.nFields] do
      if !c.read[k]! then
        deadFields := deadFields + 1; any := true
        df.putStrLn s!"{nm c.ind}\t{nm c.fieldNames[k]!}\t{if c.prop then 1 else 0}\t{k}\t{c.nFields}\t{c.pend[k]!.size}"
    if any then deadStructs := deadStructs + 1
  df.flush
  let dr ← IO.FS.Handle.mk (outdir ++ "/dropped-constants.txt") .write
  let mut dropped := 0
  for n in liveBase do
    if !live.contains n && env.contains n then
      dropped := dropped + 1; dr.putStrLn (nm n)
  dr.flush
  -- kernel edges among dropped constants: "src,,dst" (an inductive also uses its constructors' types)
  let de ← IO.FS.Handle.mk (outdir ++ "/dead-edges.csv") .write
  for n in liveBase do
    if live.contains n then continue
    let some ci := env.find? n | continue
    let mut used := ci.getUsedConstantsAsSet
    if let .inductInfo I := ci then
      for cn in I.ctors do
        used := used.insert cn
        if let some cc := env.find? cn then used := used.union cc.getUsedConstantsAsSet
    for m in used do
      if m != n && liveBase.contains m && !live.contains m then de.putStrLn s!"{nm n},,{nm m}"
  de.flush
  IO.eprintln s!"dead fields: {deadFields} in {deadStructs} live structures; constants dropped: {dropped}"
  -- per dead field: dropped constants reachable from what it holds back
  let fa ← IO.FS.Handle.mk (outdir ++ "/field-reach.tsv") .write
  for c in sf.cands do
    if !live.contains c.ind then continue
    for k in [0:c.nFields] do
      if c.read[k]! then continue
      let mut vis : Std.HashSet USize := {}
      let mut got : Std.HashSet Name := {}
      let mut gotL : Array Name := #[]
      let mut st := c.pend[k]!
      while h : st.size > 0 do
        let e := st.back
        st := st.pop
        if vis.contains (ptrAddrUnsafe e) then continue
        vis := vis.insert (ptrAddrUnsafe e)
        match e with
        | .const n _ =>
          if liveBase.contains n && !live.contains n && !got.contains n then
            got := got.insert n; gotL := gotL.push n
            if let some ci := env.find? n then
              st := st.push ci.type
              if let some v := ci.value? (allowOpaque := true) then st := st.push v
              if let .inductInfo I := ci then
                for cn in I.ctors do
                  if let some cc := env.find? cn then st := st.push cc.type
        | .app f a | .lam _ f a _ | .forallE _ f a _ => st := st.push f |>.push a
        | .letE _ t v b _ => st := st.push t |>.push v |>.push b
        | .proj _ _ s | .mdata _ s => st := st.push s
        | _ => pure ()
      fa.putStrLn s!"{nm c.ind}\t{nm c.fieldNames[k]!}\t{gotL.size}\t{";".intercalate (gotL.toList.map nm)}"
  fa.flush
  IO.println s!"dead_fields\t{deadFields}\ndead_structs\t{deadStructs}\ndropped_constants\t{dropped}"
  return 0

@[implemented_by mainImpl]
opaque mainSafe : List String → IO UInt32

def main (args : List String) : IO UInt32 := mainSafe args
