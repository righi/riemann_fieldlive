/-
fieldlive: what a built Lean project's root theorems do not need, over the loaded environment.

Walks the kernel terms reachable from the roots. In `fields` mode the arguments of a fully applied
constructor of a project structure are held back, one per field, until something reads that field
(a projection, the recursor or `casesOn`, a partial or bare use of the constructor, or a later
field's type); fields still held back at the end are dead. `args` mode does the same for unused
explicit `Prop` arguments of theorems, `unreachable` mode only computes the closure. A baseline
pass, with every field read, gives the ordinary closure to compare against. The prune plan maps
what is dropped back to source ranges.

Run `fieldlive --help` for the options, from the project root with `lake env`.
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
  pend : Array (Array (Expr × Name))
  fieldNames : Array Name
  deriving Inhabited

/-- a theorem with explicit Prop arguments its proof never uses (`slots`: their argument positions) -/
structure ACand where
  thm : Name
  slots : Array Nat
  names : Array Name
  used : Array Bool
  pend : Array (Array (Expr × Name))
  deriving Inhabited

structure Ctx where
  env : Environment
  candOfInd : Std.HashMap Name Nat
  candOfCtor : Std.HashMap Name Nat
  candOfRec : Std.HashMap Name Nat
  fieldMode : Bool
  paths : Bool := false
  argMode : Bool := false
  argOf : Std.HashMap Name Nat := {}
  /-- defined in a project module (outside Lean, Std, Mathlib, ...) -/
  isProj : Name → Bool
  /-- also walk into library constants (FIELDLIVE_DEEP=1; slower, same project results) -/
  deep : Bool

structure St where
  live : Std.HashSet Name := {}
  vis : Std.HashSet USize
  st : Array (Expr × Name) := #[]
  cur : Name := .anonymous
  edges : Std.HashSet (Name × Name) := {}
  cands : Array Cand
  acands : Array ACand := #[]
  doneInd : Std.HashSet Name := {}
  nVis : Nat := 0

abbrev M := ReaderT Ctx (StateT St IO)

@[inline] def push (e : Expr) : M Unit := modify fun s => { s with st := s.st.push (e, s.cur) }

/-- record the reference `cur → n` (when tracking paths) -/
@[inline] def edge (n : Name) : M Unit := do
  if (← read).paths then modify fun s => { s with edges := s.edges.insert (s.cur, n) }

/-- run `act` with `n` as owner of what it pushes -/
@[inline] def withCur (n : Name) (act : M Unit) : M Unit := do
  let o := (← get).cur
  modify fun s => { s with cur := n }
  act
  modify fun s => { s with cur := o }

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

def useArg (i s : Nat) : M Unit := do
  if (← get).acands[i]!.used[s]! then return
  modify fun st =>
    let p := st.acands[i]!.pend[s]!
    { st with
      st := st.st ++ p
      acands := st.acands.modify i fun c => { c with used := c.used.set! s true, pend := c.pend.set! s #[] } }

def useAllArgs (i : Nat) : M Unit := do
  for s in [0:(← get).acands[i]!.slots.size] do useArg i s

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
        modify fun s => { s with cands := s.cands.modify ci.get! fun c => { c with pend := c.pend.modify f (·.push (ty, s.cur)) } }
      else push ty
      e := b; i := i + 1
    | _ => break
  push e

def reachInd (n : Name) : M Unit := do
  let ctx ← read
  let some (.inductInfo I) := ctx.env.find? n | return
  edge n
  markLive n
  if (← get).doneInd.contains n then return
  withCur n do
    modify fun s => { s with doneInd := s.doneInd.insert n }
    push I.type
    for a in I.all do
      if a != n then
        -- reach a (inlined below to avoid mutual recursion): mutual inductives are never candidates
        edge a
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
  edge n
  if (← get).live.contains n then return
  markLive n
  let ctx ← read
  -- A library constant's type and value cannot mention project constants (libraries do not import
  -- the project), so there is nothing to find inside them: mark it live and stop.
  if !ctx.deep && !ctx.isProj n then return
  let some ci := ctx.env.find? n | return
  withCur n do
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
    let some (e, o) := (← get).st.back? | break
    modify fun s => { s with st := s.st.pop, cur := o }
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
      if ctx.argMode then
        if let some i := ctx.argOf[n]? then useAllArgs i
    | .app .. =>
      let h := e.getAppFn
      let args := e.getAppArgs
      let ai : Option Nat := if ctx.argMode then
          match h with
          | .const n _ => ctx.argOf[n]?
          | _ => none
        else none
      if let some i := ai then
        -- a call of a theorem with unused arguments: hold back the unused ones
        reach h.constName!
        let slots := (← get).acands[i]!.slots
        for k in [0:args.size] do
          match slots.findIdx? (· == k) with
          | some s =>
            if (← get).acands[i]!.used[s]! then push args[k]!
            else modify fun st => { st with acands := st.acands.modify i fun c => { c with pend := c.pend.modify s (·.push (args[k]!, st.cur)) } }
          | none => push args[k]!
        -- partially applied: a missing unused argument is supplied elsewhere; count it as used
        for s in [0:slots.size] do
          if slots[s]! ≥ args.size then useArg i s
        continue
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
              else modify fun s => { s with cands := s.cands.modify c fun c => { c with pend := c.pend.modify f (·.push (args[k]!, s.cur)) } }
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

/-- explicit arguments of a theorem that its proof never uses: positions `k` such that the value's
`k`-th leading lambda variable occurs neither in the body nor in a later binder type nor in the
statement. Only positions that are syntactic foralls of the statement are considered. -/
def unusedArgs (type val : Expr) : Array (Nat × Name) := Id.run do
  let mut tys : Array (BinderInfo × Name × Expr) := #[]
  let mut t := type
  repeat
    match t with
    | .forallE n ty b bi => tys := tys.push (bi, n, ty); t := b
    | _ => break
  let mut vtys : Array Expr := #[]
  let mut v := val
  while vtys.size < tys.size do
    match v with
    | .lam _ ty b _ => vtys := vtys.push ty; v := b
    | _ => break
  let m := vtys.size
  -- the statement under the first `m` binders
  let mut tres := type
  for _ in [0:m] do tres := tres.bindingBody!
  let mut out := #[]
  for k in [0:m] do
    let (bi, n, _) := tys[k]!
    if bi != .default then continue
    let i := m - 1 - k
    if v.hasLooseBVar i || tres.hasLooseBVar i then continue
    let mut dep := false
    for j in [k+1:m] do
      if vtys[j]!.hasLooseBVar (j - 1 - k) || (tys[j]!).2.2.hasLooseBVar (j - 1 - k) then dep := true; break
    if !dep then out := out.push (k, n)
  return out

/-- keep the positions whose binder type is a proposition; also a short rendering of each type -/
def propArgs (env : Environment) (cs : Array (Name × Array (Nat × Name))) :
    IO (Array (Name × Array (Nat × Name × String))) := do
  let act : MetaM (Array (Name × Array (Nat × Name × String))) := do
    let mut out := #[]
    for (n, ks) in cs do
      let some ci := env.find? n | continue
      let maxK := ks.foldl (fun a (k, _) => max a (k + 1)) 0
      try
        let r ← Meta.forallBoundedTelescope ci.type (some maxK) fun xs _ => do
          let mut r := #[]
          for (k, bn) in ks do
            if h : k < xs.size then
              let ty ← Meta.inferType xs[k]
              if ← Meta.isProp ty then
                let s := toString (← Meta.ppExpr ty) |>.replace "\n" " "
                let s := if s.length > 120 then (s.take 117).toString ++ "..." else s
                r := r.push (k, bn, s)
          return r
        if !r.isEmpty then out := out.push (n, r)
      catch _ => pure ()
    return out
  let (r, _) ← (act.run' {} {}).toIO { fileName := "<fieldlive>", fileMap := default, maxHeartbeats := 0 } { env }
  return r

/-- dropped constants (live in `liveBase`, not in `live`) reachable from the expressions `es` -/
unsafe def freedFrom (env : Environment) (isProj : Name → Bool) (liveBase live : Std.HashSet Name) (es : Array Expr) : Array Name := Id.run do
  let mut vis : Std.HashSet USize := {}
  let mut got : Std.HashSet Name := {}
  let mut gotL : Array Name := #[]
  let mut st := es
  while h : st.size > 0 do
    let e := st.back
    st := st.pop
    if vis.contains (ptrAddrUnsafe e) then continue
    vis := vis.insert (ptrAddrUnsafe e)
    match e with
    | .const n _ =>
      if liveBase.contains n && !live.contains n && !got.contains n && isProj n then
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
  return gotL

/-- `dropped-constants.txt` and `dead-edges.csv` ("src,,dst"; an inductive also uses its
constructors' types) for `prune.py`; returns the number dropped -/
def writeDropped (env : Environment) (outdir : String) (isProj : Name → Bool) (liveBase live : Std.HashSet Name) : IO Nat := do
  let dr ← IO.FS.Handle.mk (outdir ++ "/dropped-constants.txt") .write
  let mut dropped := 0
  for n in liveBase do
    if !live.contains n && env.contains n && isProj n then
      dropped := dropped + 1; dr.putStrLn (nm n)
  dr.flush
  let de ← IO.FS.Handle.mk (outdir ++ "/dead-edges.csv") .write
  for n in liveBase do
    if live.contains n || !isProj n then continue
    let some ci := env.find? n | continue
    let mut used := ci.getUsedConstantsAsSet
    if let .inductInfo I := ci then
      for cn in I.ctors do
        used := used.insert cn
        if let some cc := env.find? cn then used := used.union cc.getUsedConstantsAsSet
    for m in used do
      if m != n && liveBase.contains m && !live.contains m && isProj m then de.putStrLn s!"{nm n},,{nm m}"
  de.flush
  return dropped

/-! ## Command line -/

structure Config where
  outdir : String := ""
  /-- `fields` (dead structure fields), `args` (unused theorem arguments) or `unreachable` -/
  mode : String := "fields"
  imports : Array Name := #[]
  roots : Array Name := #[]
  rootModules : Array Name := #[]
  /-- top-level module names of the project; empty: detect from where the `.olean` files live -/
  projectRoots : Array Name := #[]
  /-- modules (or module prefixes) whose declarations are kept and never edited -/
  protect : Array Name := #[]
  only? : Option String := none
  deep : Bool := false
  paths : Bool := false
  liveOnly : Bool := false
  liveOut? : Option String := none
  before? : Option String := none
  plan : Bool := true

def usage : String := "usage: fieldlive [OPTIONS] OUTDIR

Walks the kernel terms of the declarations reachable from the root theorems of a built Lean
project and reports what they do not need. Run it with `lake env` in the project, so that
LEAN_PATH points at the project's .olean files.

  --mode MODE           fields (default): fields of project structures nothing reads
                        args: explicit Prop arguments of theorems their proofs never use
                        unreachable: project declarations the roots do not need at all
  --import MOD          module to load (repeatable; default: the root modules, or Main)
  --root NAME           a root declaration (repeatable)
  --root-module MOD     every declaration of MOD is a root (repeatable). Without --root or
                        --root-module, the declarations of the --import modules are the roots.
  --roots-file FILE     root declarations, one per line
  --project MOD         top-level module name of the project (repeatable). Default: every module
                        whose .olean is outside the toolchain and outside .lake/packages.
  --protect MOD         keep every declaration of MOD and of modules under it; in args mode its
                        theorems are not candidates (repeatable; the root modules always are)
  --only FILE           only these fields (Structure<TAB>field) or arguments (theorem<TAB>index)
                        may be dropped
  --live-out FILE       write the baseline live project constants (a snapshot before an edit)
  --before FILE         such a snapshot: report what an edit freed (fields and args modes)
  --no-plan             do not write prune-plan.tsv
  --deep                also walk into library constants (slower, same project results)
  --paths               write parents.tsv, a shortest reference path to every live constant
  --live-only           skip the baseline; write only the live set (fields mode)

The legacy form `fieldlive OUTDIR PROJECT_ROOTS_FILE [ROOT...]` and the FIELDLIVE_* environment
variables still work."

/-- parse the command line, then fill in the legacy environment variables -/
def parseArgs (args : List String) : IO (Except String Config) := do
  let mut c : Config := {}
  let mut pos : Array String := #[]
  let mut rest := args
  let valued := ["--mode", "--import", "--root", "--root-module", "--project", "--protect", "--only",
    "--live-out", "--before", "--roots-file"]
  repeat
    match rest with
    | [] => break
    | a :: r =>
      rest := r
      if valued.contains a then
        let v :: r' := rest | return .error s!"{a} needs an argument"
        rest := r'
        match a with
        | "--mode" => c := { c with mode := v }
        | "--import" => c := { c with imports := c.imports.push v.toName }
        | "--root" => c := { c with roots := c.roots.push v.toName }
        | "--root-module" => c := { c with rootModules := c.rootModules.push v.toName }
        | "--project" => c := { c with projectRoots := c.projectRoots.push v.toName }
        | "--protect" => c := { c with protect := c.protect.push v.toName }
        | "--only" => c := { c with only? := some v }
        | "--live-out" => c := { c with liveOut? := some v }
        | "--before" => c := { c with before? := some v }
        | _ =>
          for l in ← IO.FS.lines v do
            let t := l.trimAscii.toString
            if !t.isEmpty then c := { c with roots := c.roots.push t.toName }
      else match a with
        | "--no-plan" => c := { c with plan := false }
        | "--deep" => c := { c with deep := true }
        | "--paths" => c := { c with paths := true }
        | "--live-only" => c := { c with liveOnly := true }
        | "-h" | "--help" => return .error ""
        | _ =>
          if a.startsWith "--" then return .error s!"unknown option {a}"
          pos := pos.push a
  let some outdir := pos[0]? | return .error "missing OUTDIR"
  c := { c with outdir }
  -- legacy: OUTDIR PROJECT_ROOTS_FILE [ROOT...]
  if let some (f : String) := pos[1]? then
    let ls ← IO.FS.lines f
    c := { c with projectRoots := ls.foldl (fun acc l => if l.isEmpty then acc else acc.push l.toName) c.projectRoots }
    c := { c with roots := c.roots ++ (pos.extract 2 pos.size).map String.toName }
  if let some m ← IO.getEnv "FIELDLIVE_MODULE" then c := { c with imports := c.imports.push m.toName }
  if let some m ← IO.getEnv "FIELDLIVE_MODE" then c := { c with mode := m }
  if let some f ← IO.getEnv "FIELDLIVE_ONLY" then c := { c with only? := c.only?.getD f }
  if let some f ← IO.getEnv "FIELDLIVE_LIVE_OUT" then c := { c with liveOut? := c.liveOut?.getD f }
  if let some f ← IO.getEnv "FIELDLIVE_BEFORE" then c := { c with before? := c.before?.getD f }
  if (← IO.getEnv "FIELDLIVE_DEEP").isSome then c := { c with deep := true }
  if (← IO.getEnv "FIELDLIVE_PATHS").isSome then c := { c with paths := true }
  if (← IO.getEnv "FIELDLIVE_LIVE_ONLY").isSome then c := { c with liveOnly := true }
  unless ["fields", "args", "unreachable"].contains c.mode do return .error s!"unknown mode {c.mode}"
  if c.imports.isEmpty then
    c := { c with imports := if c.rootModules.isEmpty then #[`Main] else c.rootModules }
  return .ok c

/-! ## Project detection and extra roots -/

/-- modules of the project: under one of `roots` if given, otherwise every module whose `.olean`
is neither in the toolchain nor in a Lake dependency (`.lake/packages/`) -/
def projectModules (modNames : Array Name) (roots : Array Name) : IO (Std.HashSet Name) := do
  if !roots.isEmpty then
    return modNames.foldl (fun s m => if roots.contains m.getRoot then s.insert m else s) {}
  let sysroot := (← findSysroot).toString
  let mut s : Std.HashSet Name := {}
  for m in modNames do
    let p := (← findOLean m).toString
    if p.startsWith sysroot || (p.splitOn "/.lake/packages/").length > 1 then continue
    s := s.insert m
  return s

/-- whether `m` is `p` or a module under `p` -/
def underModule (ps : Array Name) (m : Name) : Bool := ps.any (·.isPrefixOf m)

/-- declarations used in ways kernel terms do not show: meta code (syntax, macros, elaborators,
tactics), `implemented_by` targets. They are kept as roots. -/
def isMetaLike (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  isMarkedMeta env n ||
  ci.type.getUsedConstants.any fun c =>
    [`Lean.Syntax, `Lean.ParserDescr, `Lean.TrailingParserDescr, `Lean.Macro, `Lean.Elab,
     `Lean.Meta, `Lean.Parser, `Lean.PrettyPrinter].any (·.isPrefixOf c)

/-- the name a closed `Lean.Name` expression builds, as meta code writes name literals -/
partial def exprToName? (e : Expr) : Option Name :=
  let strs (as : Array Expr) : Option (Array String) := as.mapM fun | .lit (.strVal s) => some s | _ => none
  match e.getAppFn, e.getAppArgs with
  | .const ``Name.anonymous _, #[] => some .anonymous
  | .const c _, as =>
    if c == ``Name.str || c == ``Name.mkStr then
      match as with
      | #[p, .lit (.strVal s)] => (exprToName? p).map (·.str s)
      | _ => none
    else
    if (c.getPrefix == ``Name) && (c.toString.startsWith "Lean.Name.mkStr") then
      (strs as).map fun ss => ss.foldl (·.str ·) .anonymous
    else none
  | _, _ => none

/-- project declarations that meta code names by a literal (notations, macros, unexpanders) -/
def namedByMeta (env : Environment) (isProj : Name → Bool) : Array Name := Id.run do
  let mut out : NameSet := {}
  for (n, ci) in env.constants.toList do
    if !isProj n then continue
    unless isMetaLike env n ci || ci.type.getUsedConstants.contains ``Name do continue
    let some v := ci.value? (allowOpaque := true) | continue
    let mut st := #[v]
    while h : st.size > 0 do
      let e := st.back
      st := st.pop
      match exprToName? e with
      | some m => if !m.isAnonymous && env.contains m && isProj m then out := out.insert m
      | none =>
        match e with
        | .app f a | .lam _ f a _ | .forallE _ f a _ => st := st.push f |>.push a
        | .letE _ t x b _ => st := st.push t |>.push x |>.push b
        | .mdata _ b | .proj _ _ b => st := st.push b
        | _ => pure ()
  return out.toArray

/-! ## Source ranges and the prune plan -/

structure Range where
  mod : Name
  sl : Nat
  sc : Nat
  el : Nat
  ec : Nat
  deriving BEq, Hashable, Inhabited

def declRange? (env : Environment) (n : Name) : Option DeclarationRange :=
  let r := declRangeExt.find? (level := .exported) env n <|> declRangeExt.find? (level := .server) env n
  r.map (·.range)

/-- the units a deletion works on: each declaration whose source range is not inside another's,
with every constant whose range lies inside it or which has no range but whose name extends it
(equation lemmas, `match_` and `_proof_` auxiliaries, projections, `where` helpers). -/
def units (env : Environment) (modNames : Array Name) (consts : Array Name) :
    Std.HashMap Name Nat × Array Range := Id.run do
  let mut rangeOf : Std.HashMap Name Range := {}
  for n in consts do
    let some i := env.getModuleIdxFor? n | continue
    let some r := declRange? env n | continue
    rangeOf := rangeOf.insert n { mod := modNames[i.toNat]!, sl := r.pos.line, sc := r.pos.column,
                                  el := r.endPos.line, ec := r.endPos.column }
  -- outermost ranges, per module: sort by start, longest first, and sweep
  let rs := (rangeOf.fold (init := (#[] : Array Range)) fun a _ r => a.push r).qsort fun a b =>
    if a.mod != b.mod then a.mod.lt b.mod
    else if a.sl != b.sl then a.sl < b.sl
    else if a.sc != b.sc then a.sc < b.sc
    else if a.el != b.el then a.el > b.el
    else a.ec > b.ec
  let mut outer : Std.HashMap Range Nat := {}
  let mut us : Array Range := #[]
  for r in rs do
    if outer.contains r then continue
    match us.back? with
    | some u =>
      if u.mod == r.mod && (u.sl < r.sl || (u.sl == r.sl && u.sc ≤ r.sc)) && (r.el < u.el || (r.el == u.el && r.ec ≤ u.ec)) then
        outer := outer.insert r (us.size - 1)
      else outer := outer.insert r us.size; us := us.push r
    | none => outer := outer.insert r us.size; us := us.push r
  let mut unitOf : Std.HashMap Name Nat := {}
  for n in consts do
    if let some r := rangeOf[n]? then unitOf := unitOf.insert n outer[r]!
  for n in consts do
    if unitOf.contains n then continue
    let mut p := n.getPrefix
    while !p.isAnonymous do
      if let some u := unitOf[p]? then unitOf := unitOf.insert n u; break
      p := p.getPrefix
  return (unitOf, us)

/-- constants a constant's declaration mentions (an inductive: also its constructors' types) -/
def usedBy (env : Environment) (n : Name) : NameSet := Id.run do
  let some ci := env.find? n | return {}
  let mut used := ci.getUsedConstantsAsSet
  if let .inductInfo I := ci then
    for cn in I.ctors do
      if let some cc := env.find? cn then used := used.union cc.getUsedConstantsAsSet
  return used

/-- `prune-plan.tsv`: the source ranges to delete. A unit is deleted when it holds a dropped
constant and nothing live; then, until nothing changes, a deleted unit comes back when a constant
that stays (outside every deleted unit) mentions one of its constants. Returns (deleted, kept). -/
def writePlan (env : Environment) (modNames : Array Name) (outdir : String) (isProj : Name → Bool)
    (dropped live : Std.HashSet Name) : IO (Nat × Nat) := do
  let consts := env.constants.fold (init := #[]) fun acc n _ => if isProj n then acc.push n else acc
  let (unitOf, us) := units env modNames consts
  let mut members : Array (Array Name) := Array.replicate us.size #[]
  for (n, u) in unitOf do members := members.modify u (·.push n)
  let mut del : Array Bool := Array.replicate us.size false
  for u in [0:us.size] do
    let ms := members[u]!
    if ms.any dropped.contains && !ms.any live.contains then del := del.set! u true
  -- constants that stay but are not live: they still have to compile
  let mut work : Array Name := #[]
  for n in consts do
    if live.contains n then continue
    match unitOf[n]? with
    | some u => if !del[u]! then work := work.push n
    | none => work := work.push n
  let kept ← IO.FS.Handle.mk (outdir ++ "/plan-kept.tsv") .write
  kept.putStrLn "constant\tmentioned_by"
  let mut nKept := 0
  while h : work.size > 0 do
    let n := work.back
    work := work.pop
    for m in usedBy env n do
      let some u := unitOf[m]? | continue
      if del[u]! then
        del := del.set! u false
        nKept := nKept + 1
        kept.putStrLn s!"{nm m}\t{nm n}"
        for k in members[u]! do
          if !live.contains k then work := work.push k
  kept.flush
  let sp ← getSrcSearchPath
  let pl ← IO.FS.Handle.mk (outdir ++ "/prune-plan.tsv") .write
  pl.putStrLn "file\tmodule\tstart_line\tstart_col\tend_line\tend_col\tdeclarations"
  let mut nDel := 0
  for u in [0:us.size] do
    unless del[u]! do continue
    nDel := nDel + 1
    let r := us[u]!
    let file := match ← sp.findModuleWithExt "lean" r.mod with
      | some f => f.toString
      | none => ""
    let names := members[u]!.filterMap fun n =>
      match privateToUserName? n with
      | some m => some s!"private {nm m}"
      | none => if n.isInternalDetail then none else some (nm n)
    pl.putStrLn s!"{file}\t{nm r.mod}\t{r.sl}\t{r.sc}\t{r.el}\t{r.ec}\t{";".intercalate names.toList}"
  pl.flush
  return (nDel, nKept)

/-! ## Main -/

unsafe def mainImpl (args : List String) : IO UInt32 := do
  let cfg ← match ← parseArgs args with
    | .ok c => pure c
    | .error e =>
      unless e.isEmpty do IO.eprintln s!"fieldlive: {e}"
      IO.eprintln usage
      return 2
  let outdir := cfg.outdir
  initSearchPath (← findSysroot)
  IO.eprintln s!"importing {cfg.imports.toList} ..."
  let env ← importModules (cfg.imports.map fun m => { module := m }) {} (leakEnv := true)
  let modNames := env.allImportedModuleNames
  IO.eprintln s!"imported {modNames.size} modules"
  let projMods ← projectModules modNames cfg.projectRoots
  IO.eprintln s!"project modules: {projMods.size}"
  let isProject (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => projMods.contains modNames[i.toNat]!
    | none => true
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => modNames[i.toNat]!
  let rootMods := if cfg.rootModules.isEmpty && cfg.roots.isEmpty then cfg.imports else cfg.rootModules
  let protect := cfg.protect ++ rootMods
  let isProtected (n : Name) : Bool := match modOf n with
    | some m => underModule protect m
    | none => false
  -- roots: the named declarations, every declaration of a root or protected module, and meta code
  let mut roots : Array Name := cfg.roots.filter env.contains
  IO.eprintln s!"roots named: {roots.size} of {cfg.roots.size} found"
  let mut nMeta := 0
  for (n, ci) in env.constants.toList do
    if !isProject n then continue
    if isProtected n && !n.isInternalDetail then roots := roots.push n
    else if isMetaLike env n ci then roots := roots.push n; nMeta := nMeta + 1
    if let some t := Compiler.getImplementedBy? env n then roots := roots.push t
  let named := namedByMeta env isProject
  roots := roots ++ named
  IO.eprintln s!"roots: {roots.size} ({nMeta} meta declarations, {named.size} declarations named by meta code)"
  -- candidates
  let mut cands : Array Cand := #[]
  let mut candOfInd : Std.HashMap Name Nat := {}
  let mut candOfCtor : Std.HashMap Name Nat := {}
  let mut candOfRec : Std.HashMap Name Nat := {}
  let inds := env.constants.fold (init := #[]) fun acc _ ci =>
    match ci with | .inductInfo v => acc.push v | _ => acc
  for I in inds do
    if I.ctors.length != 1 || I.numIndices != 0 || I.isRec || I.all.length != 1 then continue
    if !isProject I.name || isProtected I.name then continue
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
  if cfg.mode != "fields" then
    cands := cands.map fun c => { c with read := c.read.map fun _ => true }
  else
    IO.eprintln s!"candidate structures: {cands.size}"
    if let some only := cfg.only? then
      let allow : Std.HashSet String := (← IO.FS.lines only).foldl (fun s l => if l.isEmpty then s else s.insert l) {}
      let mut kept := 0
      for i in [0:cands.size] do
        let c := cands[i]!
        for k in [0:c.nFields] do
          if allow.contains s!"{nm c.ind}\t{nm c.fieldNames[k]!}" then kept := kept + 1
          else cands := cands.modify i fun c => { c with read := c.read.set! k true }
      IO.eprintln s!"--only: {kept} fields may be dropped"
  let deep := cfg.deep
  IO.eprintln s!"walk: {if deep then "deep (into library constants)" else "project constants only"}"
  let paths := cfg.paths
  let mkCtx (fm : Bool) (am := false) (argOf : Std.HashMap Name Nat := {}) (pb := false) : Ctx :=
    { env, candOfInd, candOfCtor, candOfRec, fieldMode := fm, paths := paths && (fm || am || pb), argMode := am, argOf, isProj := isProject, deep }
  let go : M Unit := do for r in roots do reach r; run
  IO.FS.createDirAll outdir
  let writeLive (sf : St) : IO Unit := do
    let h ← IO.FS.Handle.mk (outdir ++ "/live-constants.txt") .write
    for n in sf.live do if env.contains n then h.putStrLn (nm n)
    h.flush
    if paths then
      let mut adj : Std.HashMap Name (Array Name) := {}
      for (a, b) in sf.edges do
        if a != b then adj := adj.alter a fun | some v => some (v.push b) | none => some #[b]
      -- BFS from the roots (owner `.anonymous`)
      let mut par : Std.HashMap Name (Name × Nat) := {}
      let mut q : Array Name := #[.anonymous]
      let mut qi := 0
      par := par.insert .anonymous (.anonymous, 0)
      while qi < q.size do
        let a := q[qi]!
        qi := qi + 1
        let d := (par[a]!).2
        for b in adj.getD a #[] do
          unless par.contains b do
            par := par.insert b (a, d + 1); q := q.push b
      let t ← IO.FS.Handle.mk (outdir ++ "/parents.tsv") .write
      t.putStrLn "constant\tdepth\tparent"
      for n in q do
        if n != .anonymous then
          let (p, d) := par[n]!
          t.putStrLn s!"{nm n}\t{d}\t{if p == .anonymous then "ROOT" else nm p}"
      t.flush
      IO.eprintln s!"path edges: {sf.edges.size}; tree nodes: {q.size - 1}"
  if cfg.liveOnly then
    let ((), sf) ← (go.run (mkCtx (cfg.mode == "fields"))).run { vis := Std.HashSet.emptyWithCapacity (1 <<< 20), cands }
    IO.eprintln s!"live constants: {sf.live.size} (visited {sf.nVis} nodes)"
    writeLive sf
    return 0
  -- baseline
  let t0 ← IO.monoMsNow
  let ((), sb) ← (go.run (mkCtx false (pb := cfg.mode == "unreachable"))).run { vis := Std.HashSet.emptyWithCapacity (1 <<< 20), cands }
  IO.eprintln s!"baseline pass: {((← IO.monoMsNow) - t0) / 1000} s"
  let liveBase := sb.live
  IO.eprintln s!"baseline live constants: {liveBase.size} (visited {sb.nVis} nodes)"
  if let some f := cfg.liveOut? then
    let h ← IO.FS.Handle.mk f .write
    for n in liveBase do if isProject n then h.putStrLn (nm n)
    h.flush
  -- the constants an edit can have freed: live before it (--before), or live in the baseline now
  let pool : Std.HashSet Name ← match cfg.before? with
    | some f => do
      let ls ← IO.FS.lines f
      pure (ls.foldl (fun s l => if l.isEmpty then s else s.insert (String.toName l)) {})
    | none => pure liveBase
  let plan (live : Std.HashSet Name) (dropped : Std.HashSet Name) : IO Unit := do
    if !cfg.plan then return
    let (nDel, nKept) ← writePlan env modNames outdir isProject dropped live
    IO.eprintln s!"prune plan: {nDel} declarations to delete; {nKept} kept because code that stays mentions them"
  let droppedSet (live : Std.HashSet Name) : Std.HashSet Name :=
    pool.fold (init := {}) fun s n => if !live.contains n && env.contains n && isProject n then s.insert n else s
  -- every project constant: module, kind, whether its type ends in Prop, live in baseline / final pass
  let writeInfo (live : Std.HashSet Name) : IO Unit := do
    let ci ← IO.FS.Handle.mk (outdir ++ "/constants-info.tsv") .write
    ci.putStrLn "constant\tmodule\tkind\tprop_valued\tlive_base\tlive_field"
    let projConsts := env.constants.fold (init := #[]) fun acc n c =>
      if n.isInternalDetail || !isProject n then acc else acc.push (n, c)
    for (n, c) in projConsts do
      let some i := env.getModuleIdxFor? n | continue
      let kind := match c with
        | .thmInfo _ => "thm" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
        | .inductInfo _ => "ind" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"
      ci.putStrLn s!"{nm n}\t{nm modNames[i.toNat]!}\t{kind}\t{if resultIsProp c.type then 1 else 0}\t{if liveBase.contains n then 1 else 0}\t{if live.contains n then 1 else 0}"
    ci.flush
  -- unreachable: project declarations outside the baseline closure
  if cfg.mode == "unreachable" then
    writeLive sb
    writeInfo liveBase
    let dropped : Std.HashSet Name := env.constants.fold (init := {}) fun s n _ =>
      if isProject n && !liveBase.contains n then s.insert n else s
    let nDropped ← writeDropped env outdir isProject (env.constants.fold (init := {}) fun s n _ => if isProject n then s.insert n else s) liveBase
    IO.eprintln s!"unreachable project constants: {nDropped}"
    plan liveBase dropped
    IO.println s!"unreachable_constants\t{nDropped}"
    return 0
  -- args: unused theorem arguments instead of dead fields (fields all count as read)
  if cfg.mode == "args" then
    let mut syn : Array (Name × Array (Nat × Name)) := #[]
    for n in liveBase do
      if n.isInternalDetail || !isProject n || isProtected n then continue
      let some (.thmInfo t) := env.find? n | continue
      let ks := unusedArgs t.type t.value
      if !ks.isEmpty then syn := syn.push (n, ks)
    IO.eprintln s!"theorems with syntactically unused explicit arguments: {syn.size}"
    let mut pa ← propArgs env syn
    let allow : Option (Std.HashSet String) ← match cfg.only? with
      | some f => pure (some ((← IO.FS.lines f).foldl (fun s l => if l.isEmpty then s else s.insert l) {}))
      | none => pure none
    let mut acands : Array ACand := #[]
    let mut argOf : Std.HashMap Name Nat := {}
    for (n, ks) in pa do
      let ks : Array (Nat × Name × String) := match allow with
        | some a => ks.filter fun (x : Nat × Name × String) => a.contains s!"{nm n}\t{x.1}"
        | none => ks
      if ks.isEmpty then continue
      argOf := argOf.insert n acands.size
      acands := acands.push { thm := n, slots := ks.map (·.1), names := ks.map (·.2.1), used := ks.map fun _ => false,
                              pend := ks.map fun _ => #[] }
    let tyOf : Std.HashMap (Name × Nat) String := pa.foldl (fun m (n, ks) => ks.foldl (fun m (k, _, s) => m.insert (n, k) s) m) {}
    pa := #[]
    IO.eprintln s!"candidate arguments (explicit, Prop, unused): {acands.foldl (· + ·.slots.size) 0} in {acands.size} theorems"
    let ((), sa) ← (go.run (mkCtx false true argOf)).run { vis := Std.HashSet.emptyWithCapacity (1 <<< 20), cands, acands }
    let live := sa.live
    IO.eprintln s!"arg-mode live constants: {live.size} (visited {sa.nVis} nodes)"
    writeLive sa
    let dropped ← writeDropped env outdir isProject pool live
    let ua ← IO.FS.Handle.mk (outdir ++ "/unused-args.tsv") .write
    ua.putStrLn "theorem\targ_index\targ_name\ttype\tcall_sites_held\tfreed\tfreed_constants"
    let mut nUnused := 0
    for c in sa.acands do
      if !live.contains c.thm then continue
      for s in [0:c.slots.size] do
        if c.used[s]! then continue
        nUnused := nUnused + 1
        let got := freedFrom env isProject liveBase live (c.pend[s]!.map (·.1))
        ua.putStrLn s!"{nm c.thm}\t{c.slots[s]!}\t{nm c.names[s]!}\t{tyOf.getD (c.thm, c.slots[s]!) ""}\t{c.pend[s]!.size}\t{got.size}\t{";".intercalate (got.toList.map nm)}"
    ua.flush
    IO.eprintln s!"unused arguments: {nUnused}; constants dropped: {dropped}"
    -- before an edit the dropped constants are still mentioned at the call sites; plan after it
    if cfg.before?.isSome then plan live (droppedSet live)
    IO.println s!"unused_args\t{nUnused}\ndropped_constants\t{dropped}"
    return 0
  let t1 ← IO.monoMsNow
  let ((), sf) ← (go.run (mkCtx true)).run { vis := Std.HashSet.emptyWithCapacity (1 <<< 20), cands }
  IO.eprintln s!"field-mode pass: {((← IO.monoMsNow) - t1) / 1000} s"
  let live := sf.live
  IO.eprintln s!"field-mode live constants: {live.size} (visited {sf.nVis} nodes)"
  writeLive sf
  writeInfo live
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
  let dropped ← writeDropped env outdir isProject pool live
  IO.eprintln s!"dead fields: {deadFields} in {deadStructs} live structures; constants dropped: {dropped}"
  -- per dead field: dropped constants reachable from what it holds back
  let fa ← IO.FS.Handle.mk (outdir ++ "/field-reach.tsv") .write
  for c in sf.cands do
    if !live.contains c.ind then continue
    for k in [0:c.nFields] do
      if c.read[k]! then continue
      let gotL := freedFrom env isProject liveBase live (c.pend[k]!.map (·.1))
      fa.putStrLn s!"{nm c.ind}\t{nm c.fieldNames[k]!}\t{gotL.size}\t{";".intercalate (gotL.toList.map nm)}"
  fa.flush
  -- before the structural edits the dead fields' values still mention what they free; plan after
  if cfg.before?.isSome then plan live (droppedSet live)
  IO.println s!"dead_fields\t{deadFields}\ndead_structs\t{deadStructs}\ndropped_constants\t{dropped}"
  return 0

@[implemented_by mainImpl]
opaque mainSafe : List String → IO UInt32

def main (args : List String) : IO UInt32 := mainSafe args
