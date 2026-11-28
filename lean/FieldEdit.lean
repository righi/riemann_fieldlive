/-
fieldedit: the source edits that remove dead structure fields.

    fieldedit FIELD_SITES OUT

FIELD_SITES is `field-sites.tsv` from `fieldlive` (fields mode): for each dead field, the files that
build or read it. Each file is elaborated again (run with `lake env`, after a build), and its info
trees give the exact syntax of every place the field occurs. OUT gets one row per edit:

  file, start line, start column, end line, end column, kind, projection, detail

with kind
  decl     the field in the `structure` declaration (with its doc comment)
  value    `field := v` in a structure instance (`{ … }` or `where`)
  arg      the field's argument of `⟨…⟩` or `S.mk …`
  reader   a use of the projection: the field is read there, so the code around it has to go first
  unknown  a use of the constructor this tool cannot edit (partial application, `@S.mk`, …)

The ranges of one site never overlap: a removed entry takes the separator up to the next kept
entry, or, if it is the last, the one before it. Columns count code points.
-/
import Lean
open Lean Elab

structure Target where
  proj : Name
  ctor : Name
  index : Nat
  nFields : Nat

/-- the nodes from `stx` down to the innermost one whose range contains `p` -/
partial def pathTo (stx : Syntax) (p : String.Pos.Raw) : Array Syntax := Id.run do
  let mut out := #[stx]
  let mut cur := stx
  repeat
    let inside (c : Syntax) : Bool := match c.getRange? with
      | some r => r.start ≤ p && p < r.stop
      | none => false
    let some c := cur.getArgs.find? inside | break
    out := out.push c
    cur := c
  return out

/-- the index of the last element satisfying `p` -/
def lastIdx? (a : Array Syntax) (p : Syntax → Bool) : Option Nat := Id.run do
  let mut r := none
  for i in [0:a.size] do
    if p a[i]! then r := some i
  return r

def isOrig (stx : Syntax) : Bool := stx.getHeadInfo matches .original ..

/-- a site: a list of entries (fields of a structure instance, arguments of a constructor, fields of
a structure declaration), and which of them go -/
structure Site where
  kind : String
  elems : Array Syntax
  del : Array (Nat × Name) := #[]

def startOf (s : Syntax) : String.Pos.Raw := s.getPos?.getD 0
def stopOf (s : Syntax) : String.Pos.Raw := s.getTailPos?.getD 0

/-- the ranges to delete for a site: entry `i` with everything up to the next entry, or for a
trailing run of deleted entries, from the end of the entry before -/
def siteRanges (s : Site) : Array (String.Pos.Raw × String.Pos.Raw × Name) := Id.run do
  let dels := s.del.map (·.1)
  let mut out := #[]
  for (i, proj) in s.del do
    let keptAfter := (List.range s.elems.size).any fun j => j > i && !dels.contains j
    if keptAfter then
      out := out.push (startOf s.elems[i]!, startOf s.elems[i + 1]!, proj)
    else if i > 0 then
      out := out.push (stopOf s.elems[i - 1]!, stopOf s.elems[i]!, proj)
    else
      out := out.push (startOf s.elems[i]!, stopOf s.elems[i]!, proj)
  return out

def binderKinds : List Name :=
  [``Parser.Command.structSimpleBinder, ``Parser.Command.structExplicitBinder,
   ``Parser.Command.structImplicitBinder, ``Parser.Command.structInstBinder]

unsafe def processFile (path : String) (mod : Name) (targets : Array Target) (out : IO.FS.Handle) :
    IO Unit := do
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx (trustLevel := 1024)
    (leakEnv := true) (mainModule := mod)
  let cmdState := { Command.mkState env messages {} with infoState := { enabled := true } }
  let s ← IO.processCommands inputCtx parserState cmdState
  let fm := inputCtx.fileMap
  let env := s.commandState.env
  let pos (p : String.Pos.Raw) : String := let q := fm.toPosition p; s!"{q.line}\t{q.column}"
  let row (a b : String.Pos.Raw) (kind : String) (proj : Name) (detail : String) : IO Unit :=
    out.putStrLn s!"{path}\t{pos a}\t{pos b}\t{kind}\t{proj.toString (escape := false)}\t{detail}"
  let byProj : Std.HashMap Name Target := targets.foldl (fun m t => m.insert t.proj t) {}
  let mut sites : Std.HashMap (String.Pos.Raw × String.Pos.Raw) Site := {}
  let addDel (sites : Std.HashMap (String.Pos.Raw × String.Pos.Raw) Site) (key : String.Pos.Raw × String.Pos.Raw)
      (kind : String) (elems : Array Syntax) (i : Nat) (proj : Name) :=
    let st := sites.getD key { kind, elems }
    if st.del.any (·.1 == i) then sites else sites.insert key { st with del := st.del.push (i, proj) }
  let mut handledFns : Std.HashSet String.Pos.Raw := {}
  -- the field declarations themselves (their names elaborate to the projection)
  let mut declSpans : Array (String.Pos.Raw × String.Pos.Raw) := #[]
  let mut others : Array (Syntax × Name × String) := #[]
  -- the field declarations, found from the projections' declaration ranges
  for t in targets do
    let some r := declRangeExt.find? (level := .server) env t.proj | continue
    if r.range.pos.line == 0 then continue
    let p := fm.ofPosition r.range.pos
    let mut found := false
    for c in s.commands do
      let path := pathTo c p
      if path.size ≤ 1 then continue
      let some bi := lastIdx? path fun x => binderKinds.contains x.getKind | continue
      let b := path[bi]!
      let parent := path[bi - 1]!
      found := true
      -- `(a b : T)` declares several fields in one binder: cannot delete one of them
      if b.getKind == ``Parser.Command.structExplicitBinder && b[2]!.getArgs.size != 1 then
        others := others.push (b, t.proj, "unknown")
        continue
      declSpans := declSpans.push (startOf b, stopOf b)
      let elems := parent.getArgs.filter fun x => binderKinds.contains x.getKind
      let some i := elems.findIdx? (startOf · == startOf b) | continue
      sites := addDel sites (startOf parent, stopOf parent) "decl" elems i t.proj
    unless found do
      others := others.push (Syntax.missing, t.proj, "unknown: field declaration not found")
  for tree in s.commandState.infoState.trees do
    let acc ← IO.mkRef (#[] : Array (Info × ContextInfo × Syntax))
    tree.visitM' (postNode := fun ci info _ => do
      match info with
      | .ofFieldInfo fi => acc.modify (·.push (info, ci, fi.stx))
      | .ofTermInfo ti => acc.modify (·.push (info, ci, ti.stx))
      | _ => pure ())
    for (info, ci, stx) in ← acc.get do
      if !isOrig stx then continue
      match info with
      | .ofFieldInfo fi =>
        let some t := byProj[fi.projName]? | continue
        let some p := stx.getPos? | continue
        let mut done := false
        for c in s.commands do
          let path := pathTo c p
          let some fi' := lastIdx? path (·.getKind == ``Parser.Term.structInstField) | continue
          if fi' == 0 then continue
          let parent := path[fi' - 1]!
          let elems := parent.getSepArgs
          let some i := elems.findIdx? (startOf · == startOf path[fi']!) | continue
          sites := addDel sites (startOf parent, stopOf parent) "value" elems i t.proj
          done := true
        unless done do others := others.push (stx, t.proj, "unknown: structure instance field")
      | .ofTermInfo ti =>
        let e ← ci.runMetaM ti.lctx (instantiateMVars ti.expr)
        let e := e.consumeMData
        let some h := e.getAppFn.constName? | continue
        if let some t := byProj[h]? then
          others := others.push (stx, t.proj, "reader")
          continue
        let ts := targets.filter (·.ctor == h)
        if ts.isEmpty then continue
        -- structure instances: their fields were handled one by one above
        if stx.getKind == ``Parser.Term.structInst || stx.getKind == ``Parser.Command.whereStructInst then
          continue
        if stx.getKind == ``Parser.Term.anonymousCtor then
          let elems := stx[1]!.getSepArgs
          for t in ts do
            -- `⟨a, b, c⟩` flattens extra arguments into the last field
            if (t.index + 1 < t.nFields && elems.size ≥ t.nFields) || elems.size == t.nFields then
              sites := addDel sites (startOf stx, stopOf stx) "arg" elems t.index t.proj
            else others := others.push (stx, t.proj, s!"unknown: ⟨…⟩ with {elems.size} arguments")
        else if stx.getKind == ``Parser.Term.app && stx[0]!.isIdent then
          let args := stx[1]!.getArgs
          let some (.ctorInfo cv) := env.find? h | continue
          -- explicit binders of the constructor: its explicit parameters, then the fields
          let mut explicit : Array Nat := #[]
          let mut ty := cv.type
          let mut k := 0
          repeat
            match ty with
            | .forallE _ _ b bi => if bi.isExplicit then explicit := explicit.push k
                                   ty := b; k := k + 1
            | _ => break
          handledFns := handledFns.insert (startOf stx[0]!)
          let named := args.any (·.getKind == ``Parser.Term.namedArgument)
          for t in ts do
            let slot := cv.numParams + t.index
            match explicit.idxOf? slot with
            | some j =>
              if !named && args.size == explicit.size then
                sites := addDel sites (startOf stx, stopOf stx) "arg" args j t.proj
              else others := others.push (stx, t.proj, "unknown: constructor application with named or missing arguments")
            | none => others := others.push (stx, t.proj, "unknown: implicit field")
        else
          for t in ts do others := others.push (stx, t.proj, s!"unknown: {stx.getKind}")
      | _ => pure ()
  for (_, st) in sites do
    for (a, b, proj) in siteRanges st do row a b st.kind proj ""
  let mut seen : Std.HashSet (String.Pos.Raw × Name × String) := {}
  for (stx, proj, what) in others do
    if stx.isMissing then
      out.putStrLn s!"{path}\t0\t0\t0\t0\tunknown\t{proj.toString (escape := false)}\t{what}"
      continue
    let a := startOf stx
    -- the constructor's name in an application handled above
    if handledFns.contains a then continue
    if declSpans.any fun (x, y) => x ≤ a && a < y then continue
    if seen.contains (a, proj, what) then continue
    seen := seen.insert (a, proj, what)
    let kind := if what == "reader" then "reader" else "unknown"
    row a (stopOf stx) kind proj (if what == "reader" || what == "unknown" then "" else what.drop 9 |>.toString)
  for m in s.commandState.messages.toList do
    if m.severity == .error then IO.eprintln s!"warning: {path}: {← m.toString}"

/-- the targets of each file, from `field-sites.tsv` -/
def readSites (sitesFile : String) : IO (Array String × Std.HashMap String (Name × Array Target)) := do
  let mut byFile : Std.HashMap String (Name × Array Target) := {}
  let mut order : Array String := #[]
  for l in (← IO.FS.lines sitesFile).toList.drop 1 do
    let c := l.splitOn "\t"
    let [proj, _, _, idx, nf, ctor, mod, file] := c | continue
    if file.isEmpty then continue
    let t : Target := { proj := proj.toName, ctor := ctor.toName, index := idx.toNat!, nFields := nf.toNat! }
    unless byFile.contains file do order := order.push file
    byFile := byFile.alter file fun
      | some (m, ts) => some (m, ts.push t)
      | none => some (mod.toName, #[t])
  return (order, byFile)

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["--file", sitesFile, file, part] =>
    -- one file per process: importing a second time in the same process is not supported
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let (_, byFile) ← readSites sitesFile
    let some (m, ts) := byFile[file]? | return 1
    let out ← IO.FS.Handle.mk part .write
    processFile file m ts out
    out.flush
    return 0
  | [sitesFile, outFile] =>
    let (order, byFile) ← readSites sitesFile
    let self ← IO.appPath
    let mut text := "file\tstart_line\tstart_col\tend_line\tend_col\tkind\tprojection\tdetail\n"
    let mut failed := 0
    for f in order do
      IO.eprintln s!"elaborating {f} ({byFile[f]!.2.size} fields)"
      let part := outFile ++ ".part"
      let r ← IO.Process.output { cmd := self.toString, args := #["--file", sitesFile, f, part] }
      IO.eprint r.stderr
      if r.exitCode != 0 then
        IO.eprintln s!"error: elaborating {f} failed ({r.exitCode})"; failed := failed + 1; continue
      text := text ++ (← IO.FS.readFile part)
      IO.FS.removeFile part
    IO.FS.writeFile outFile text
    return if failed == 0 then 0 else 1
  | _ => IO.eprintln "usage: fieldedit FIELD_SITES OUT"; return 2
