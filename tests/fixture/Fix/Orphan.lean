module

public import Fix.Basic

@[expose] public section

/-- No root imports this module, but it is protected (and `lake build` still compiles it), so what
it uses stays. Without the import of every built module the analysis would not see this use. -/
theorem orphan_uses : Fix.orphanNeeds = 7 := rfl
