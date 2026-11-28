module

public import Fix.Basic

@[expose] public section

/-- Protected module: everything here stays, so `Fix.mentioned` must stay too. -/
theorem stillCompiles : Fix.mentioned = 3 := rfl

/-- An `example` is no declaration: only the source text shows it uses `Fix.onlyForSimp_def`. -/
example : Fix.onlyForSimp = 2 := by simp only [Fix.onlyForSimp_def]

