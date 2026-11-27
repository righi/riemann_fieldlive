module

public import Fix.Basic

@[expose] public section

/-- Protected module: everything here stays, so `Fix.mentioned` must stay too. -/
theorem stillCompiles : Fix.mentioned = 3 := rfl

-- `Fix.onlyForSimp_def` is meant for `simp only` calls downstream.
