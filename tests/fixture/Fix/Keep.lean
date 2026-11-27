module

public import Fix.Basic

@[expose] public section

/-- Protected module: everything here stays, so `Fix.mentioned` must stay too. -/
theorem stillCompiles : Fix.mentioned = 3 := rfl
