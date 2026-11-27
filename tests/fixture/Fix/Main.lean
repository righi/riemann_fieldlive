module

public import Fix.Basic
public import Fix.Keep

@[expose] public section

/-- The root theorem. -/
theorem fix_root : 0 < (5 : Nat) ∧ Fix.twice 2 = 4 := ⟨Fix.five_pos, by simp only [Fix.twice_def]⟩
