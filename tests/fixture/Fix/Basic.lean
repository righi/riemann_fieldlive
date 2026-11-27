module

@[expose] public section

namespace Fix

/-- Two facts about a number; only `pos` is ever read. -/
structure Facts (n : Nat) : Prop where
  pos : 0 < n
  big : n ≠ 1000

/-- Used only to prove the field nobody reads. -/
theorem helper_for_big : (5 : Nat) ≠ 1000 := by decide

theorem facts_five : Facts 5 := ⟨by decide, helper_for_big⟩

/-- Needed by the root. -/
theorem five_pos : 0 < (5 : Nat) := (facts_five).pos

/-- Not needed by anything. -/
def unusedDef (n : Nat) : Nat := n + 1

theorem unusedDef_spec (n : Nat) : unusedDef n = n + 1 := rfl

open Nat in
/-- An unreachable theorem behind an `open … in` prefix. -/
theorem unused_open (n : Nat) : n ≤ succ n := le_succ n

/-- Unreachable, with a `where` helper and a pattern match. -/
def unusedRec : Nat → Nat
  | 0 => go 0
  | n + 1 => unusedRec n + 1
where
  go (k : Nat) : Nat := k

/-- Unreachable itself, but `stillCompiles` below mentions it, and that one is kept. -/
def mentioned : Nat := 3

/-- Unreachable but protected by `--protect Fix.Keep`? No: lives here, so it goes; it mentions
`mentioned` only through its value. -/
theorem uses_mentioned : mentioned = 3 := rfl

private theorem private_unused : True := trivial

instance instUnused : Inhabited (Fin 3) := ⟨0⟩

/-- An unused local instance of a class written through a definition (`DecidableEq`): kept. -/
local instance instDecEqUnit' : DecidableEq PUnit := fun _ _ => isTrue rfl

/-- A notation is meta code: it is kept even though no proof term mentions it. -/
scoped notation "⟪" n "⟫" => unusedDef n

/-- Unreachable, but an `rfl` simp lemma: `dsimp` uses such lemmas without a trace, so it stays. -/
@[simp] theorem unusedDef_zero : unusedDef 0 = 1 := rfl

/-- Unreachable, but a coercion: coercions are unfolded where they are used, so it stays. -/
instance instCoeBoolNat : Coe Bool Nat := ⟨fun b => if b then 1 else 0⟩

/-- Used only by `Fix.Orphan`, which nothing imports. -/
def orphanNeeds : Nat := 7

/-- Unreachable, but mentioned by `onlyForSimp_def`, which the text check keeps. -/
def onlyForSimp : Nat := 2

/-- Proved by `rfl`; `Fix.Keep` writes its name, so it stays, and with it `onlyForSimp`. -/
theorem onlyForSimp_def : onlyForSimp = 2 := rfl

def twice (n : Nat) : Nat := n + n

/-- Proved by `rfl` and used only through `simp only [twice_def]`, which leaves no trace in the
proof term: the plan marks it for the text check, which finds the use and keeps it. -/
theorem twice_def (n : Nat) : twice n = n + n := rfl

end Fix
