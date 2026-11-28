module

@[expose] public section

namespace Fix

/-- Three numbers; `junk` is never read. -/
structure Box where
  a : Nat
  junk : Nat
  b : Nat

/-- Only `junk` uses it. -/
def junkValue : Nat := 41

def box1 : Box := ⟨1, junkValue, 2⟩

def box2 : Box := { a := 3, junk := junkValue + 1, b := 4 }

def box3 : Box where
  a := 5
  junk := junkValue
  b := 6

def box4 : Box := Box.mk 7 junkValue 8

def box5 : Box :=
  { a := 9
    junk := 0
    b := 10 }

/-- `extra` is never read, but `@Pair.mk` is a use fieldedit does not edit: the field is blocked. -/
structure Pair where
  fst : Nat
  extra : Nat

def pair1 : Pair := @Pair.mk 1 2

def boxSum : Nat := box1.a + box2.b + box3.a + box4.b + box5.a + pair1.fst

end Fix
