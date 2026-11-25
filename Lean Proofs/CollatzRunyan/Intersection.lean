import Mathlib

open scoped BigOperators

namespace CollatzRunyan

/-! Finite exterior-coordinate portion of v2.1L Theorem 5.
Order the 20 triples of coordinates x1,y1,x2,y2,x3,y3
lexicographically, using indices 0,...,19:
012 013 014 015 023 024 025 034 035 045
123 124 125 134 135 145 234 235 245 345.
Complementary triples have indices summing to 19.
Admissible triples: xxx=024, xyy=035, yxy=125, yyx=134.
These finite statements do not establish that geometric cycles
satisfy the Lagrangian or calibration constraints. -/

def admissible (i : Fin 20) : Prop :=
  i.val = 5 ∨ i.val = 8 ∨ i.val = 12 ∨ i.val = 13

theorem no_complement (i j : Fin 20)
    (hi : admissible i) (hj : admissible j) :
    i.val + j.val ≠ 19 := by
  unfold admissible at hi hj
  omega

/-! The intersection entry is zero except on complementary triples;
its orientation sign may be any integer. Thus the conclusion is
independent of orientation conventions. -/

def intersectionEntry (s : Fin 20 → ℤ) (i j : Fin 20) : ℤ :=
  if i.val + j.val = 19 then s i else 0

theorem admissible_entry_zero (s : Fin 20 → ℤ)
    (i j : Fin 20) (hi : admissible i) (hj : admissible j) :
    intersectionEntry s i j = 0 := by
  simp [intersectionEntry, no_complement i j hi hj]

/-! Arbitrary integral coefficient vectors supported on the four
admissible basis elements have zero bilinear pairing. -/

theorem supported_pairing_zero (a b s : Fin 20 → ℤ)
    (ha : ∀ i, ¬ admissible i → a i = 0)
    (hb : ∀ j, ¬ admissible j → b j = 0) :
    (∑ i : Fin 20, ∑ j : Fin 20,
      a i * intersectionEntry s i j * b j) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hi : admissible i
  · by_cases hj : admissible j
    · simp [admissible_entry_zero s i j hi hj]
    · simp [hb j hj]
  · simp [ha i hi]

end CollatzRunyan
