import BinaryConjugation

/-!
# Collatz–Runyan: Conjugate Coefficient Rigidity

Depends on BinaryConjugation, revision 2. This module proves transport
and uniqueness of affine corrections for fixed multiplicative coefficients.
It does not assert uniqueness of the exponent from a single orbit equation,
import external v25 rigidity theorems, or assume physical correspondence.
-/

namespace CollatzRunyan.BinaryConjugation

 def sectorSign (s : State) : ℤ := if s.sector then -1 else 1

 theorem sectorSign_conjugate (s : State) :
    sectorSign (conjugate s) = -sectorSign s := by
  cases s with
  | mk n b => cases b <;> simp [sectorSign, conjugate]

 theorem sectorSign_sq (s : State) : sectorSign s * sectorSign s = 1 := by
  cases s with
  | mk n b => cases b <;> norm_num [sectorSign]

 theorem signed_eq_sectorSign (s : State) :
    signed s = sectorSign s * (s.magnitude : ℤ) := by
  cases s with
  | mk n b => cases b <;> simp [signed, sectorSign]

 def Affine (k a : ℕ) (s : State) (c : ℤ) : Prop :=
  (2 : ℤ)^k * signed (evolve k s) = (3 : ℤ)^a * signed s + c

 theorem affine_conjugate_iff (k a : ℕ) (s : State) (c : ℤ) :
    Affine k a (conjugate s) (-c) ↔ Affine k a s c := by
  unfold Affine
  rw [signed_orbit_reflection, signed_conjugate]
  constructor <;> intro h <;> linarith

 theorem affine_correction_unique (k a : ℕ) (s : State) (c d : ℤ)
    (hc : Affine k a s c) (hd : Affine k a s d) : c = d := by
  unfold Affine at hc hd
  linarith

 def correction (k a : ℕ) (s : State) : ℤ :=
  (2 : ℤ)^k * signed (evolve k s) - (3 : ℤ)^a * signed s

 theorem affine_correction (k a : ℕ) (s : State) :
    Affine k a s (correction k a s) := by
  unfold Affine correction
  ring

 theorem affine_iff_correction (k a : ℕ) (s : State) (c : ℤ) :
    Affine k a s c ↔ c = correction k a s := by
  constructor
  · intro h
    exact affine_correction_unique k a s c _ h (affine_correction k a s)
  · intro h
    rw [h]
    exact affine_correction k a s

 theorem correction_conjugate (k a : ℕ) (s : State) :
    correction k a (conjugate s) = -correction k a s := by
  unfold correction
  rw [signed_orbit_reflection, signed_conjugate]
  ring

 theorem correction_valuation_invariant (j k a : ℕ) (s : State) :
    ExactValuation j (correction k a (conjugate s)) ↔
      ExactValuation j (correction k a s) := by
  rw [correction_conjugate, exactValuation_neg]

 theorem correction_eq_iff_conjugate (k a l b : ℕ) (s t : State) :
    correction k a (conjugate s) = correction l b (conjugate t) ↔
      correction k a s = correction l b t := by
  rw [correction_conjugate, correction_conjugate]
  constructor <;> intro h <;> linarith

 theorem affine_cycle_iff (k a : ℕ) (s : State) (c : ℤ)
    (h : evolve k s = s) :
    Affine k a s c ↔ ((2 : ℤ)^k - (3 : ℤ)^a) * signed s = c := by
  unfold Affine
  rw [h, sub_mul]
  constructor <;> intro h' <;> linarith

 theorem affine_cycle_transport (k a : ℕ) (s : State) (c : ℤ)
    (h : evolve k s = s) (hc : Affine k a s c) :
    ((2 : ℤ)^k - (3 : ℤ)^a) * signed (conjugate s) = -c := by
  have h' := (affine_cycle_iff k a s c h).mp hc
  rw [signed_conjugate, mul_neg, h']

-- The shortcut orbit 1 -> 2 -> 1 has k = 2 and a = 1.
example : Affine 2 1 ⟨1, false⟩ 1 := by
  norm_num [Affine, signed, evolve, orbit, shortcut]

example : Affine 2 1 ⟨1, true⟩ (-1) := by
  norm_num [Affine, signed, evolve, orbit, shortcut]

end CollatzRunyan.BinaryConjugation
