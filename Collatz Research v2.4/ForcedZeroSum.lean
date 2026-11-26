import Mathlib

/-! A barrier to forcing proper zero-sum blocks.
The arithmetic theorems are conditional on explicit block bounds and
congruences. No external logarithmic estimate is asserted as a Lean axiom.
The example is rational, not a counterexample to the integer Collatz conjecture.
-/
namespace CollatzRunyan.ForcedZeroSum

-- Positive multiples of a positive modulus cannot be smaller than it.
theorem positive_divisor_le (q b : ℤ) (hq : 0 < q) (hb : 0 < b)
    (hd : q ∣ b) : q ≤ b := by
  obtain ⟨t, ht⟩ := hd
  by_cases hp : 0 < t
  · have hm := mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ t-1 by omega)
    nlinarith
  · have hm := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hq)
        (show t ≤ 0 by omega)
    omega

-- A divisor common to two positive block numerators has a square bound.
theorem common_divisor_square (q b1 b2 : ℤ) (hq : 0 < q)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hd1 : q ∣ b1) (hd2 : q ∣ b2) :
    q*q ≤ b1*b2 := by
  exact mul_le_mul (positive_divisor_le q b1 hq hb1 hd1)
    (positive_divisor_le q b2 hq hb2 hd2) (le_of_lt hq) (le_of_lt hb1)

-- This criterion applies to every common divisor, not just the full denominator.
theorem large_modulus_exclusion (q b1 b2 : ℤ) (hq : 0 < q)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hsmall : b1*b2 < q*q) :
    ¬ (q ∣ b1 ∧ q ∣ b2) := by
  rintro ⟨h1, h2⟩
  exact (not_lt_of_ge (common_divisor_square q b1 b2 hq hb1 hb2 h1 h2)) hsmall

-- If every odd cycle value is >= 3, the external product argument gives
-- M*3^a <= 10^a. Under that explicit input the bound improves from 6^a to 5^a.
theorem nontrivial_cycle_divisor_cap (a : ℕ) (q M : ℤ)
    (hbound : (2 : ℤ)^a*(q*q) ≤ M*(3 : ℤ)^a)
    (hM : M*(3 : ℤ)^a ≤ (10 : ℤ)^a) : q*q ≤ (5 : ℤ)^a := by
  have he : (10 : ℤ)^a = (2 : ℤ)^a*(5 : ℤ)^a := by
    rw [← mul_pow] <;> norm_num
  have h := le_trans hbound hM
  rw [he] at h
  by_contra hn
  have hp := mul_pos (show 0 < (2 : ℤ)^a by positivity)
    (show 0 < q*q-(5 : ℤ)^a by omega)
  nlinarith only [h, hp]

-- More prefix residues than residue classes force a collision.
theorem prefix_collision_forced (a q : ℕ) (f : Fin a → Fin q) (h : q < a) :
    ∃ i j : Fin a, i ≠ j ∧ f i = f j := by
  by_contra hn
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact hn ⟨i, j, hne, hij⟩
  have hc : a ≤ q := by
    simpa using Fintype.card_le_of_injective f hf
  omega

-- Distinct proper prefix residues require at least as many residues as prefixes.
theorem no_collision_cardinality (a q : ℕ) (f : Fin a → Fin q)
    (h : ∀ i j : Fin a, i ≠ j → f i ≠ f j) : a ≤ q := by
  by_contra hn
  obtain ⟨i, j, hne, heq⟩ := prefix_collision_forced a q f (by omega)
  exact h i j hne heq

-- For gaps (1,5), D=55, B=5. Closure and balance modulo 5 do not
-- force a proper zero-sum block: neither of the two weights vanishes.
theorem proper_divisor_counterexample :
    (2 : ℤ)^6-3^2 = 55 ∧ (3 : ℤ)+2 = 5 ∧
    (5 : ℤ) ∣ (55 : ℤ) ∧ (5 : ℤ) ∣ (5 : ℤ) ∧
    (5 : ℤ) ∣ (2*1-3*4 : ℤ) ∧ (5 : ℤ) ∣ (32*4-3*1 : ℤ) ∧
    (5 : ℤ) ∣ (1+4 : ℤ) ∧ ¬ (5 : ℤ) ∣ (1 : ℤ) ∧
    ¬ (5 : ℤ) ∣ (4 : ℤ) ∧ ¬ (55 : ℤ) ∣ (5 : ℤ) := by norm_num

-- The positive rational fixed point is not an integer cycle.
theorem rational_two_gap_return :
    (3*(1/11 : ℚ)+1)/2 = 7/11 ∧
    (3*(7/11 : ℚ)+1)/32 = 1/11 := by norm_num

#print axioms positive_divisor_le
#print axioms common_divisor_square
#print axioms large_modulus_exclusion
#print axioms nontrivial_cycle_divisor_cap
#print axioms prefix_collision_forced
#print axioms no_collision_cardinality
#print axioms proper_divisor_counterexample
#print axioms rational_two_gap_return

end CollatzRunyan.ForcedZeroSum
