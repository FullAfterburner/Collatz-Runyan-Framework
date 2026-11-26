import Mathlib

/-! Full-denominator split obstruction: arithmetic core.
A block with a odd transitions and scale M has numerator b satisfying
  2^a * b <= M * (3^a - 2^a).
Two positive block numerators divisible by D force a square bound.
The logarithmic separation theorem of Rhin and the finite exhaustive
check are external to this Lean module. No claim of universal cycle
exclusion is made. -/
namespace CollatzRunyan.CycleBoundConflict

-- Elementary order of the two exponential bases.
theorem two_pow_le_three_pow (n : ℕ) : (2 : ℤ)^n ≤ 3^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ, pow_succ]
      have h1 := mul_le_mul_of_nonneg_right ih (show (0 : ℤ) ≤ 2 by norm_num)
      have h2 := mul_le_mul_of_nonneg_left (show (2 : ℤ) ≤ 3 by norm_num)
        (show 0 ≤ (3 : ℤ)^n by positivity)
      exact le_trans h1 h2

-- Exact numerator envelope under the accelerated affine recurrence.
theorem block_numerator_bound (M B scale : ℕ → ℤ)
    (hM0 : M 0 = 1) (hB0 : B 0 = 0)
    (hMn : ∀ i, 0 ≤ M i) (hs : ∀ i, 2 ≤ scale i)
    (hM : ∀ i, M (i+1) = scale i * M i)
    (hB : ∀ i, B (i+1) = 3*B i + M i) (n : ℕ) :
    (2 : ℤ)^n * B n ≤ M n * ((3 : ℤ)^n - (2 : ℤ)^n) := by
  induction n with
  | zero => simp [hM0, hB0]
  | succ n ih =>
      have hp : 0 ≤ (3 : ℤ)^(n+1) - (2 : ℤ)^(n+1) :=
        sub_nonneg.mpr (two_pow_le_three_pow (n+1))
      have hprod := mul_nonneg (hMn n) hp
      have h6 := mul_le_mul_of_nonneg_left ih (show (0 : ℤ) ≤ 6 by norm_num)
      calc
        (2 : ℤ)^(n+1) * B (n+1) = 6*((2 : ℤ)^n * B n) + 2*((2 : ℤ)^n * M n) := by
          rw [hB n, pow_succ]; ring
        _ ≤ 6*(M n*((3 : ℤ)^n-(2 : ℤ)^n)) + 2*((2 : ℤ)^n * M n) :=
          add_le_add_right h6 _
        _ = 2*(M n*((3 : ℤ)^(n+1)-(2 : ℤ)^(n+1))) := by
          rw [pow_succ, pow_succ]; ring
        _ ≤ scale n*(M n*((3 : ℤ)^(n+1)-(2 : ℤ)^(n+1))) :=
          mul_le_mul_of_nonneg_right (hs n) hprod
        _ = M (n+1)*((3 : ℤ)^(n+1)-(2 : ℤ)^(n+1)) := by
          rw [hM n]; ring

-- Weaken the envelope to an expression convenient for multiplication.
theorem block_numerator_relaxed (a : ℕ) (M b : ℤ) (hM : 0 ≤ M)
    (h : (2 : ℤ)^a*b ≤ M*((3 : ℤ)^a-(2 : ℤ)^a)) :
    (2 : ℤ)^a*b ≤ M*(3 : ℤ)^a := by
  have hp : 0 ≤ (2 : ℤ)^a := by positivity
  have hh := mul_le_mul_of_nonneg_left (show (3 : ℤ)^a-(2 : ℤ)^a ≤ 3^a by omega) hM
  exact le_trans h hh

-- Multiply the two block envelopes; no minimum assumption is used.
theorem split_product_bound (l r : ℕ) (M1 M2 b1 b2 : ℤ)
    (hM1 : 0 ≤ M1) (hb2 : 0 ≤ b2)
    (h1 : (2 : ℤ)^l*b1 ≤ M1*(3 : ℤ)^l)
    (h2 : (2 : ℤ)^r*b2 ≤ M2*(3 : ℤ)^r) :
    (2 : ℤ)^(l+r)*(b1*b2) ≤ (M1*M2)*(3 : ℤ)^(l+r) := by
  have hp : 0 ≤ (2 : ℤ)^r*b2 := mul_nonneg (by positivity) hb2
  have hq : 0 ≤ M1*(3 : ℤ)^l := mul_nonneg hM1 (by positivity)
  have h := mul_le_mul h1 h2 hp hq
  calc
    (2 : ℤ)^(l+r)*(b1*b2) = ((2 : ℤ)^l*b1)*((2 : ℤ)^r*b2) := by rw [pow_add]; ring
    _ ≤ (M1*(3 : ℤ)^l)*(M2*(3 : ℤ)^r) := h
    _ = (M1*M2)*(3 : ℤ)^(l+r) := by rw [pow_add]; ring

-- Two positive multiples of D have product at least D^2.
theorem divisor_product_lower (D b1 b2 : ℤ)
    (hD : 0 < D) (hb1 : 0 < b1) (hb2 : 0 < b2)
    (hd1 : D ∣ b1) (hd2 : D ∣ b2) : D*D ≤ b1*b2 := by
  obtain ⟨u, hu⟩ := hd1
  obtain ⟨v, hv⟩ := hd2
  have hpos (t b : ℤ) (hb : 0 < b) (ht : b = D*t) : 1 ≤ t := by
    by_contra hn
    have hz : t ≤ 0 := by omega
    have hm := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hD) hz
    omega
  have hu1 := hpos u b1 hb1 hu
  have hv1 := hpos v b2 hb2 hv
  have h1 := mul_le_mul_of_nonneg_left hu1 (le_of_lt hD)
  have h2 := mul_le_mul_of_nonneg_left hv1 (le_of_lt hD)
  rw [mul_one, ← hu] at h1
  rw [mul_one, ← hv] at h2
  exact mul_le_mul h1 h2 (le_of_lt hD) (le_of_lt hb1)

-- Necessary square inequality for a full-denominator split.
theorem full_split_square (a : ℕ) (D M b1 b2 : ℤ)
    (hD : 0 < D) (hb1 : 0 < b1) (hb2 : 0 < b2)
    (hd1 : D ∣ b1) (hd2 : D ∣ b2)
    (hbound : (2 : ℤ)^a*(b1*b2) ≤ M*(3 : ℤ)^a) :
    (2 : ℤ)^a*(D*D) ≤ M*(3 : ℤ)^a := by
  have hp := divisor_product_lower D b1 b2 hD hb1 hb2 hd1 hd2
  exact le_trans (mul_le_mul_of_nonneg_left hp (by positivity)) hbound

-- For positive integer cycles the separate product argument gives M <= 4^a.
-- Under that explicit hypothesis the previous square bound gives D^2 <= 6^a.
theorem cycle_square_cap (a : ℕ) (D M : ℤ)
    (hM : M ≤ (4 : ℤ)^a)
    (hbound : (2 : ℤ)^a*(D*D) ≤ M*(3 : ℤ)^a) :
    D*D ≤ (6 : ℤ)^a := by
  have hh := mul_le_mul_of_nonneg_right hM (show 0 ≤ (3 : ℤ)^a by positivity)
  have he : (4 : ℤ)^a*(3 : ℤ)^a = (2 : ℤ)^a*(6 : ℤ)^a := by
    rw [← mul_pow, ← mul_pow]; norm_num
  have h := le_trans hbound hh
  rw [he] at h
  by_contra hn
  have hp := mul_pos (show 0 < (2 : ℤ)^a by positivity)
    (show 0 < D*D-(6 : ℤ)^a by omega)
  nlinarith only [h, hp]

-- Arithmetic interface for external logarithmic separation.
-- A < C*D is the externally derived separation, not a Lean axiom.
theorem separation_conflict (A C D U : ℤ)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hsep : A < C*D) (hcap : D*D ≤ U)
    (htail : C*C*U < A*A) : False := by
  have hp := mul_pos (show 0 < C*D-A by omega) (show 0 < C*D+A by omega)
  have hh := mul_le_mul_of_nonneg_left hcap (mul_nonneg hC hC)
  nlinarith only [hp, hh, htail]

#print axioms two_pow_le_three_pow
#print axioms block_numerator_bound
#print axioms block_numerator_relaxed
#print axioms split_product_bound
#print axioms divisor_product_lower
#print axioms full_split_square
#print axioms cycle_square_cap
#print axioms separation_conflict

end CollatzRunyan.CycleBoundConflict
