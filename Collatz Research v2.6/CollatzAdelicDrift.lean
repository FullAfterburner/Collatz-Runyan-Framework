import CollatzAdelicCompatibility

/-! Exact finite-orbit drift, conditional on the supplied step equations. -/
namespace CollatzRunyan.CollatzAdelicDrift
open CollatzRunyan.CollatzAdelicCompatibility

def binaryBudget (k : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m+1 => binaryBudget k m + k m

def correction (n : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | m+1 => correction n m * (1 + 1 / (3 * n m))

theorem step_balance (x y : ℚ) (k : ℕ) (hx : x ≠ 0)
    (h : y = normalized x k) :
    (2 : ℚ)^k * y = 3 * x * (1 + 1 / (3*x)) := by
  rw [h, normalized]
  have hp := CollatzRunyan.BinarySpectralIteration.half_power_reciprocal k
  calc
    (2 : ℚ)^k * ((1/2 : ℚ)^k * (3*x+1)) = 3*x+1 := by
      rw [← mul_assoc, mul_comm ((2 : ℚ)^k) ((1/2 : ℚ)^k), hp, one_mul]
    _ = 3*x*(1+1/(3*x)) := by
      field_simp [hx]

theorem orbit_balance (n : ℕ → ℚ) (k : ℕ → ℕ)
    (hn : ∀ i, 0 < n i)
    (hs : ∀ i, n (i+1) = normalized (n i) (k i)) (m : ℕ) :
    (2 : ℚ)^(binaryBudget k m) * n m =
      (3 : ℚ)^m * n 0 * correction n m := by
  induction m with
  | zero => simp [binaryBudget, correction]
  | succ m ih =>
    rw [binaryBudget, correction, pow_add, pow_succ]
    calc
      (2 : ℚ)^binaryBudget k m * (2 : ℚ)^k m * n (m+1) =
          (2 : ℚ)^binaryBudget k m * ((2 : ℚ)^k m * n (m+1)) := by ring
      _ = (2 : ℚ)^binaryBudget k m * (3*n m*(1+1/(3*n m))) := by
        rw [step_balance (n m) (n (m+1)) (k m) (ne_of_gt (hn m)) (hs m)]
      _ = 3 * ((2 : ℚ)^binaryBudget k m * n m) * (1+1/(3*n m)) := by ring
      _ = (3 : ℚ)^m * 3 * n 0 * (correction n m * (1+1/(3*n m))) := by
        rw [ih]
        ring

theorem descent_iff (n : ℕ → ℚ) (k : ℕ → ℕ)
    (hn : ∀ i, 0 < n i)
    (hs : ∀ i, n (i+1) = normalized (n i) (k i)) (m : ℕ) :
    n m < n 0 ↔ (3 : ℚ)^m * correction n m < (2 : ℚ)^binaryBudget k m := by
  have hb := orbit_balance n k hn hs m
  have hp : 0 < (2 : ℚ)^binaryBudget k m := by positivity
  constructor
  · intro h
    have hh := mul_lt_mul_of_pos_left h hp
    rw [hb] at hh
    apply (mul_lt_mul_right (hn 0)).mp
    calc
      ((3 : ℚ)^m * correction n m) * n 0 = (3 : ℚ)^m * n 0 * correction n m := by ring
      _ < (2 : ℚ)^binaryBudget k m * n 0 := hh
  · intro h
    have hh := mul_lt_mul_of_pos_right h (hn 0)
    have he : (3 : ℚ)^m * correction n m * n 0 = (2 : ℚ)^binaryBudget k m * n m := by
      rw [hb]
      ring
    rw [he] at hh
    exact (mul_lt_mul_left hp).mp hh

end CollatzRunyan.CollatzAdelicDrift
