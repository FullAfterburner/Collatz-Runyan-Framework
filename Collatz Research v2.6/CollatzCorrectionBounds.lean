import CollatzAdelicDrift

/-! Conditional correction bounds for positive rational orbit segments. -/
namespace CollatzRunyan.CollatzCorrectionBounds
open CollatzRunyan.CollatzAdelicDrift
open CollatzRunyan.CollatzAdelicCompatibility

theorem correction_lower (n : ℕ → ℚ) (hn : ∀ i, 0 < n i) (m : ℕ) :
    1 ≤ correction n m := by
  induction m with
  | zero => simp [correction]
  | succ m ih =>
    rw [correction]
    have hp : 0 < 1 / (3 * n m) := by
      exact div_pos (by norm_num) (mul_pos (by norm_num) (hn m))
    have hf : 1 ≤ 1 + 1 / (3 * n m) := by linarith
    calc
      1 = 1 * 1 := by ring
      _ ≤ correction n m * (1 + 1 / (3 * n m)) :=
        mul_le_mul ih hf (by norm_num) (by linarith)

theorem correction_strict (n : ℕ → ℚ) (hn : ∀ i, 0 < n i) (m : ℕ) :
    1 < correction n (m+1) := by
  rw [correction]
  have hp : 0 < 1 / (3 * n m) := by
    exact div_pos (by norm_num) (mul_pos (by norm_num) (hn m))
  have hl := correction_lower n hn m
  calc
    1 < 1 + 1 / (3 * n m) := by linarith
    _ = 1 * (1 + 1 / (3 * n m)) := by ring
    _ ≤ correction n m * (1 + 1 / (3 * n m)) :=
      mul_le_mul_of_nonneg_right hl (by linarith)

theorem correction_upper (n : ℕ → ℚ) (N : ℚ) (hN : 0 < N)
    (m : ℕ) (hn : ∀ i < m, N ≤ n i) :
    correction n m ≤ (1 + 1 / (3 * N))^m := by
  induction m with
  | zero => simp [correction]
  | succ m ih =>
    have hm : N ≤ n m := hn m (Nat.lt_succ_self m)
    have hpos : 0 < n m := lt_of_lt_of_le hN hm
    have hrec : 1 / (3 * n m) ≤ 1 / (3 * N) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 3 * n m)
        (by positivity : 0 < 3 * N)).2
      linarith
    have hf : 1 + 1 / (3 * n m) ≤ 1 + 1 / (3 * N) := by linarith
    have hi := ih (fun i hi => hn i (Nat.lt_trans hi (Nat.lt_succ_self m)))
    rw [correction, pow_succ]
    exact mul_le_mul hi hf (by positivity) (by positivity)

theorem corrected_growth_upper (n : ℕ → ℚ) (N : ℚ) (hN : 0 < N)
    (m : ℕ) (hn : ∀ i < m, N ≤ n i) :
    (3 : ℚ)^m * correction n m ≤ (3 + 1 / N)^m := by
  have he : (3 : ℚ) * (1 + 1 / (3 * N)) = 3 + 1 / N := by
    field_simp [ne_of_gt hN]
    ring
  calc
    (3 : ℚ)^m * correction n m ≤ (3 : ℚ)^m * (1 + 1 / (3 * N))^m :=
      mul_le_mul_of_nonneg_left (correction_upper n N hN m hn) (by positivity)
    _ = (3 + 1 / N)^m := by rw [← mul_pow, he]

theorem sufficient_descent (n : ℕ → ℚ) (k : ℕ → ℕ)
    (hn : ∀ i, 0 < n i)
    (hs : ∀ i, n (i+1) = normalized (n i) (k i))
    (N : ℚ) (hN : 0 < N) (m : ℕ) (hb : ∀ i < m, N ≤ n i)
    (hbudget : (3 + 1 / N)^m < (2 : ℚ)^binaryBudget k m) : n m < n 0 := by
  apply (descent_iff n k hn hs m).2
  exact lt_of_le_of_lt (corrected_growth_upper n N hN m hb) hbudget

theorem nondescending_budget (n : ℕ → ℚ) (k : ℕ → ℕ)
    (hn : ∀ i, 0 < n i)
    (hs : ∀ i, n (i+1) = normalized (n i) (k i))
    (N : ℚ) (hN : 0 < N) (m : ℕ) (hb : ∀ i < m, N ≤ n i)
    (hnd : n 0 ≤ n m) : (2 : ℚ)^binaryBudget k m ≤ (3 + 1 / N)^m := by
  apply le_of_not_gt
  intro h
  exact (not_lt_of_ge hnd) (sufficient_descent n k hn hs N hN m hb h)

end CollatzRunyan.CollatzCorrectionBounds
