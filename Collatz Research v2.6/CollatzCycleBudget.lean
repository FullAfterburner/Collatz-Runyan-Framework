import IntegratedNonDescentRigidity

/-! Necessary budget restrictions for closed accelerated orbit segments.
These results do not exclude all nontrivial cycles. -/
namespace CollatzRunyan.CollatzCycleBudget
open CollatzRunyan.CollatzAdelicDrift
open CollatzRunyan.CollatzAdelicCompatibility
open CollatzRunyan.CollatzCorrectionBounds

theorem closed_balance (n : ℕ → ℚ) (k : ℕ → ℕ)
    (hn : ∀ i, 0 < n i)
    (hs : ∀ i, n (i+1) = normalized (n i) (k i))
    (m : ℕ) (hc : n m = n 0) :
    (2 : ℚ)^binaryBudget k m = (3 : ℚ)^m * correction n m := by
  have hb := orbit_balance n k hn hs m
  rw [hc] at hb
  apply mul_right_cancel₀ (ne_of_gt (hn 0))
  calc
    (2 : ℚ)^binaryBudget k m * n 0 = (3 : ℚ)^m * n 0 * correction n m := hb
    _ = ((3 : ℚ)^m * correction n m) * n 0 := by ring

theorem closed_budget_strict (n : ℕ → ℚ) (k : ℕ → ℕ)
    (hn : ∀ i, 0 < n i)
    (hs : ∀ i, n (i+1) = normalized (n i) (k i))
    (m : ℕ) (hc : n (m+1) = n 0) :
    (3 : ℚ)^(m+1) < (2 : ℚ)^binaryBudget k (m+1) := by
  rw [closed_balance n k hn hs (m+1) hc]
  calc
    (3 : ℚ)^(m+1) = (3 : ℚ)^(m+1) * 1 := by ring
    _ < (3 : ℚ)^(m+1) * correction n (m+1) :=
      mul_lt_mul_of_pos_left (correction_strict n hn m) (by positivity)

theorem closed_budget_window (n : ℕ → ℚ) (k : ℕ → ℕ)
    (hn : ∀ i, 0 < n i)
    (hs : ∀ i, n (i+1) = normalized (n i) (k i))
    (N : ℚ) (hN : 0 < N) (m : ℕ)
    (hb : ∀ i < m+1, N ≤ n i) (hc : n (m+1) = n 0) :
    (3 : ℚ)^(m+1) < (2 : ℚ)^binaryBudget k (m+1) ∧
      (2 : ℚ)^binaryBudget k (m+1) ≤ (3 + 1/N)^(m+1) := by
  refine ⟨closed_budget_strict n k hn hs m hc, ?_⟩
  rw [closed_balance n k hn hs (m+1) hc]
  exact corrected_growth_upper n N hN (m+1) hb

#print axioms closed_balance
#print axioms closed_budget_strict
#print axioms closed_budget_window
end CollatzRunyan.CollatzCycleBudget
