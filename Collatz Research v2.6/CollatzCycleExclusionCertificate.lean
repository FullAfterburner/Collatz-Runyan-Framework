import CollatzCycleBudget

/-! Exact integer certificates for excluding specified closed segments.
These are necessary conditions, not a universal cycle exclusion. -/
namespace CollatzRunyan.CollatzCycleExclusionCertificate
open CollatzRunyan.CollatzAdelicDrift
open CollatzRunyan.CollatzAdelicCompatibility
open CollatzRunyan.CollatzCycleBudget

theorem integer_budget_window (n : ℕ → ℚ) (k : ℕ → ℕ)
    (hn : ∀ i, 0 < n i)
    (hs : ∀ i, n (i+1) = normalized (n i) (k i))
    (N : ℕ) (hN : 0 < N) (m : ℕ)
    (hb : ∀ i < m+1, (N : ℚ) ≤ n i) (hc : n (m+1) = n 0) :
    (3 : ℕ)^(m+1) < 2^binaryBudget k (m+1) ∧
      N^(m+1) * 2^binaryBudget k (m+1) ≤ (3*N+1)^(m+1) := by
  have hNq : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  obtain ⟨hl, hu⟩ := closed_budget_window n k hn hs (N : ℚ) hNq m hb hc
  constructor
  · exact_mod_cast hl
  · have h := mul_le_mul_of_nonneg_left hu (show (0 : ℚ) ≤ (N : ℚ)^(m+1) by positivity)
    rw [← mul_pow (N : ℚ) (3 + 1 / (N : ℚ))] at h
    have he : (N : ℚ) * (3 + 1 / (N : ℚ)) = 3 * (N : ℚ) + 1 := by
      field_simp [ne_of_gt hNq] <;> ring
    rw [he] at h
    exact_mod_cast h

theorem exclude_budget (n : ℕ → ℚ) (k : ℕ → ℕ)
    (hn : ∀ i, 0 < n i)
    (hs : ∀ i, n (i+1) = normalized (n i) (k i))
    (N : ℕ) (hN : 0 < N) (m K : ℕ)
    (hb : ∀ i < m+1, (N : ℚ) ≤ n i)
    (hk : binaryBudget k (m+1) = K)
    (bad : 2^K ≤ (3 : ℕ)^(m+1) ∨ (3*N+1)^(m+1) < N^(m+1)*2^K) :
    n (m+1) ≠ n 0 := by
  intro hc
  obtain ⟨hl, hu⟩ := integer_budget_window n k hn hs N hN m hb hc
  rw [hk] at hl hu
  rcases bad with h | h
  · exact (not_le_of_gt hl) h
  · exact (not_le_of_gt h) hu

#print axioms integer_budget_window
#print axioms exclude_budget
end CollatzRunyan.CollatzCycleExclusionCertificate
