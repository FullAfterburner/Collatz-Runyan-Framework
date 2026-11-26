import CollatzCycleExclusionCertificate

/-! Relative correction bounds and exact minimum-value restrictions.
The restrictions are conditional on closure; they do not prove universal
cycle exclusion. -/
namespace CollatzRunyan.CollatzCycleMinimumRigidity
open CollatzRunyan.CollatzAdelicDrift
open CollatzRunyan.CollatzAdelicCompatibility
open CollatzRunyan.CollatzCorrectionBounds
open CollatzRunyan.CollatzCycleBudget
open CollatzRunyan.CollatzCycleExclusionCertificate

theorem correction_relative_bound (n : ℕ → ℚ) (hn : ∀ i, 0 < n i)
    (N : ℚ) (m : ℕ) (hb : ∀ i < m, N ≤ n i) :
    (3*N+1) * (correction n m - 1) ≤ (m : ℚ) * correction n m := by
  induction m with
  | zero => simp [correction]
  | succ m ih =>
    have hi := ih (fun i h => hb i (Nat.lt_trans h (Nat.lt_succ_self m)))
    have hm := hb m (Nat.lt_succ_self m)
    have hd : 0 < 3 * n m := mul_pos (by norm_num) (hn m)
    have hrec : (3*N) * (1 / (3*n m)) ≤ 1 := by
      calc
        (3*N) * (1 / (3*n m)) = (3*N) / (3*n m) := by ring
        _ ≤ 1 := (div_le_iff₀ hd).2 (by linarith)
    let f : ℚ := 1 + 1 / (3*n m)
    have hf : 1 ≤ f := by
      dsimp [f]
      have hp : 0 < 1 / (3*n m) := div_pos (by norm_num) hd
      linarith
    have hf0 : 0 ≤ f := by linarith
    have hstep : (3*N+1)*(f-1) ≤ f := by
      dsimp [f]
      nlinarith only [hrec]
    have hC := correction_lower n hn m
    have h1 := mul_le_mul_of_nonneg_right hi hf0
    have h2 : f ≤ correction n m * f := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hf0
    rw [correction]
    change (3*N+1)*(correction n m*f-1) ≤
      ((m+1 : ℕ) : ℚ)*(correction n m*f)
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      (3*N+1)*(correction n m*f-1) =
          ((3*N+1)*(correction n m-1))*f + (3*N+1)*(f-1) := by ring
      _ ≤ ((m : ℚ)*correction n m)*f + f := add_le_add h1 hstep
      _ ≤ ((m : ℚ)*correction n m)*f + correction n m*f :=
        add_le_add_left h2 _
      _ = ((m : ℚ)+1)*(correction n m*f) := by ring

theorem closed_minimum_bound (n : ℕ → ℚ) (k : ℕ → ℕ)
    (hn : ∀ i, 0 < n i)
    (hs : ∀ i, n (i+1) = normalized (n i) (k i))
    (N : ℕ) (hN : 0 < N) (m : ℕ)
    (hb : ∀ i < m+1, (N : ℚ) ≤ n i) (hc : n (m+1) = n 0) :
    (3*N+1) * (2^binaryBudget k (m+1) - 3^(m+1)) ≤
      (m+1) * 2^binaryBudget k (m+1) := by
  have h := correction_relative_bound n hn (N : ℚ) (m+1) hb
  have hscl := mul_le_mul_of_nonneg_left h
    (show (0 : ℚ) ≤ (3 : ℚ)^(m+1) by positivity)
  have he := closed_balance n k hn hs (m+1) hc
  have hq : (3*(N : ℚ)+1)*((2 : ℚ)^binaryBudget k (m+1) - (3 : ℚ)^(m+1)) ≤
      ((m+1 : ℕ) : ℚ)*(2 : ℚ)^binaryBudget k (m+1) := by
    calc
      (3*(N : ℚ)+1)*((2 : ℚ)^binaryBudget k (m+1) - (3 : ℚ)^(m+1)) =
          (3 : ℚ)^(m+1)*((3*(N : ℚ)+1)*(correction n (m+1)-1)) := by
        rw [he]
        ring
      _ ≤ (3 : ℚ)^(m+1)*(((m+1 : ℕ) : ℚ)*correction n (m+1)) := hscl
      _ = ((m+1 : ℕ) : ℚ)*(2 : ℚ)^binaryBudget k (m+1) := by
        rw [he]
        ring
  have hl := (integer_budget_window n k hn hs N hN m hb hc).1
  have hq' : (3*(N : ℚ)+1)*((2^binaryBudget k (m+1) - 3^(m+1) : ℕ) : ℚ) ≤
      ((m+1 : ℕ) : ℚ)*(2 : ℚ)^binaryBudget k (m+1) := by
    rw [Nat.cast_sub (le_of_lt hl)]
    exact_mod_cast hq
  exact_mod_cast hq'

theorem exclude_minimum (n : ℕ → ℚ) (k : ℕ → ℕ)
    (hn : ∀ i, 0 < n i)
    (hs : ∀ i, n (i+1) = normalized (n i) (k i))
    (N : ℕ) (hN : 0 < N) (m K : ℕ)
    (hb : ∀ i < m+1, (N : ℚ) ≤ n i)
    (hk : binaryBudget k (m+1) = K)
    (bad : (m+1)*2^K < (3*N+1)*(2^K-3^(m+1))) :
    n (m+1) ≠ n 0 := by
  intro hc
  have h := closed_minimum_bound n k hn hs N hN m hb hc
  rw [hk] at h
  exact (not_le_of_gt bad) h

#print axioms correction_relative_bound
#print axioms closed_minimum_bound
#print axioms exclude_minimum
end CollatzRunyan.CollatzCycleMinimumRigidity
