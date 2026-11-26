import CollatzCycleMinimumRigidity

/-! Exact, order-sensitive affine numerators for supplied accelerated
Collatz step equations. The divisibility test is necessary for closure;
it does not by itself establish admissibility or exclude every cycle. -/
namespace CollatzRunyan.CollatzCycleAffineRigidity
open CollatzRunyan.CollatzAdelicDrift (binaryBudget)

/-- A_0 = 0 and A_(m+1) = 3 A_m + 2^K_m, where K_m is the prefix budget. -/
def affineNumerator (k : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m+1 => 3 * affineNumerator k m + 2^binaryBudget k m

theorem affine_numerator_pos (k : ℕ → ℕ) (m : ℕ) :
    0 < affineNumerator k (m+1) := by
  rw [affineNumerator]
  have hp : 0 < (2 : ℕ)^binaryBudget k m := by positivity
  omega

/-- The affine identity holds for every prefix, even without closure. -/
theorem affine_balance (a k : ℕ → ℕ)
    (hs : ∀ i, 3*a i+1 = 2^(k i)*a (i+1)) (m : ℕ) :
    2^binaryBudget k m * a m = 3^m * a 0 + affineNumerator k m := by
  induction m with
  | zero => simp [binaryBudget, affineNumerator]
  | succ m ih =>
    rw [binaryBudget, pow_add, pow_succ, affineNumerator]
    calc
      2^binaryBudget k m * 2^k m * a (m+1) =
          2^binaryBudget k m * (2^k m * a (m+1)) := by ring
      _ = 2^binaryBudget k m * (3*a m+1) := by rw [← hs m]
      _ = 3*(2^binaryBudget k m*a m) + 2^binaryBudget k m := by ring
      _ = 3^m*3*a 0 + (3*affineNumerator k m + 2^binaryBudget k m) := by
        rw [ih]
        ring

theorem closed_affine (a k : ℕ → ℕ)
    (hs : ∀ i, 3*a i+1 = 2^(k i)*a (i+1)) (m : ℕ)
    (hc : a m = a 0) :
    (2^binaryBudget k m - 3^m)*a 0 = affineNumerator k m := by
  have h := affine_balance a k hs m
  rw [hc] at h
  rw [Nat.sub_mul]
  omega

/-- Nonempty closed segments force a strictly positive discrepancy. -/
theorem closed_affine_discrepancy_pos (a k : ℕ → ℕ)
    (hs : ∀ i, 3*a i+1 = 2^(k i)*a (i+1)) (m : ℕ)
    (hc : a (m+1) = a 0) :
    (3 : ℕ)^(m+1) < 2^binaryBudget k (m+1) := by
  have h := closed_affine a k hs (m+1) hc
  have hp := affine_numerator_pos k m
  by_contra! hle
  rw [Nat.sub_eq_zero_of_le hle, zero_mul] at h
  omega

theorem closed_affine_dvd (a k : ℕ → ℕ)
    (hs : ∀ i, 3*a i+1 = 2^(k i)*a (i+1)) (m : ℕ)
    (hc : a m = a 0) :
    (2^binaryBudget k m - 3^m) ∣ affineNumerator k m := by
  exact ⟨a 0, (closed_affine a k hs m hc).symm⟩

theorem exclude_affine (a k : ℕ → ℕ)
    (hs : ∀ i, 3*a i+1 = 2^(k i)*a (i+1)) (m : ℕ)
    (bad : ¬ (2^binaryBudget k m - 3^m) ∣ affineNumerator k m) :
    a m ≠ a 0 := by
  intro hc
  exact bad (closed_affine_dvd a k hs m hc)

#print axioms affine_numerator_pos
#print axioms affine_balance
#print axioms closed_affine
#print axioms closed_affine_discrepancy_pos
#print axioms closed_affine_dvd
#print axioms exclude_affine
end CollatzRunyan.CollatzCycleAffineRigidity
