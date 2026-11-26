import CollatzCycleAffineRigidity

/-! Exact binary residue conditions for finite accelerated Collatz prefixes.
The step equations are hypotheses. These results check necessary conditions
and characterize oddness of a supplied endpoint; they do not construct a cycle. -/
namespace CollatzRunyan.CollatzCycleAdmissibility
open CollatzRunyan.CollatzAdelicDrift (binaryBudget)
open CollatzRunyan.CollatzCycleAffineRigidity (affineNumerator affine_balance)

/-- A factorization by 2^K is exact precisely when the quotient is odd. -/
theorem binary_residue_iff (K x : ℕ) :
    (2^K*x) % 2^(K+1) = 2^K ↔ x%2 = 1 := by
  have hp : 0 < (2 : ℕ)^K := by positivity
  have hx : x = 2*(x/2) + x%2 := by omega
  have he : (2 : ℕ)^K*x = (2^K*2)*(x/2) + 2^K*(x%2) := by
    calc
      (2 : ℕ)^K*x = 2^K*(2*(x/2)+x%2) :=
        congrArg (fun v : ℕ => 2^K*v) hx
      _ = (2^K*2)*(x/2) + 2^K*(x%2) := by ring
  have hz : (2^K*2*(x/2) : ℕ) % (2^K*2) = 0 :=
    Nat.mod_eq_zero_of_dvd ⟨x/2, rfl⟩
  have hl : (2 : ℕ)^K*(x%2) < 2^K*2 :=
    mul_lt_mul_of_pos_left (show x%2 < 2 by omega) hp
  have hm : (2^K*x : ℕ) % (2^K*2) = 2^K*(x%2) := by
    rw [he, Nat.add_mod]
    simp only [hz, zero_add, Nat.mod_eq_of_lt hl]
  rw [pow_succ, hm]
  constructor
  · intro h
    by_contra hn
    have h0 : x%2 = 0 := by omega
    rw [h0, mul_zero] at h
    omega
  · intro h
    rw [h, mul_one]

/-- Every supplied prefix has the required power of two as a divisor. -/
theorem prefix_binary_dvd (a k : ℕ → ℕ)
    (hs : ∀ i, 3*a i+1 = 2^(k i)*a (i+1)) (m : ℕ) :
    2^binaryBudget k m ∣ 3^m*a 0 + affineNumerator k m := by
  exact ⟨a m, (affine_balance a k hs m).symm⟩

/-- Exact prefix residue is equivalent to oddness of the endpoint. -/
theorem prefix_exact_residue_iff (a k : ℕ → ℕ)
    (hs : ∀ i, 3*a i+1 = 2^(k i)*a (i+1)) (m : ℕ) :
    (3^m*a 0 + affineNumerator k m) % 2^(binaryBudget k m+1) =
      2^binaryBudget k m ↔ a m%2 = 1 := by
  rw [← affine_balance a k hs m]
  exact binary_residue_iff (binaryBudget k m) (a m)

/-- A supplied step exponent is exact if and only if the next state is odd. -/
theorem step_exact_residue_iff (a k : ℕ → ℕ)
    (hs : ∀ i, 3*a i+1 = 2^(k i)*a (i+1)) (i : ℕ) :
    (3*a i+1) % 2^(k i+1) = 2^k i ↔ a (i+1)%2 = 1 := by
  rw [hs i]
  exact binary_residue_iff (k i) (a (i+1))

/-- An incorrect prefix residue rules out an all-odd supplied orbit. -/
theorem exclude_prefix_residue (a k : ℕ → ℕ)
    (hs : ∀ i, 3*a i+1 = 2^(k i)*a (i+1)) (m : ℕ)
    (bad : (3^m*a 0 + affineNumerator k m) % 2^(binaryBudget k m+1) ≠
      2^binaryBudget k m) :
    ¬ (∀ i, a i%2 = 1) := by
  intro ho
  exact bad ((prefix_exact_residue_iff a k hs m).2 (ho m))

#print axioms binary_residue_iff
#print axioms prefix_binary_dvd
#print axioms prefix_exact_residue_iff
#print axioms step_exact_residue_iff
#print axioms exclude_prefix_residue
end CollatzRunyan.CollatzCycleAdmissibility
