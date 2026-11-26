import CollatzCycleAdmissibility

/-! Rotation of finite valuation words. An integer affine candidate propagates
through one cyclic rotation when the first exponent is positive and the
cycle discrepancy is positive. This is a local constructive result, not
an exclusion of all nontrivial cycles. -/
namespace CollatzRunyan.CollatzCyclicRotationRigidity
open CollatzRunyan.CollatzAdelicDrift (binaryBudget)
open CollatzRunyan.CollatzCycleAffineRigidity (affineNumerator)

def shift (k : ℕ → ℕ) : ℕ → ℕ := fun i => k (i+1)

def discrepancy (k : ℕ → ℕ) (m : ℕ) : ℕ :=
  2^binaryBudget k m - 3^m

theorem budget_head (k : ℕ → ℕ) (m : ℕ) :
    binaryBudget k (m+1) = k 0 + binaryBudget (shift k) m := by
  induction m with
  | zero => simp [binaryBudget]
  | succ m ih =>
    change binaryBudget k (m+1) + k (m+1) =
      k 0 + (binaryBudget (shift k) m + k (m+1))
    rw [ih]
    omega

theorem affine_head (k : ℕ → ℕ) (m : ℕ) :
    affineNumerator k (m+1) = 3^m + 2^k 0 * affineNumerator (shift k) m := by
  induction m with
  | zero => simp [affineNumerator, binaryBudget]
  | succ m ih =>
    change 3 * affineNumerator k (m+1) + 2^binaryBudget k (m+1) =
      3^(m+1) + 2^k 0 * (3*affineNumerator (shift k) m +
        2^binaryBudget (shift k) m)
    rw [ih, budget_head k m, pow_add, pow_succ (3 : ℕ) m]
    ring

theorem rotation_budget (k : ℕ → ℕ) (m : ℕ)
    (hw : k (m+1) = k 0) :
    binaryBudget (shift k) (m+1) = binaryBudget k (m+1) := by
  change binaryBudget (shift k) m + k (m+1) = binaryBudget k (m+1)
  rw [budget_head k m, hw]
  omega

theorem rotation_discrepancy (k : ℕ → ℕ) (m : ℕ)
    (hw : k (m+1) = k 0) :
    discrepancy (shift k) (m+1) = discrepancy k (m+1) := by
  unfold discrepancy
  rw [rotation_budget k m hw]

/-- Rotate the first valuation to the end. The affine numerator transforms
by 2^e A' = 3 A + D. The wrap condition supplies the final exponent. -/
theorem rotation_identity (k : ℕ → ℕ) (m : ℕ)
    (hp : (3 : ℕ)^(m+1) ≤ 2^binaryBudget k (m+1)) :
    2^k 0 * affineNumerator (shift k) (m+1) =
      3 * affineNumerator k (m+1) + discrepancy k (m+1) := by
  have hpow : (2 : ℕ)^binaryBudget k (m+1) =
      2^k 0 * 2^binaryBudget (shift k) m := by
    rw [budget_head, pow_add]
  have hd : (2 : ℕ)^binaryBudget k (m+1) =
      3^(m+1) + discrepancy k (m+1) := by
    unfold discrepancy
    omega
  calc
    2^k 0 * affineNumerator (shift k) (m+1) =
        3 * (2^k 0 * affineNumerator (shift k) m) +
          2^binaryBudget k (m+1) := by
      rw [affineNumerator, hpow]
      ring
    _ = 3 * affineNumerator k (m+1) + discrepancy k (m+1) := by
      rw [affine_head k m, hd, pow_succ (3 : ℕ) m]
      ring

theorem three_power_odd (m : ℕ) : (3 : ℕ)^m % 2 = 1 := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [pow_succ, Nat.mul_mod, ih] <;> decide

theorem two_power_even (e : ℕ) (he : 0 < e) : (2 : ℕ)^e % 2 = 0 := by
  cases e with
  | zero => omega
  | succ e =>
    rw [pow_succ, Nat.mul_mod]
    simp

theorem discrepancy_odd (k : ℕ → ℕ) (m : ℕ)
    (hk : 0 < k 0)
    (hp : (3 : ℕ)^(m+1) < 2^binaryBudget k (m+1)) :
    discrepancy k (m+1) % 2 = 1 := by
  have hb : 0 < binaryBudget k (m+1) := by
    rw [budget_head]
    omega
  have h2 := two_power_even (binaryBudget k (m+1)) hb
  have h3 := three_power_odd (m+1)
  unfold discrepancy
  omega

/-- Cancel an arbitrary power of two in a divisibility statement with odd divisor. -/
theorem odd_dvd_two_power_mul (d e b : ℕ) (hd : d%2 = 1)
    (h : d ∣ 2^e*b) : d ∣ b := by
  induction e with
  | zero => simpa using h
  | succ e ih =>
    obtain ⟨q, hq⟩ := h
    have he : 2*(2^e*b) = d*q := by
      calc
        2*(2^e*b) = 2^(e+1)*b := by rw [pow_succ]; ring
        _ = d*q := hq
    have hm : (d*q)%2 = 0 := by
      rw [← he]
      omega
    rw [Nat.mul_mod, hd, one_mul] at hm
    have hq2 : q = 2*(q/2) := by omega
    have hh : 2*(2^e*b) = 2*(d*(q/2)) := by
      calc
        2*(2^e*b) = d*q := he
        _ = d*(2*(q/2)) := congrArg (fun t : ℕ => d*t) hq2
        _ = 2*(d*(q/2)) := by ring
    exact ih ⟨q/2, by omega⟩

/-- A positive integer candidate for the original word yields a positive
integer candidate for the rotated word and the exact accelerated step.
The source endpoint is odd; oddness of the next endpoint follows when
its own outgoing exponent is positive and the argument is repeated. -/
theorem rotation_step (k : ℕ → ℕ) (m x : ℕ)
    (hw : k (m+1) = k 0) (hk : 0 < k 0)
    (hp : (3 : ℕ)^(m+1) < 2^binaryBudget k (m+1))
    (hx : affineNumerator k (m+1) = discrepancy k (m+1)*x) :
    ∃ y : ℕ, 0 < y ∧ x%2 = 1 ∧
      affineNumerator (shift k) (m+1) = discrepancy (shift k) (m+1)*y ∧
      3*x+1 = 2^k 0*y := by
  have hd : 0 < discrepancy k (m+1) := by
    unfold discrepancy
    omega
  have hodd := discrepancy_odd k m hk hp
  have hi := rotation_identity k m (Nat.le_of_lt hp)
  rw [hx] at hi
  have he : 2^k 0*affineNumerator (shift k) (m+1) =
      discrepancy k (m+1)*(3*x+1) := by
    rw [hi]
    ring
  obtain ⟨y, hy⟩ := odd_dvd_two_power_mul (discrepancy k (m+1))
    (k 0) (affineNumerator (shift k) (m+1)) hodd ⟨3*x+1, he⟩
  have hcancel : discrepancy k (m+1)*(2^k 0*y) =
      discrepancy k (m+1)*(3*x+1) := by
    calc
      discrepancy k (m+1)*(2^k 0*y) =
          2^k 0*(discrepancy k (m+1)*y) := by ring
      _ = 2^k 0*affineNumerator (shift k) (m+1) := by rw [← hy]
      _ = discrepancy k (m+1)*(3*x+1) := he
  have hs : 3*x+1 = 2^k 0*y := by
    symm
    exact mul_left_cancel₀ (ne_of_gt hd) hcancel
  have hypos : 0 < y := by
    by_contra! hn
    have hz : y = 0 := by omega
    rw [hz, mul_zero] at hs
    omega
  have hmod : (3*x+1)%2 = 0 := by
    rw [hs, Nat.mul_mod, two_power_even (k 0) hk, zero_mul] <;> decide
  have hxodd : x%2 = 1 := by omega
  refine ⟨y, hypos, hxodd, ?_, hs⟩
  rw [rotation_discrepancy k m hw]
  exact hy

#print axioms budget_head
#print axioms affine_head
#print axioms rotation_budget
#print axioms rotation_discrepancy
#print axioms rotation_identity
#print axioms three_power_odd
#print axioms two_power_even
#print axioms discrepancy_odd
#print axioms odd_dvd_two_power_mul
#print axioms rotation_step
end CollatzRunyan.CollatzCyclicRotationRigidity
