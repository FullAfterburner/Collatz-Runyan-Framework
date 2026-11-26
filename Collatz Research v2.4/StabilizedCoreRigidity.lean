import Mathlib

/-!
# Common-offset rigidity for cyclic affine integer chains
Theorems are conditional on exact chain equations. No claim of universal
cycle exclusion is made. The gcd formulation and parity-word interpretation
are mathematical deductions outside this standalone arithmetic module.
-/
namespace CollatzRunyan.StabilizedCoreRigidity

/-- A common core divisor must divide the edge offset. -/
theorem offset_from_cores (q A P C u v : ℤ)
    (he : P*v = A*u+C) (hu : q ∣ u) (hv : q ∣ v) : q ∣ C := by
  obtain ⟨s, hs⟩ := hu
  obtain ⟨t, ht⟩ := hv
  refine ⟨P*t-A*s, ?_⟩
  calc
    C = P*v-A*u := by linear_combination -he
    _ = q*(P*t-A*s) := by rw [hs, ht]; ring

def coeffProduct (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | n+1 => coeffProduct f n * f n

/-- If all offsets are divisible by q, the composed affine defect is too. -/
theorem chain_defect_dvd (q : ℤ) (A P C u : ℕ → ℤ)
    (he : ∀ i, P i*u (i+1) = A i*u i+C i)
    (hC : ∀ i, q ∣ C i) (n : ℕ) :
    q ∣ coeffProduct P n*u n-coeffProduct A n*u 0 := by
  induction n with
  | zero => simp [coeffProduct]
  | succ n ih =>
    obtain ⟨v, hv⟩ := ih
    obtain ⟨z, hz⟩ := hC n
    refine ⟨A n*v+coeffProduct P n*z, ?_⟩
    simp only [coeffProduct]
    calc
      coeffProduct P n*P n*u (n+1)-coeffProduct A n*A n*u 0 =
          A n*(coeffProduct P n*u n-coeffProduct A n*u 0)+coeffProduct P n*C n := by
            linear_combination coeffProduct P n * he n
      _ = q*(A n*v+coeffProduct P n*z) := by rw [hv, hz]; ring

/-- Closure implies q divides the denominator times the initial core. -/
theorem closed_seed_dvd (q : ℤ) (A P C u : ℕ → ℤ)
    (he : ∀ i, P i*u (i+1) = A i*u i+C i)
    (hC : ∀ i, q ∣ C i) (n : ℕ) (hc : u n = u 0) :
    q ∣ (coeffProduct P n-coeffProduct A n)*u 0 := by
  have h := chain_defect_dvd q A P C u he hC n
  rw [hc] at h
  rw [sub_mul]
  exact h

/-- After removing a common factor of the modulus and denominator, cancel
    the remaining coprime denominator factor. -/
theorem reduced_divisor (Q D d q e u : ℤ)
    (hd : d ≠ 0) (hQ : Q = d*q) (hD : D = d*e)
    (hc : IsCoprime q e) (h : Q ∣ D*u) : q ∣ u := by
  obtain ⟨z, hz⟩ := h
  rw [hQ, hD] at hz
  have hzero : d*(e*u-q*z) = 0 := by linear_combination hz
  have hz' : e*u-q*z = 0 := (mul_eq_zero.mp hzero).resolve_left hd
  apply hc.dvd_of_dvd_mul_left
  exact ⟨z, sub_eq_zero.mp hz'⟩

/-- A divisor of the initial core propagates through any edge whose offset
    is divisible by it and whose denominator is coprime to it. -/
theorem transfer_divisor (q A P C u v : ℤ)
    (hc : IsCoprime q P) (he : P*v = A*u+C)
    (hu : q ∣ u) (hC : q ∣ C) : q ∣ v := by
  obtain ⟨s, hs⟩ := hu
  obtain ⟨t, ht⟩ := hC
  apply hc.dvd_of_dvd_mul_left
  refine ⟨A*s+t, ?_⟩
  rw [he, hs, ht]
  ring

/-- Repeated transfer applies the common divisor to every core. -/
theorem all_cores_dvd (q : ℤ) (A P C u : ℕ → ℤ)
    (he : ∀ i, P i*u (i+1) = A i*u i+C i)
    (hC : ∀ i, q ∣ C i) (hP : ∀ i, IsCoprime q (P i))
    (h0 : q ∣ u 0) (n : ℕ) : q ∣ u n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    exact transfer_divisor q (A n) (P n) (C n) (u n) (u (n+1)) (hP n) (he n) ih (hC n)

/-- Positive multiples of the common divisor give a minimum lower bound. -/
theorem core_lower (q P u : ℤ) (hq : 0 < q) (hP : 0 ≤ P)
    (hu : 0 < u) (hd : q ∣ u) : P*q-1 ≤ P*u-1 := by
  obtain ⟨z, hz⟩ := hd
  have hp : 0 < z := by
    by_contra! hn
    have h := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hq) hn
    linarith
  have h1 : 1 ≤ z := by omega
  have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hq)
  rw [mul_one] at h2
  have h3 : q ≤ u := by linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hP
  linarith

/-- Three odd runs of lengths 3,3,9 and three even runs of length 3:
    the ordinary core envelope survives, while the common divisor 7
    makes the refined envelope impossible. -/
theorem common_divisor_example :
    IsCoprime (7 : ℤ) (2^24-3^15) ∧
    (2 : ℤ)^9*(2^3-1)^2*(2^9-1) ≤ (3^3-1)^2*(3^9-1) ∧
    (2 : ℤ)^9*(2^3*7-1)^2*(2^9*7-1) > (3^3*7-1)^2*(3^9*7-1) := by
  refine ⟨?_, by norm_num, by norm_num⟩
  exact ⟨-1387605, 4, by norm_num⟩

end CollatzRunyan.StabilizedCoreRigidity

#print axioms CollatzRunyan.StabilizedCoreRigidity.offset_from_cores
#print axioms CollatzRunyan.StabilizedCoreRigidity.chain_defect_dvd
#print axioms CollatzRunyan.StabilizedCoreRigidity.closed_seed_dvd
#print axioms CollatzRunyan.StabilizedCoreRigidity.reduced_divisor
#print axioms CollatzRunyan.StabilizedCoreRigidity.transfer_divisor
#print axioms CollatzRunyan.StabilizedCoreRigidity.all_cores_dvd
#print axioms CollatzRunyan.StabilizedCoreRigidity.core_lower
#print axioms CollatzRunyan.StabilizedCoreRigidity.common_divisor_example
