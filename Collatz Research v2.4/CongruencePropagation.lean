import Mathlib

/-! Congruence propagation for affine run equations. The shadow lemmas
show why coprime modular tests cannot alone certify integrality. The
size bound separates a nonintegral rational from bounded integers.
No universal Collatz claim is made. -/
namespace CollatzRunyan.CongruencePropagation

/-- Propagate a known residue through an exact edge. -/
theorem forward_defect (A P C u v R Q : ℤ)
    (he : P*v = A*u+C) (hr : Q ∣ u-R) :
    A*Q ∣ P*v-A*R-C := by
  obtain ⟨z, hz⟩ := hr
  refine ⟨z, ?_⟩
  calc
    P*v-A*R-C = A*(u-R) := by rw [he]; ring
    _ = A*Q*z := by rw [hz]; ring

/-- The corresponding backward propagation. -/
theorem backward_defect (A P C u v R Q : ℤ)
    (he : P*v = A*u+C) (hr : Q ∣ v-R) :
    P*Q ∣ A*u+C-P*R := by
  obtain ⟨z, hz⟩ := hr
  refine ⟨z, ?_⟩
  calc
    A*u+C-P*R = P*(v-R) := by rw [← he]; ring
    _ = P*Q*z := by rw [hz]; ring

/-- A rational solution with denominator D has an integer shadow
at every modulus coprime to D. -/
theorem rational_shadow (D N Q : ℤ) (hc : IsCoprime D Q) :
    ∃ x : ℤ, Q ∣ D*x-N := by
  obtain ⟨b,c,h⟩ := hc
  refine ⟨b*N, -c*N, ?_⟩
  linear_combination N*h

/-- One choice of inverse works simultaneously for every scaled edge. -/
theorem simultaneous_shadow (D Q b c : ℤ) (A P C N : ℕ → ℤ)
    (hinv : b*D+c*Q=1)
    (he : ∀ i, P i*N (i+1)=A i*N i+D*C i) :
    ∀ i, Q ∣ P i*(b*N (i+1))-A i*(b*N i)-C i := by
  intro i
  refine ⟨-c*C i, ?_⟩
  linear_combination b*(he i) + C i*hinv

/-- Distinct integer representatives of the same rational residue
must differ by a multiple of the modulus. -/
theorem shadow_uniqueness (D N Q x y : ℤ) (hc : IsCoprime Q D)
    (hx : Q ∣ D*x-N) (hy : Q ∣ D*y-N) : Q ∣ x-y := by
  have h := dvd_sub hx hy
  rw [show D*x-N-(D*y-N)=D*(x-y) by ring] at h
  exact hc.dvd_of_dvd_mul_left h

/-- A nonintegral fraction cannot have a small nonnegative integer
shadow when the modulus exceeds the numerator. -/
theorem nonintegral_shadow_lower (D N Q x : ℤ)
    (hN : 0 ≤ N) (hQ : N < Q) (hD : 0 < D) (hx : 0 ≤ x)
    (hni : ¬ D ∣ N) (hr : Q ∣ D*x-N) : Q+N ≤ D*x := by
  obtain ⟨t, ht⟩ := hr
  have hqp : 0 < Q := by omega
  have hdx := mul_nonneg (le_of_lt hD) hx
  have ht0 : t ≠ 0 := by
    intro hz
    have he : D*x=N := by rw [hz, mul_zero] at ht; omega
    exact hni ⟨x, he.symm⟩
  have ht1 : 1 ≤ t := by
    by_contra! hn
    have hneg : 0 ≤ -t-1 := by omega
    have hm := mul_nonneg (le_of_lt hqp) hneg
    nlinarith only [ht, hdx, hQ, hm]
  have hm := mul_nonneg (le_of_lt hqp) (show 0 ≤ t-1 by omega)
  nlinarith only [ht, hm]

/-- Explicit finite-precision exclusion using an independent size cap. -/
theorem bounded_shadow_exclusion (D N Q x U : ℤ)
    (hN : 0 ≤ N) (hQ : N < Q) (hD : 0 < D)
    (hx : 0 ≤ x) (hU : x ≤ U) (hni : ¬ D ∣ N)
    (hcap : D*U < Q+N) : ¬ Q ∣ D*x-N := by
  intro hr
  have hlo := nonintegral_shadow_lower D N Q x hN hQ hD hx hni hr
  have hhi := mul_le_mul_of_nonneg_left hU (le_of_lt hD)
  linarith

/-- The run pattern h=2,t=4 has rational core 3/11.
It has an integer modular shadow at every modulus coprime to 11,
but the core itself is not integral. -/
theorem rational_core_example (Q : ℤ) (hc : IsCoprime (11 : ℤ) Q) :
    (∃ x : ℤ, Q ∣ 11*x-3) ∧ ¬ (11 : ℤ) ∣ 3 := by
  exact ⟨rational_shadow 11 3 Q hc, by norm_num⟩

end CollatzRunyan.CongruencePropagation

#print axioms CollatzRunyan.CongruencePropagation.forward_defect
#print axioms CollatzRunyan.CongruencePropagation.backward_defect
#print axioms CollatzRunyan.CongruencePropagation.rational_shadow
#print axioms CollatzRunyan.CongruencePropagation.simultaneous_shadow
#print axioms CollatzRunyan.CongruencePropagation.shadow_uniqueness
#print axioms CollatzRunyan.CongruencePropagation.nonintegral_shadow_lower
#print axioms CollatzRunyan.CongruencePropagation.bounded_shadow_exclusion
#print axioms CollatzRunyan.CongruencePropagation.rational_core_example
