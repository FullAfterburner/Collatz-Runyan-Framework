import Mathlib

/-!
# LocalDivisorRigidity
Adjacent run equations imply a joint core congruence. Four elementary
lemmas are reused from the already checked IntegralityRigidity module
so this file can be compiled independently. The concrete run-envelope
example is arithmetic; the general cycle interpretation and the Python
necklace enumeration are external. No universal Collatz claim is made.
-/
namespace CollatzRunyan.LocalDivisorRigidity

theorem incoming_residue (A M B u x R : ℤ) (hc : IsCoprime A M)
    (h : M*x = A*u+B) (hr : A ∣ M*R-B) : A ∣ x-R := by
  have hx : A ∣ M*x-B := ⟨u, by linarith only [h]⟩
  have hd := dvd_sub hx hr
  have he : M*x-B-(M*R-B) = M*(x-R) := by ring
  rw [he] at hd
  exact hc.dvd_of_dvd_mul_left hd

theorem outgoing_residue (C N E x y R t : ℤ) (hc : IsCoprime (2*N) C)
    (h : N*y = C*x+E) (hy : y = 2*t+1)
    (hr : 2*N ∣ C*R+E-N) : 2*N ∣ x-R := by
  have hx : 2*N ∣ C*x+E-N := by
    refine ⟨t, ?_⟩
    rw [hy] at h
    nlinarith only [h]
  have hd := dvd_sub hx hr
  have he : C*x+E-N-(C*R+E-N) = C*(x-R) := by ring
  rw [he] at hd
  exact hc.dvd_of_dvd_mul_left hd

theorem coprime_joint_residue (P Q x R : ℤ) (hc : IsCoprime Q P)
    (hp : P ∣ x-R) (hq : Q ∣ x-R) : P*Q ∣ x-R := by
  obtain ⟨u, hu⟩ := hp
  have hd : Q ∣ P*u := by rw [← hu]; exact hq
  obtain ⟨v, hv⟩ := hc.dvd_of_dvd_mul_left hd
  refine ⟨v, ?_⟩
  rw [hu, hv]
  ring

theorem least_representative_lower (P L R x : ℤ) (hP : 0 < P)
    (hR : L ≤ R) (hR' : R < L+P) (hx : L ≤ x)
    (hd : P ∣ x-R) : R ≤ x := by
  obtain ⟨t, ht⟩ := hd
  by_contra hn
  by_cases h : 0 ≤ t
  · have hp := mul_nonneg (le_of_lt hP) h
    omega
  · have ht1 : 0 ≤ -t-1 := by omega
    have hp := mul_nonneg (le_of_lt hP) ht1
    nlinarith only [ht, hR', hx, hp]

/-- Incoming and outgoing chain equations constrain the same arithmetic core.
    The endpoint of the outgoing equation is assumed odd. -/
theorem adjacent_core_residue (A M B C N E u x y R z : ℤ)
    (hc1 : IsCoprime A M) (hc2 : IsCoprime (2*N) C)
    (hc3 : IsCoprime (2*N) A)
    (hin : M*x = A*u+B) (hout : N*y = C*x+E)
    (hy : y = 2*z+1) (hr1 : A ∣ M*R-B) (hr2 : 2*N ∣ C*R+E-N) :
    A*(2*N) ∣ x-R := by
  exact coprime_joint_residue A (2*N) x R hc3
    (incoming_residue A M B u x R hc1 hin hr1)
    (outgoing_residue C N E x y R z hc2 hout hy hr2)

/-- For any divisor of the incoming odd coefficient, divisibility of
    the endpoint is equivalent to divisibility of the offset. -/
theorem local_offset_iff (q A P C u v : ℤ)
    (hc : IsCoprime q P) (hA : q ∣ A)
    (he : P*v = A*u+C) : q ∣ v ↔ q ∣ C := by
  have hAu : q ∣ A*u := by
    obtain ⟨s, hs⟩ := hA
    refine ⟨s*u, ?_⟩
    rw [hs]
    ring
  constructor
  · intro hv
    obtain ⟨s, hs⟩ := hv
    have hPv : q ∣ P*v := by
      refine ⟨P*s, ?_⟩
      rw [hs]
      ring
    have h := dvd_sub hPv hAu
    rw [show P*v-A*u = C by linarith only [he]] at h
    exact h
  · intro hC
    have h := dvd_add hAu hC
    rw [← he] at h
    exact hc.dvd_of_dvd_mul_left h

/-- Once a representative has been selected in [L,L+modulus), both
    adjacent equations force a lower bound on the actual core. -/
theorem adjacent_core_lower (A M B C N E u x y R z L : ℤ)
    (hc1 : IsCoprime A M) (hc2 : IsCoprime (2*N) C)
    (hc3 : IsCoprime (2*N) A)
    (hin : M*x = A*u+B) (hout : N*y = C*x+E)
    (hy : y = 2*z+1) (hr1 : A ∣ M*R-B) (hr2 : 2*N ∣ C*R+E-N)
    (hp : 0 < A*(2*N)) (hL : L ≤ R) (hR : R < L+A*(2*N))
    (hx : L ≤ x) : R ≤ x := by
  have hd := adjacent_core_residue A M B C N E u x y R z hc1 hc2 hc3 hin hout hy hr1 hr2
  exact least_representative_lower (A*(2*N)) L R x hp hL hR hx hd

/-- Run lengths h=(1,2,2), t=(1,1,1). The old, incoming-only,
    and outgoing-only bounds survive; the joint bounds fail. -/
theorem joint_only_example :
    (8 : ℤ)*(2*7-1)*(4*5-1)*(4*5-1) ≤ (3*7-1)*(9*5-1)*(9*5-1) ∧
    (8 : ℤ)*(2*7-1)*(4*5-1)*(4*17-1) ≤ (3*7-1)*(9*5-1)*(9*17-1) ∧
    (8 : ℤ)*(2*13-1)*(4*15-1)*(4*3-1) ≤ (3*13-1)*(9*15-1)*(9*3-1) ∧
    (8 : ℤ)*(2*61-1)*(4*47-1)*(4*35-1) > (3*61-1)*(9*47-1)*(9*35-1) := by
  norm_num

end CollatzRunyan.LocalDivisorRigidity

#print axioms CollatzRunyan.LocalDivisorRigidity.incoming_residue
#print axioms CollatzRunyan.LocalDivisorRigidity.outgoing_residue
#print axioms CollatzRunyan.LocalDivisorRigidity.coprime_joint_residue
#print axioms CollatzRunyan.LocalDivisorRigidity.least_representative_lower
#print axioms CollatzRunyan.LocalDivisorRigidity.adjacent_core_residue
#print axioms CollatzRunyan.LocalDivisorRigidity.local_offset_iff
#print axioms CollatzRunyan.LocalDivisorRigidity.adjacent_core_lower
#print axioms CollatzRunyan.LocalDivisorRigidity.joint_only_example
