import Mathlib

/-! Two-sided affine integrality certificates for hypothetical odd Collatz
cycles. The incoming and outgoing affine equations are explicit hypotheses.
The minimum bound is derived from an explicit product inequality. The
finite search and the identification of minimum positions are external.
No claim of universal cycle exclusion is made. -/
namespace CollatzRunyan.IntegralityRigidity

-- An incoming affine block determines the endpoint modulo its odd factor.
theorem incoming_residue (A M B u x R : ℤ) (hc : IsCoprime A M)
    (h : M*x = A*u+B) (hr : A ∣ M*R-B) : A ∣ x-R := by
  have hx : A ∣ M*x-B := ⟨u, by linarith only [h]⟩
  have hd := dvd_sub hx hr
  have he : M*x-B-(M*R-B) = M*(x-R) := by ring
  rw [he] at hd
  exact hc.dvd_of_dvd_mul_left hd

-- An odd outgoing endpoint supplies one extra bit of parity information.
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

-- Coprime modulus constraints combine into one product modulus.
theorem coprime_joint_residue (P Q x R : ℤ) (hc : IsCoprime Q P)
    (hp : P ∣ x-R) (hq : Q ∣ x-R) : P*Q ∣ x-R := by
  obtain ⟨u, hu⟩ := hp
  have hd : Q ∣ P*u := by rw [← hu]; exact hq
  obtain ⟨v, hv⟩ := hc.dvd_of_dvd_mul_left hd
  refine ⟨v, ?_⟩
  rw [hu, hv]
  ring

-- Combine the two actual affine constraints at the same boundary.
theorem two_sided_residue (A M B C N E u x y R t : ℤ)
    (hc1 : IsCoprime A M) (hc2 : IsCoprime (2*N) C)
    (hc3 : IsCoprime (2*N) A)
    (hin : M*x = A*u+B) (hout : N*y = C*x+E)
    (hy : y = 2*t+1) (hr1 : A ∣ M*R-B) (hr2 : 2*N ∣ C*R+E-N) :
    A*(2*N) ∣ x-R := by
  exact coprime_joint_residue A (2*N) x R hc3
    (incoming_residue A M B u x R hc1 hin hr1)
    (outgoing_residue C N E x y R t hc2 hout hy hr2)

-- R is the representative of its residue class in [L,L+P).
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

-- A residue class with first representative above the upper bound is empty.
theorem interval_exclusion (P L R U : ℤ) (hP : 0 < P)
    (hR : L ≤ R) (hR' : R < L+P) (hU : U < R) :
    ¬ ∃ x : ℤ, L ≤ x ∧ x ≤ U ∧ P ∣ x-R := by
  rintro ⟨x, hx, hu, hd⟩
  have h := least_representative_lower P L R x hP hR hR' hx hd
  omega

-- Elementary monotonicity of integer powers on nonnegative integers.
theorem nonneg_power_mono (u v : ℤ) (hu : 0 ≤ u) (h : u ≤ v) (a : ℕ) :
    u^a ≤ v^a := by
  have hv : 0 ≤ v := le_trans hu h
  induction a with
  | zero => simp
  | succ a ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih h hu (by positivity)

-- Substitute a positive lower bound for a cycle minimum in the product test.
theorem product_bound_at_lower (a : ℕ) (M x R : ℤ)
    (hR : 0 < R) (hx : R ≤ x)
    (hcycle : M*x^a ≤ (3*x+1)^a) : M*R^a ≤ (3*R+1)^a := by
  have hx0 : 0 < x := lt_of_lt_of_le hR hx
  have hcross : R*(3*x+1) ≤ x*(3*R+1) := by nlinarith only [hx]
  have hpow := nonneg_power_mono (R*(3*x+1)) (x*(3*R+1)) (by positivity) hcross a
  rw [mul_pow, mul_pow] at hpow
  have hs := mul_le_mul_of_nonneg_left hcycle (show 0 ≤ R^a by positivity)
  have hh : x^a*(M*R^a) ≤ x^a*(3*R+1)^a := by
    calc
      x^a*(M*R^a) = R^a*(M*x^a) := by ring
      _ ≤ R^a*(3*x+1)^a := hs
      _ ≤ x^a*(3*R+1)^a := hpow
  by_contra hn
  have hp := mul_pos (show 0 < x^a by positivity)
    (show 0 < M*R^a-(3*R+1)^a by omega)
  nlinarith only [hh, hp]

-- Direct conflict between a joint residue and the cycle product inequality.
theorem joint_product_exclusion (a : ℕ) (M P L R x : ℤ)
    (hP : 0 < P) (hR : L ≤ R) (hR' : R < L+P)
    (hR0 : 0 < R) (hx : L ≤ x) (hd : P ∣ x-R)
    (hcycle : M*x^a ≤ (3*x+1)^a)
    (hconflict : (3*R+1)^a < M*R^a) : False := by
  have h := least_representative_lower P L R x hP hR hR' hx hd
  exact (not_lt_of_ge (product_bound_at_lower a M x R hR0 h hcycle)) hconflict

-- Gaps (1,1,3): at the eligible minimum, incoming residue 2 mod 3,
-- outgoing residue 3 mod 4; joint residue 11 mod 12 excludes [3,5].
theorem joint_only_example :
    (3 : ℤ) ∣ 8*11-1 ∧ (4 : ℤ) ∣ 3*11+1-2 ∧
    (3 : ℤ) ∣ 5-2 ∧ (4 : ℤ) ∣ 3-3 ∧
    ¬ ∃ x : ℤ, 3 ≤ x ∧ x ≤ 5 ∧ (12 : ℤ) ∣ x-11 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  exact interval_exclusion 12 3 11 5 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

#print axioms incoming_residue
#print axioms outgoing_residue
#print axioms coprime_joint_residue
#print axioms two_sided_residue
#print axioms least_representative_lower
#print axioms interval_exclusion
#print axioms nonneg_power_mono
#print axioms product_bound_at_lower
#print axioms joint_product_exclusion
#print axioms joint_only_example

end CollatzRunyan.IntegralityRigidity
