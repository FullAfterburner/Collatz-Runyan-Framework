import Mathlib

/-! Ordered zero-sum block rigidity.
These are conditional affine arithmetic results, not universal cycle exclusion.
For a split into two nonempty accelerated Collatz blocks, the full
numerator is A2*b1 + M1*b2. The local numerators are positive.
The connection between modular weights and local block numerators is
encoded by an explicit coprime congruence hypothesis. -/
namespace CollatzRunyan.ZeroSumRigidity

-- Transfer a zero-sum condition through a unit multiple modulo q.
theorem block_zero_iff (q c s b : ℤ) (hc : IsCoprime q c)
    (h : q ∣ c*s-b) : (q ∣ s) ↔ (q ∣ b) := by
  constructor
  · rintro ⟨t, ht⟩
    have hcs : q ∣ c*s := by
      refine ⟨c*t, ?_⟩
      rw [ht]
      ring
    have hd := dvd_sub hcs h
    have he : c*s-(c*s-b) = b := by ring
    rwa [he] at hd
  · intro hb
    apply hc.dvd_of_dvd_mul_left
    have hd := dvd_add h hb
    have he : c*s-b+b = c*s := by ring
    rwa [he] at hd

-- Two consecutive affine blocks compose without losing their local offsets.
theorem affine_split (A1 A2 M1 M2 b1 b2 x y z : ℤ)
    (h1 : M1*y = A1*x+b1) (h2 : M2*z = A2*y+b2) :
    M1*M2*z = A1*A2*x+A2*b1+M1*b2 := by
  calc
    M1*M2*z = M1*(M2*z) := by ring
    _ = M1*(A2*y+b2) := by rw [h2]
    _ = A2*(M1*y)+M1*b2 := by ring
    _ = A1*A2*x+A2*b1+M1*b2 := by rw [h1]; ring

-- If the total numerator vanishes mod q, either zero block forces the other.
theorem complementary_blocks (q A2 M1 b1 b2 : ℤ)
    (hA : IsCoprime q A2) (hM : IsCoprime q M1)
    (h : q ∣ A2*b1+M1*b2) : (q ∣ b1) ↔ (q ∣ b2) := by
  constructor
  · rintro ⟨t, ht⟩
    have h1 : q ∣ A2*b1 := by
      refine ⟨A2*t, ?_⟩
      rw [ht]
      ring
    apply hM.dvd_of_dvd_mul_left
    have hd := dvd_sub h h1
    have he : A2*b1+M1*b2-A2*b1 = M1*b2 := by ring
    rwa [he] at hd
  · rintro ⟨t, ht⟩
    have h2 : q ∣ M1*b2 := by
      refine ⟨M1*t, ?_⟩
      rw [ht]
      ring
    apply hA.dvd_of_dvd_mul_left
    have hd := dvd_sub h h2
    have he : A2*b1+M1*b2-M1*b2 = A2*b1 := by ring
    rwa [he] at hd

-- A positive multiple of a positive modulus is at least the modulus.
theorem positive_multiple_lower (q b : ℤ) (hq : 0 < q) (hb : 0 < b)
    (hd : q ∣ b) : q ≤ b := by
  obtain ⟨t, ht⟩ := hd
  by_cases hp : 0 < t
  · have hm := mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ t-1 by omega)
    nlinarith
  · have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ q by omega)
        (show t ≤ 0 by omega)
    omega

-- A zero-sum split gives a quantitative lower bound on the full numerator.
theorem zero_split_bound (q A2 M1 b1 b2 : ℤ)
    (hq : 0 < q) (hA0 : 0 ≤ A2) (hM0 : 0 ≤ M1)
    (hb1 : 0 < b1) (hb2 : 0 < b2)
    (hA : IsCoprime q A2) (hM : IsCoprime q M1)
    (htotal : q ∣ A2*b1+M1*b2) (hzero : q ∣ b1) :
    q*(A2+M1) ≤ A2*b1+M1*b2 := by
  have hz2 := (complementary_blocks q A2 M1 b1 b2 hA hM htotal).mp hzero
  have h1 := positive_multiple_lower q b1 hq hb1 hzero
  have h2 := positive_multiple_lower q b2 hq hb2 hz2
  have h3 := mul_le_mul_of_nonneg_left h1 hA0
  have h4 := mul_le_mul_of_nonneg_left h2 hM0
  nlinarith

-- With the full denominator as modulus, this bounds the cycle value itself.
theorem full_denominator_lower (D A2 M1 b1 b2 x : ℤ)
    (hD : 0 < D) (hA0 : 0 ≤ A2) (hM0 : 0 ≤ M1)
    (hb1 : 0 < b1) (hb2 : 0 < b2)
    (hA : IsCoprime D A2) (hM : IsCoprime D M1)
    (hcycle : D*x = A2*b1+M1*b2) (hzero : D ∣ b1) :
    A2+M1 ≤ x := by
  have ht : D ∣ A2*b1+M1*b2 := ⟨x, hcycle.symm⟩
  have hb := zero_split_bound D A2 M1 b1 b2 hD hA0 hM0 hb1 hb2 hA hM ht hzero
  rw [← hcycle] at hb
  by_contra hn
  have hh : 0 < A2+M1-x := by omega
  have hp := mul_pos hD hh
  nlinarith

-- An independent upper bound below this lower bound rules out the split.
theorem small_cycle_no_zero_split (D A2 M1 b1 b2 x : ℤ)
    (hD : 0 < D) (hA0 : 0 ≤ A2) (hM0 : 0 ≤ M1)
    (hb1 : 0 < b1) (hb2 : 0 < b2)
    (hA : IsCoprime D A2) (hM : IsCoprime D M1)
    (hcycle : D*x = A2*b1+M1*b2) (hsmall : x < A2+M1) :
    ¬ D ∣ b1 := by
  intro hz
  exact (not_lt_of_ge (full_denominator_lower D A2 M1 b1 b2 x hD hA0 hM0
    hb1 hb2 hA hM hcycle hz)) hsmall

-- Gaps (1,2,3,2): modular balance with a proper zero-sum segment,
-- yet the full affine denominator does not divide the numerator.
theorem proper_zero_segment_example :
    (2 : ℤ)^8-3^4 = 175 ∧
    (3 : ℤ)^3+3^2*2+3*8+64 = 133 ∧
    (7 : ℤ) ∣ (175 : ℤ) ∧ (7 : ℤ) ∣ (133 : ℤ) ∧
    (7 : ℤ) ∣ (1+3+4+6 : ℤ) ∧ (7 : ℤ) ∣ (3+4 : ℤ) ∧
    ¬ (175 : ℤ) ∣ (133 : ℤ) := by norm_num

#print axioms block_zero_iff
#print axioms affine_split
#print axioms complementary_blocks
#print axioms positive_multiple_lower
#print axioms zero_split_bound
#print axioms full_denominator_lower
#print axioms small_cycle_no_zero_split
#print axioms proper_zero_segment_example

end CollatzRunyan.ZeroSumRigidity
