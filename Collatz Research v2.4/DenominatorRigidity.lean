import Mathlib

/-!
# Collatz–Runyan: denominator rigidity
Arithmetic lemmas for cyclic rotations and two-position transpositions.
The variables represent exact affine coefficients of parity blocks.
Connecting them to a concrete parity word uses the affine composition law.
No universal cycle exclusion or Collatz convergence is asserted.
-/
namespace CollatzRunyan.DenominatorRigidity

-- If M and A are coprime, so is their difference with either of them.
theorem difference_coprime (M A : ℤ) (h : IsCoprime M A) :
    IsCoprime (M - A) M ∧ IsCoprime (M - A) A := by
  obtain ⟨u, v, h⟩ := h
  constructor
  · refine ⟨-v, u+v, ?_⟩
    linear_combination h
  · refine ⟨u, u+v, ?_⟩
    linear_combination h

-- A single cyclic rotation preserves divisibility by every divisor d of D,
-- provided that 2 and the leading branch multiplier are units modulo d.
theorem rotation_divisibility_iff (d D A B C e : ℤ)
    (h2 : IsCoprime d 2) (hA : IsCoprime d A) (hd : d ∣ D)
    (h : 2*C = A*B + e*D) : (d ∣ B) ↔ (d ∣ C) := by
  obtain ⟨v, hv⟩ := hd
  constructor
  · rintro ⟨u, hu⟩
    apply h2.dvd_of_dvd_mul_left
    refine ⟨A*u+e*v, ?_⟩
    rw [h, hu, hv]
    ring
  · rintro ⟨u, hu⟩
    apply hA.dvd_of_dvd_mul_left
    refine ⟨2*u-e*v, ?_⟩
    calc
      A*B = 2*C-e*D := by linear_combination -h
      _ = _ := by rw [hu, hv]; ring

-- Compare blocks 1 U 0 and 0 U 1, where U has affine triple (A,M,B).
theorem middle_swap_gap (A M B : ℤ) :
    (6*B+2*M) - (A+2*B) = 2*M-A+4*B := by ring

-- Insert the swapped blocks into a common prefix (L,P) and suffix (R,S).
-- L is the prefix's denominator and R the suffix's multiplier.
def offsetOneZero (L P A M B R S : ℤ) : ℤ :=
  R*(3*A*P+L*(A+2*B))+4*L*M*S

def offsetZeroOne (L P A M B R S : ℤ) : ℤ :=
  R*(3*A*P+L*(6*B+2*M))+4*L*M*S

theorem contextual_swap_gap (L P A M B R S : ℤ) :
    offsetZeroOne L P A M B R S - offsetOneZero L P A M B R S =
      (L*R)*(2*M-A+4*B) := by
  unfold offsetZeroOne offsetOneZero
  ring

-- If two rotated numerators are integral multiples of D, D divides the
-- difference, and all factors coprime to D can be cancelled.
theorem coprime_gap_certificate (D F U V H : ℤ)
    (hc : IsCoprime D F) (h : V-U = F*H)
    (hu : D ∣ U) (hv : D ∣ V) : D ∣ H := by
  apply hc.dvd_of_dvd_mul_left
  rw [← h]
  exact dvd_sub hv hu

theorem two_position_obstruction (D L P A M B R S : ℤ)
    (hc : IsCoprime D (L*R))
    (hu : D ∣ offsetOneZero L P A M B R S)
    (hv : D ∣ offsetZeroOne L P A M B R S) :
    D ∣ (2*M-A+4*B) := by
  exact coprime_gap_certificate D (L*R) _ _ _ hc
    (contextual_swap_gap L P A M B R S) hu hv

-- Empty middle block: A=M=1, B=0. An adjacent transposition forces D | 1.
theorem adjacent_swap_forces_unit (D L P R S : ℤ)
    (hc : IsCoprime D (L*R))
    (hu : D ∣ offsetOneZero L P 1 1 0 R S)
    (hv : D ∣ offsetZeroOne L P 1 1 0 R S) : D ∣ (1 : ℤ) := by
  have h := two_position_obstruction D L P 1 1 0 R S hc hu hv
  have he : (2 : ℤ)*1-1+4*0 = 1 := by norm_num
  rw [he] at h
  exact h

#print axioms difference_coprime
#print axioms rotation_divisibility_iff
#print axioms middle_swap_gap
#print axioms contextual_swap_gap
#print axioms coprime_gap_certificate
#print axioms two_position_obstruction
#print axioms adjacent_swap_forces_unit

end CollatzRunyan.DenominatorRigidity
