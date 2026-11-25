import Mathlib

namespace CollatzRunyan

/-! Rational affine extensions, not globally invertible maps on the
2-adic integers. Compare v2.1L, Lemma 3.1. -/

def f0 (x : ℚ) : ℚ := 2 * x
def f1 (x : ℚ) : ℚ := (2 * x - 1) / 3
def f0Inv (x : ℚ) : ℚ := x / 2
def f1Inv (x : ℚ) : ℚ := (3 * x + 1) / 2

theorem f0_left_inverse (x : ℚ) : f0Inv (f0 x) = x := by
  unfold f0Inv f0
  ring

theorem f1_left_inverse (x : ℚ) : f1Inv (f1 x) = x := by
  unfold f1Inv f1
  ring

theorem f0_right_inverse (x : ℚ) : f0 (f0Inv x) = x := by
  unfold f0Inv f0
  ring

theorem f1_right_inverse (x : ℚ) : f1 (f1Inv x) = x := by
  unfold f1Inv f1
  ring

theorem affine_commutator (x : ℚ) :
    f0 (f1 (f0Inv (f1Inv x))) = x - 1 / 3 := by
  unfold f0 f1 f0Inv f1Inv
  ring

/-! An exact descent equivalence conditional on the affine trajectory
identity. The trajectory identity itself is not formalized here. -/

theorem descent_certificate (n y A B C : ℤ)
    (hB : 0 < B) (h : B * y = A * n + C) :
    y < n ↔ 0 < (B - A) * n - C := by
  have heq : B * (n - y) = (B - A) * n - C := by
    calc
      B * (n - y) = B * n - B * y := by ring
      _ = (B - A) * n - C := by rw [h]; ring
  constructor
  · intro hy
    rw [← heq]
    exact mul_pos hB (sub_pos.mpr hy)
  · intro hc
    have hp : 0 < B * (n - y) := by rw [heq]; exact hc
    by_contra! hn
    have hnon : B * (n - y) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hB) (sub_nonpos.mpr hn)
    exact (not_lt_of_ge hnon) hp

/-! Original spectral parameters, checked without floating point. -/

theorem pell_three : (2 : ℤ)^2 - 3 * 1^2 = 1 := by norm_num
theorem pell_thirtyseven : (73 : ℤ)^2 - 37 * 12^2 = 1 := by norm_num
theorem pell_137 : (6083073 : ℤ)^2 - 137 * 519712^2 = 1 := by norm_num

end CollatzRunyan
