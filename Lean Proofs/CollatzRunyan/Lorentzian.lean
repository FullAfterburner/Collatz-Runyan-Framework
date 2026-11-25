import Mathlib

namespace CollatzRunyan

/-! Polynomial core of v2.1L Theorem 2.
This proves the two-by-two determinant formula for entries written
using a square root of minus one; it does not identify coordinates
with physical spacetime or formalize the full Lorentz group. -/

theorem lorentzian_polynomial (t x y z : ℝ) :
    (t + z) * (t - z) - (x^2 + y^2) =
      t^2 - x^2 - y^2 - z^2 := by
  ring

theorem hermitian_determinant_formula {R : Type*} [CommRing R]
    (t x y z i : R) (hi : i^2 = -1) :
    (t + z) * (t - z) - (x - y * i) * (x + y * i) =
      t^2 - x^2 - y^2 - z^2 := by
  linear_combination y^2 * hi

theorem boost_invariant (u w t z : ℝ) (h : u^2 - w^2 = 1) :
    (u*t + w*z)^2 - (w*t + u*z)^2 = t^2 - z^2 := by
  linear_combination (t^2 - z^2) * h

end CollatzRunyan
