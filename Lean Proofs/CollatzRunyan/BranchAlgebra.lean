import Mathlib

namespace CollatzRunyan

/-! Algebraic portion of Lemma 1.3 of v2.1L.
The equal-length cancellation relation is an explicit hypothesis.
The Haar measure construction, Hilbert adjoints, spanning, and
linear independence of the full representation are not proved here. -/

theorem matrix_unit_mul {ι A : Type*} [DecidableEq ι] [MonoidWithZero A]
    (s t : ι → A)
    (h : ∀ j k, t j * s k = if j = k then 1 else 0)
    (u v r w : ι) :
    (s u * t v) * (s r * t w) =
      if v = r then s u * t w else 0 := by
  calc
    (s u * t v) * (s r * t w) =
        s u * (t v * s r) * t w := by simp only [mul_assoc]
    _ = _ := by
      rw [h v r]
      by_cases hv : v = r <;> simp [hv]

end CollatzRunyan
