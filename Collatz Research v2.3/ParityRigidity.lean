import Mathlib

/-!
# Collatz–Runyan: parity repetition rigidity
Standalone arithmetic layer. For a repeated shortcut parity block, use
A = 3^a, M = 2^d and B = its affine offset. The hypothesis `h` is
provided by the affine trajectory formula at each block boundary.
This file does not assert universal Collatz convergence.
-/

namespace CollatzRunyan.ParityRigidity

theorem affine_telescoping (A M B : ℤ) (x : ℕ → ℤ) (r : ℕ)
    (h : ∀ j < r, M * x (j + 1) = A * x j + B) :
    M ^ r * ((A - M) * x r + B) =
      A ^ r * ((A - M) * x 0 + B) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hr := ih (fun j hj => h j (by omega))
    have hj := h r (by omega)
    have hs : M * ((A - M) * x (r + 1) + B) =
        A * ((A - M) * x r + B) := by
      linear_combination (A - M) * hj
    calc
      M ^ (r + 1) * ((A - M) * x (r + 1) + B) =
          M ^ r * (M * ((A - M) * x (r + 1) + B)) := by
            rw [pow_succ]; ring
      _ = M ^ r * (A * ((A - M) * x r + B)) := by rw [hs]
      _ = A * (M ^ r * ((A - M) * x r + B)) := by ring
      _ = A * (A ^ r * ((A - M) * x 0 + B)) := by rw [hr]
      _ = A ^ (r + 1) * ((A - M) * x 0 + B) := by
        rw [pow_succ]; ring

theorem affine_repeat_dvd (A M B : ℤ) (x : ℕ → ℤ) (r : ℕ)
    (hc : IsCoprime M A)
    (h : ∀ j < r, M * x (j + 1) = A * x j + B) :
    M ^ r ∣ (A - M) * x 0 + B := by
  have hp : IsCoprime (M ^ r) (A ^ r) := hc.pow
  have hd : M ^ r ∣ A ^ r * ((A - M) * x 0 + B) :=
    ⟨(A - M) * x r + B, (affine_telescoping A M B x r h).symm⟩
  exact hp.dvd_of_dvd_mul_left hd

theorem two_three_coprime (d a : ℕ) :
    IsCoprime ((2 : ℤ) ^ d) ((3 : ℤ) ^ a) := by
  have h : IsCoprime (2 : ℤ) 3 := by
    refine ⟨-1, 1, ?_⟩
    norm_num
  exact h.pow

theorem parity_repeat_dvd (d a r : ℕ) (B : ℤ) (x : ℕ → ℤ)
    (h : ∀ j < r, (2 : ℤ) ^ d * x (j + 1) =
      (3 : ℤ) ^ a * x j + B) :
    (2 : ℤ) ^ (d * r) ∣ ((3 : ℤ) ^ a - (2 : ℤ) ^ d) * x 0 + B := by
  rw [pow_mul]
  exact affine_repeat_dvd _ _ _ x r (two_three_coprime d a) h

theorem parity_repeat_bound (d a r : ℕ) (B : ℤ) (x : ℕ → ℤ)
    (h : ∀ j < r, (2 : ℤ) ^ d * x (j + 1) =
      (3 : ℤ) ^ a * x j + B)
    (hn : ((3 : ℤ) ^ a - (2 : ℤ) ^ d) * x 0 + B ≠ 0) :
    ((2 : ℤ) ^ (d * r)).natAbs ≤
      (((3 : ℤ) ^ a - (2 : ℤ) ^ d) * x 0 + B).natAbs := by
  exact Int.natAbs_le_of_dvd_ne_zero (parity_repeat_dvd d a r B x h) hn

theorem zero_discriminant_return (A M B u v : ℤ)
    (hm : M ≠ 0) (h : M * v = A * u + B)
    (hz : (A - M) * u + B = 0) : v = u := by
  have hz' : M * (v - u) = 0 := by
    linear_combination h + hz
  rcases mul_eq_zero.mp hz' with hM | huv
  · exact (hm hM).elim
  · omega

#print axioms affine_telescoping
#print axioms affine_repeat_dvd
#print axioms parity_repeat_dvd
#print axioms parity_repeat_bound
#print axioms zero_discriminant_return

end CollatzRunyan.ParityRigidity
