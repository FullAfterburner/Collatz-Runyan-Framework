import Mathlib

/-! Rational two-sector spectral decomposition. The swap operator models
an abstract involution, not a physical charge-conjugation law. -/
namespace CollatzRunyan.BinarySpectralSymmetry

abbrev Sector := ℚ × ℚ

def conjugate (v : Sector) : Sector := (v.2, v.1)
def pPlus (v : Sector) : Sector := ((v.1 + v.2) / 2, (v.1 + v.2) / 2)
def pMinus (v : Sector) : Sector := ((v.1 - v.2) / 2, (v.2 - v.1) / 2)

theorem conjugate_involution (v : Sector) : conjugate (conjugate v) = v := by
  cases v
  rfl

theorem plus_idempotent (v : Sector) : pPlus (pPlus v) = pPlus v := by
  apply Prod.ext <;> simp [pPlus]

theorem minus_idempotent (v : Sector) : pMinus (pMinus v) = pMinus v := by
  apply Prod.ext <;> simp [pMinus] <;> ring

theorem plus_minus_zero (v : Sector) : pPlus (pMinus v) = (0, 0) := by
  apply Prod.ext <;> simp [pPlus, pMinus] <;> ring

theorem minus_plus_zero (v : Sector) : pMinus (pPlus v) = (0, 0) := by
  apply Prod.ext <;> simp [pPlus, pMinus]

theorem reconstruction (v : Sector) :
    ((pPlus v).1 + (pMinus v).1, (pPlus v).2 + (pMinus v).2) = v := by
  apply Prod.ext <;> simp [pPlus, pMinus] <;> ring

theorem plus_invariant (v : Sector) : conjugate (pPlus v) = pPlus v := by
  rfl

theorem minus_anti_invariant (v : Sector) :
    conjugate (pMinus v) = (-(pMinus v).1, -(pMinus v).2) := by
  apply Prod.ext <;> simp [conjugate, pMinus] <;> ring

theorem plus_conjugate (v : Sector) : pPlus (conjugate v) = pPlus v := by
  apply Prod.ext <;> simp [conjugate, pPlus] <;> ring

theorem minus_conjugate (v : Sector) :
    pMinus (conjugate v) = (-(pMinus v).1, -(pMinus v).2) := by
  apply Prod.ext <;> simp [conjugate, pMinus] <;> ring

-- Integer inputs admit integral half-sum and half-difference exactly
-- when their parities agree. This avoids dividing by 2 in Z_2.
theorem integral_split_iff (a b : ℤ) :
    (∃ s d : ℤ, a = s + d ∧ b = s - d) ↔ a % 2 = b % 2 := by
  constructor
  · rintro ⟨s, d, ha, hb⟩
    omega
  · intro h
    refine ⟨(a + b) / 2, (a - b) / 2, ?_, ?_⟩ <;> omega

theorem integral_split_unique (a b s d t e : ℤ)
    (ha : a = s + d) (hb : b = s - d)
    (hc : a = t + e) (hd : b = t - e) : s = t ∧ d = e := by
  constructor <;> omega

end CollatzRunyan.BinarySpectralSymmetry
