import BinarySpectralSymmetry

namespace CollatzRunyan.BinaryDynamicalCompatibility
open CollatzRunyan.BinarySpectralSymmetry

-- Explicit coordinate representation of a swap-compatible linear map.
def symmetricMap (a b : ℚ) (v : Sector) : Sector :=
  (a * v.1 + b * v.2, b * v.1 + a * v.2)

theorem symmetricMap_conjugate (a b : ℚ) (v : Sector) :
    symmetricMap a b (conjugate v) = conjugate (symmetricMap a b v) := by
  apply Prod.ext <;> simp [symmetricMap, conjugate] <;> ring

theorem symmetricMap_plus (a b : ℚ) (v : Sector) :
    symmetricMap a b (pPlus v) = pPlus (symmetricMap a b v) := by
  apply Prod.ext <;> simp [symmetricMap, pPlus] <;> ring

theorem symmetricMap_minus (a b : ℚ) (v : Sector) :
    symmetricMap a b (pMinus v) = pMinus (symmetricMap a b v) := by
  apply Prod.ext <;> simp [symmetricMap, pMinus] <;> ring

theorem symmetric_eigenvalue (a b t : ℚ) :
    symmetricMap a b (t, t) = ((a+b)*t, (a+b)*t) := by
  apply Prod.ext <;> simp [symmetricMap] <;> ring

theorem antisymmetric_eigenvalue (a b t : ℚ) :
    symmetricMap a b (t, -t) = ((a-b)*t, -((a-b)*t)) := by
  apply Prod.ext <;> simp [symmetricMap] <;> ring

-- Equivariance alone is insufficient: coordinatewise squaring.
def squareMap (v : Sector) : Sector := (v.1^2, v.2^2)

theorem squareMap_conjugate (v : Sector) :
    squareMap (conjugate v) = conjugate (squareMap v) := by
  rfl

theorem squareMap_not_plus :
    squareMap (pPlus (2, 0)) ≠ pPlus (squareMap (2, 0)) := by
  intro h
  have h' := congrArg Prod.fst h
  norm_num [squareMap, pPlus] at h'

theorem squareMap_not_minus :
    squareMap (pMinus (2, 0)) ≠ pMinus (squareMap (2, 0)) := by
  intro h
  have h' := congrArg Prod.snd h
  norm_num [squareMap, pMinus] at h'

-- A general equivariant map preserves the fixed-point locus.
theorem fixed_locus_preserved (F : Sector → Sector)
    (hF : ∀ v, F (conjugate v) = conjugate (F v))
    (v : Sector) (hv : conjugate v = v) : conjugate (F v) = F v := by
  rw [← hF v, hv]

end CollatzRunyan.BinaryDynamicalCompatibility
