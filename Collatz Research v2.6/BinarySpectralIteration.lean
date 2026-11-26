import BinaryDynamicalCompatibility

/-! Exact rational spectral iteration. No physical interpretation is assumed. -/
namespace CollatzRunyan.BinarySpectralIteration
open CollatzRunyan.BinarySpectralSymmetry
open CollatzRunyan.BinaryDynamicalCompatibility

def evolve (a b : ℚ) : ℕ → Sector → Sector
  | 0, v => v
  | k + 1, v => symmetricMap a b (evolve a b k v)

def spectralForm (a b : ℚ) (k : ℕ) (v : Sector) : Sector :=
  ((a+b)^k * (pPlus v).1 + (a-b)^k * (pMinus v).1,
   (a+b)^k * (pPlus v).2 + (a-b)^k * (pMinus v).2)

theorem evolve_spectral (a b : ℚ) (k : ℕ) (v : Sector) :
    evolve a b k v = spectralForm a b k v := by
  induction k with
  | zero =>
    apply Prod.ext <;> simp [evolve, spectralForm, pPlus, pMinus] <;> ring
  | succ k ih =>
    rw [evolve, ih]
    apply Prod.ext <;> simp [symmetricMap, spectralForm, pPlus, pMinus, pow_succ] <;> ring

theorem evolve_conjugate (a b : ℚ) (k : ℕ) (v : Sector) :
    evolve a b k (conjugate v) = conjugate (evolve a b k v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [evolve, evolve, ih, symmetricMap_conjugate]

theorem half_iteration (k : ℕ) (v : Sector) :
    evolve (3/4) (1/4) k v =
      ((pPlus v).1 + (1/2 : ℚ)^k * (pMinus v).1,
       (pPlus v).2 + (1/2 : ℚ)^k * (pMinus v).2) := by
  rw [evolve_spectral]
  norm_num [spectralForm]

theorem half_sum_preserved (k : ℕ) (v : Sector) :
    (evolve (3/4) (1/4) k v).1 + (evolve (3/4) (1/4) k v).2 = v.1 + v.2 := by
  rw [half_iteration]
  simp only [pPlus, pMinus]
  ring

theorem half_difference (k : ℕ) (v : Sector) :
    (evolve (3/4) (1/4) k v).1 - (evolve (3/4) (1/4) k v).2 =
      (1/2 : ℚ)^k * (v.1 - v.2) := by
  rw [half_iteration]
  simp only [pPlus, pMinus]
  ring

-- Exact denominator growth; this is not a formalization of the Q_2 norm.
theorem half_power_reciprocal (k : ℕ) :
    (1/2 : ℚ)^k * 2^k = 1 := by
  rw [← mul_pow]
  norm_num

end CollatzRunyan.BinarySpectralIteration
