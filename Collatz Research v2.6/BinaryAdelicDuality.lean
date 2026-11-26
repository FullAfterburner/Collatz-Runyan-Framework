import BinarySpectralIteration
import Mathlib.NumberTheory.Padics.PadicNorm

/-! Two-place norm duality for the rational binary spectral iteration. -/
namespace CollatzRunyan.BinaryAdelicDuality
open CollatzRunyan.BinarySpectralSymmetry
open CollatzRunyan.BinarySpectralIteration

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem two_norm : padicNorm 2 (2 : ℚ) = 1 / 2 := by
  have h := padicNorm.padicNorm_p (p := 2) (by decide)
  norm_num at h
  simpa using h

theorem half_norm : padicNorm 2 (1 / 2 : ℚ) = 2 := by
  rw [padicNorm.div, padicNorm.one, two_norm]
  norm_num

theorem half_power_norm (k : ℕ) :
    padicNorm 2 ((1 / 2 : ℚ)^k) = (2 : ℚ)^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, padicNorm.mul, ih, half_norm, pow_succ]

theorem half_power_abs (k : ℕ) :
    |(1 / 2 : ℚ)^k| = (1 / 2 : ℚ)^k := by
  exact abs_of_nonneg (by positivity)

theorem half_power_duality (k : ℕ) :
    |(1 / 2 : ℚ)^k| * padicNorm 2 ((1 / 2 : ℚ)^k) = 1 := by
  rw [half_power_abs, half_power_norm]
  exact half_power_reciprocal k

theorem difference_padic (k : ℕ) (v : Sector) :
    padicNorm 2 ((evolve (3/4) (1/4) k v).1 - (evolve (3/4) (1/4) k v).2) =
      (2 : ℚ)^k * padicNorm 2 (v.1 - v.2) := by
  rw [half_difference, padicNorm.mul, half_power_norm]

theorem difference_abs (k : ℕ) (v : Sector) :
    |(evolve (3/4) (1/4) k v).1 - (evolve (3/4) (1/4) k v).2| =
      (1/2 : ℚ)^k * |v.1 - v.2| := by
  rw [half_difference, abs_mul, half_power_abs]

theorem difference_duality (k : ℕ) (v : Sector) :
    |(evolve (3/4) (1/4) k v).1 - (evolve (3/4) (1/4) k v).2| *
      padicNorm 2 ((evolve (3/4) (1/4) k v).1 - (evolve (3/4) (1/4) k v).2) =
      |v.1 - v.2| * padicNorm 2 (v.1 - v.2) := by
  rw [difference_abs, difference_padic]
  calc
    _ = ((1/2 : ℚ)^k * 2^k) * (|v.1 - v.2| * padicNorm 2 (v.1 - v.2)) := by ring
    _ = _ := by rw [half_power_reciprocal, one_mul]

end CollatzRunyan.BinaryAdelicDuality
