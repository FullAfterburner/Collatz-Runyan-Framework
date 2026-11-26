import BinaryAdelicDuality

/-! Two-place magnitude identities for affine Collatz normalization.
The exponent is supplied explicitly; no termination hypothesis is assumed. -/
namespace CollatzRunyan.CollatzAdelicCompatibility
open CollatzRunyan.BinaryAdelicDuality
open CollatzRunyan.BinarySpectralIteration

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def height (x : ℚ) : ℚ := |x| * padicNorm 2 x

def normalized (n : ℚ) (k : ℕ) : ℚ := (1/2 : ℚ)^k * (3*n+1)

theorem height_mul (x y : ℚ) : height (x*y) = height x * height y := by
  unfold height
  rw [abs_mul, padicNorm.mul]
  ring

theorem height_binary (k : ℕ) : height ((1/2 : ℚ)^k) = 1 :=
  half_power_duality k

theorem height_normalize (x : ℚ) (k : ℕ) :
    height ((1/2 : ℚ)^k * x) = height x := by
  rw [height_mul, height_binary, one_mul]

theorem collatz_height (n : ℚ) (k : ℕ) :
    height (normalized n k) = height (3*n+1) := by
  exact height_normalize (3*n+1) k

theorem collatz_abs (n : ℚ) (k : ℕ) :
    |normalized n k| = (1/2 : ℚ)^k * |3*n+1| := by
  rw [normalized, abs_mul, half_power_abs]

theorem collatz_padic (n : ℚ) (k : ℕ) :
    padicNorm 2 (normalized n k) = (2 : ℚ)^k * padicNorm 2 (3*n+1) := by
  rw [normalized, padicNorm.mul, half_power_norm]

theorem normalized_of_factor (n m : ℚ) (k : ℕ)
    (h : 3*n+1 = (2 : ℚ)^k * m) : normalized n k = m := by
  unfold normalized
  rw [h, ← mul_assoc, half_power_reciprocal, one_mul]

theorem collatz_factor_height (n m : ℚ) (k : ℕ)
    (h : 3*n+1 = (2 : ℚ)^k * m) : height m = height (3*n+1) := by
  rw [← normalized_of_factor n m k h]
  exact collatz_height n k

end CollatzRunyan.CollatzAdelicCompatibility
