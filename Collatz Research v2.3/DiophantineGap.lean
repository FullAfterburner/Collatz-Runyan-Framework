import Mathlib

/-!
# Collatz–Runyan: Diophantine gap arithmetic
Standalone integer/rational layer. No convergence assumption.
The logarithm interval certificate is separate (diophantine_gap_check.py).
The rational grid theorem explicitly takes its approximation hypotheses;
no analytic estimate or computational convergence bound is postulated here.
-/
namespace CollatzRunyan.DiophantineGap

def shortcut (n : ℤ) : ℤ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

def orbit (n : ℤ) : ℕ → ℤ
  | 0 => n
  | k + 1 => shortcut (orbit n k)

def oddCount (n : ℤ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if orbit n k % 2 = 0 then oddCount n k else oddCount n k + 1

def offset (n : ℤ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => if orbit n k % 2 = 0 then offset n k
      else 3 * offset n k + (2 : ℤ) ^ k

/-- Maximum allowed additive contribution for a given number of odd steps. -/
def envelope : ℕ → ℤ
  | 0 => 0
  | a + 1 => 3 * envelope a + (2 : ℤ) ^ Nat.log2 ((3 : ℕ) ^ a)

theorem twice_shortcut_even (n : ℤ) (h : n % 2 = 0) :
    2 * shortcut n = n := by
  unfold shortcut
  rw [if_pos h]
  omega

theorem twice_shortcut_odd (n : ℤ) (h : n % 2 ≠ 0) :
    2 * shortcut n = 3 * n + 1 := by
  unfold shortcut
  rw [if_neg h]
  omega

/-- The exact affine identity, with chronological prefix coefficients. -/
theorem affine_prefix (n : ℤ) (k : ℕ) :
    (2 : ℤ) ^ k * orbit n k = (3 : ℤ) ^ oddCount n k * n + offset n k := by
  induction k with
  | zero => simp [orbit, oddCount, offset]
  | succ k ih =>
    by_cases h : orbit n k % 2 = 0
    · simp only [orbit, oddCount, offset, if_pos h]
      calc
        _ = (2 : ℤ) ^ k * (2 * shortcut (orbit n k)) := by rw [pow_succ]; ring
        _ = (2 : ℤ) ^ k * orbit n k := by rw [twice_shortcut_even _ h]
        _ = _ := ih
    · simp only [orbit, oddCount, offset, if_neg h]
      calc
        _ = (2 : ℤ) ^ k * (2 * shortcut (orbit n k)) := by rw [pow_succ]; ring
        _ = (2 : ℤ) ^ k * (3 * orbit n k + 1) := by rw [twice_shortcut_odd _ h]
        _ = 3 * ((2 : ℤ) ^ k * orbit n k) + (2 : ℤ) ^ k := by ring
        _ = 3 * ((3 : ℤ) ^ oddCount n k * n + offset n k) + (2 : ℤ) ^ k := by rw [ih]
        _ = _ := by rw [pow_succ]; ring

/-- Linear bound for the normalized offset before the first coefficient crossing. -/
theorem offset_linear_bound (n : ℤ) (k : ℕ)
    (h : ∀ j : ℕ, j < k → (2 : ℕ) ^ j ≤ (3 : ℕ) ^ oddCount n j) :
    3 * offset n k ≤ (oddCount n k : ℤ) * (3 : ℤ) ^ oddCount n k := by
  induction k with
  | zero => simp [offset, oddCount]
  | succ k ih =>
    have hb := ih (fun j hj => h j (by omega))
    have hkN := h k (by omega)
    have hk : (2 : ℤ) ^ k ≤ (3 : ℤ) ^ oddCount n k := by
      exact_mod_cast hkN
    by_cases he : orbit n k % 2 = 0
    · simpa only [offset, oddCount, if_pos he] using hb
    · simp only [offset, oddCount, if_neg he, Nat.cast_add, Nat.cast_one, pow_succ]
      calc
        3 * (3 * offset n k + (2 : ℤ) ^ k) =
            3 * (3 * offset n k) + 3 * (2 : ℤ) ^ k := by ring
        _ ≤ 3 * ((oddCount n k : ℤ) * (3 : ℤ) ^ oddCount n k) +
            3 * (3 : ℤ) ^ oddCount n k :=
          add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num))
            (mul_le_mul_of_nonneg_left hk (by norm_num))
        _ = _ := by ring

/-- A nondescending prefix whose previous coefficients were at least one
must satisfy this necessary integer gap inequality. -/
theorem first_crossing_gap (n : ℤ) (k : ℕ)
    (hp : ∀ j : ℕ, j < k → (2 : ℕ) ^ j ≤ (3 : ℕ) ^ oddCount n j)
    (hn : n ≤ orbit n k) :
    3 * ((2 : ℤ) ^ k - (3 : ℤ) ^ oddCount n k) * n ≤
      (oddCount n k : ℤ) * (3 : ℤ) ^ oddCount n k := by
  have ha := affine_prefix n k
  have hb := offset_linear_bound n k hp
  have hh := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (2 : ℤ) ^ k)
  nlinarith only [ha, hb, hh]

/-- Integer descent certificate using the coefficient gap. -/
theorem gap_descent (n : ℤ) (k : ℕ)
    (hp : ∀ j : ℕ, j < k → (2 : ℕ) ^ j ≤ (3 : ℕ) ^ oddCount n j)
    (hg : (oddCount n k : ℤ) * (3 : ℤ) ^ oddCount n k <
      3 * ((2 : ℤ) ^ k - (3 : ℤ) ^ oddCount n k) * n) :
    orbit n k < n := by
  by_contra h
  exact (not_lt_of_ge (first_crossing_gap n k hp (le_of_not_gt h))) hg

/-- A rational grid separation lemma. The approximation error is positive
and smaller than one grid unit; a nonzero integer grid coordinate then
forces the positive gap to exceed one grid unit. -/
theorem rational_grid (z : ℤ) (q gap err : ℚ)
    (hq : 0 < q) (hg : 0 < gap) (he : 0 < err)
    (hsmall : q * err < 1) (hz : (z : ℚ) = q * (gap - err))
    (hne : z ≠ 0) : 1 < q * gap := by
  have hp := mul_pos hq hg
  have hm := mul_pos hq he
  have hb : (-1 : ℚ) < (z : ℚ) := by
    nlinarith only [hp, hsmall, hz]
  have hi : (-1 : ℤ) < z := by exact_mod_cast hb
  have h1 : (1 : ℤ) ≤ z := by omega
  have h1q : (1 : ℚ) ≤ (z : ℚ) := by exact_mod_cast h1
  nlinarith only [h1q, hm, hz]

set_option maxHeartbeats 2000000 in
/-- The particular rational grid cannot have a zero coordinate for
positive a smaller than its denominator. Bezout identity is explicit. -/
theorem fixed_grid_nonzero (k a : ℤ) (ha : 0 < a)
    (hb : a < 137528045312) :
    137528045312 * k ≠ 217976794617 * a := by
  intro h
  let z : ℤ := 65470613321 * k - 103768467013 * a
  have he : a = 137528045312 * z := by
    dsimp [z]
    linarith only [h]
  clear_value z
  by_cases hz : z ≤ 0
  · have hn := mul_nonpos_of_nonneg_of_nonpos
      (by norm_num : (0 : ℤ) ≤ 137528045312) hz
    linarith only [ha, he, hn]
  · have hz1 : 1 ≤ z := by
      clear h he ha hb
      omega
    have hh := mul_le_mul_of_nonneg_left hz1
      (by norm_num : (0 : ℤ) ≤ 137528045312)
    linarith only [hb, he, hh]

/-- Exact integer comparison with the published 2^71 verification range.
This arithmetic inequality does not assert convergence below that range. -/
theorem fifty_billion_cap (a : ℤ) (ha : a ≤ 33333333333) :
    a * 137528045312 < 2 * (2 : ℤ) ^ 71 := by
  have hh := mul_le_mul_of_nonneg_right ha
    (by norm_num : (0 : ℤ) ≤ 137528045312)
  norm_num at hh ⊢
  omega

#print axioms offset_linear_bound
#print axioms first_crossing_gap
#print axioms gap_descent
#print axioms rational_grid
#print axioms fixed_grid_nonzero
#print axioms fifty_billion_cap

end CollatzRunyan.DiophantineGap
