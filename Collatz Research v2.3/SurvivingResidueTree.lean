import Mathlib

/-!
# Collatz–Runyan: surviving residue tree / first coefficient crossings
Standalone integer arithmetic. No universal stopping-time assumption.
The envelope bounds the additive term whenever all earlier prefix
coefficients are at least one. Its optimality and the Python numerical
search are separate from these theorem audits.
-/
namespace CollatzRunyan.SurvivingResidueTree

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

/-- Before a coefficient crossing, an odd step's position is bounded
by the binary logarithm of the current power of three. -/
theorem odd_position_bound (i a : ℕ) (h : (2 : ℕ) ^ i ≤ (3 : ℕ) ^ a) :
    i ≤ Nat.log2 ((3 : ℕ) ^ a) := by
  exact (Nat.le_log2 (by positivity : (3 : ℕ) ^ a ≠ 0)).2 h

/-- Translate the position bound into an integer offset bound. -/
theorem odd_weight_bound (i a : ℕ) (h : (2 : ℕ) ^ i ≤ (3 : ℕ) ^ a) :
    (2 : ℤ) ^ i ≤ (2 : ℤ) ^ Nat.log2 ((3 : ℕ) ^ a) := by
  exact pow_le_pow_right₀ (by norm_num) (odd_position_bound i a h)

/-- Bound the offset of an actual trajectory up to and including its
first coefficient crossing, with no assumption of eventual descent. -/
theorem offset_le_envelope (n : ℤ) (k : ℕ)
    (h : ∀ j : ℕ, j < k → (2 : ℕ) ^ j ≤ (3 : ℕ) ^ oddCount n j) :
    offset n k ≤ envelope (oddCount n k) := by
  induction k with
  | zero => simp [offset, oddCount, envelope]
  | succ k ih =>
    have hb := ih (fun j hj => h j (by omega))
    have hk := h k (by omega)
    by_cases he : orbit n k % 2 = 0
    · simpa only [offset, oddCount, if_pos he] using hb
    · simp only [offset, oddCount, if_neg he, envelope]
      exact add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num))
        (odd_weight_bound k (oddCount n k) hk)

/-- The exact cutoff in terms of the affine numerator. -/
theorem affine_nondescending_iff (M A B n y : ℤ) (hm : 0 < M)
    (hc : A < M) (ha : M * y = A * n + B) :
    n ≤ y ↔ n ≤ B / (M - A) := by
  have hd : 0 < M - A := by omega
  rw [Int.le_ediv_iff_mul_le hd]
  constructor
  · intro h
    have hh := mul_le_mul_of_nonneg_left h (le_of_lt hm)
    nlinarith only [ha, hh]
  · intro h
    by_contra hn
    have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hn) hm
    nlinarith only [ha, h, hh]

/-- At a first coefficient crossing, every failure of actual descent
is bounded above by the envelope divided by the coefficient gap. -/
theorem first_crossing_exception (n : ℤ) (k : ℕ)
    (hp : ∀ j : ℕ, j < k → (2 : ℕ) ^ j ≤ (3 : ℕ) ^ oddCount n j)
    (hc : (3 : ℤ) ^ oddCount n k < (2 : ℤ) ^ k)
    (hn : n ≤ orbit n k) :
    n ≤ envelope (oddCount n k) / ((2 : ℤ) ^ k - (3 : ℤ) ^ oddCount n k) := by
  have hd : 0 < (2 : ℤ) ^ k - (3 : ℤ) ^ oddCount n k := by omega
  have ha := affine_prefix n k
  have hb := offset_le_envelope n k hp
  have hm : 0 < (2 : ℤ) ^ k := by positivity
  have hh := mul_le_mul_of_nonneg_left hn (le_of_lt hm)
  apply (Int.le_ediv_iff_mul_le hd).2
  nlinarith only [ha, hb, hh]

/-- A first crossing above the exception cutoff necessarily descends. -/
theorem first_crossing_descent (n : ℤ) (k : ℕ)
    (hp : ∀ j : ℕ, j < k → (2 : ℕ) ^ j ≤ (3 : ℕ) ^ oddCount n j)
    (hc : (3 : ℤ) ^ oddCount n k < (2 : ℤ) ^ k)
    (hn : envelope (oddCount n k) / ((2 : ℤ) ^ k - (3 : ℤ) ^ oddCount n k) < n) :
    orbit n k < n := by
  by_contra h
  exact (not_le_of_gt hn) (first_crossing_exception n k hp hc (le_of_not_gt h))

#print axioms affine_prefix
#print axioms odd_position_bound
#print axioms odd_weight_bound
#print axioms offset_le_envelope
#print axioms affine_nondescending_iff
#print axioms first_crossing_exception
#print axioms first_crossing_descent

end CollatzRunyan.SurvivingResidueTree
