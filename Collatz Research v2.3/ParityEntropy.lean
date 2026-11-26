import Mathlib

/-!
# Collatz–Runyan: local parity frequency
Standalone integer arithmetic. The entropy counting corollary is not
formalized in this file. No convergence assumption or custom axiom.
-/
namespace CollatzRunyan.ParityEntropy

def shortcut (x : ℤ) : ℤ :=
  if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

def orbit (k : ℕ) (n : ℤ) : ℤ :=
  match k with
  | 0 => n
  | j + 1 => shortcut (orbit j n)

def bit (x : ℤ) : ℕ := if x % 2 = 0 then 0 else 1

def oddCount (k : ℕ) (n : ℤ) : ℕ :=
  match k with
  | 0 => 0
  | j + 1 => oddCount j n + bit (orbit j n)

theorem twice_shortcut_even (x : ℤ) (h : x % 2 = 0) :
    2 * shortcut x = x := by
  unfold shortcut
  rw [if_pos h]
  omega

theorem twice_shortcut_odd (x : ℤ) (h : x % 2 ≠ 0) :
    2 * shortcut x = 3 * x + 1 := by
  unfold shortcut
  rw [if_neg h]
  omega

/-- A strictly contracting cubic bound for an odd step above 5. -/
theorem odd_cube_strict (x : ℤ) (hx : 6 ≤ x) (h : x % 2 ≠ 0) :
    (2 : ℤ) ^ 3 * shortcut x ^ 3 < (2 : ℤ) ^ 5 * x ^ 3 := by
  have hs := twice_shortcut_odd x h
  have hlin : 12 * shortcut x ≤ 19 * x := by omega
  have hnonneg : 0 ≤ 12 * shortcut x := by omega
  have hcube : (12 * shortcut x) ^ 3 ≤ (19 * x) ^ 3 := by
    gcongr
  have hxpos : 0 < x := by omega
  have hx3 : 0 < x ^ 3 := by positivity
  norm_num at hcube ⊢
  nlinarith

/-- Every step above 5 satisfies an integer weighted growth bound. -/
theorem step_cube_bound (x : ℤ) (hx : 6 ≤ x) :
    (2 : ℤ) ^ 3 * shortcut x ^ 3 ≤
      (2 : ℤ) ^ (5 * bit x) * x ^ 3 := by
  by_cases h : x % 2 = 0
  · have he := twice_shortcut_even x h
    have hc : 8 * shortcut x ^ 3 = x ^ 3 := by
      calc
        8 * shortcut x ^ 3 =
            (2 * shortcut x) ^ 3 := by ring
        _ = x ^ 3 := by rw [he]
    simpa [bit, h] using hc.le
  · simpa [bit, h] using (odd_cube_strict x hx h).le

/-- A finite integer substitute for the logarithmic growth inequality. -/
theorem weighted_growth (k : ℕ) (n : ℤ)
    (hfloor : ∀ j : ℕ, j < k → 6 ≤ orbit j n) :
    (2 : ℤ) ^ (3 * k) * orbit k n ^ 3 ≤
      (2 : ℤ) ^ (5 * oddCount k n) * n ^ 3 := by
  induction k with
  | zero => simp [orbit, oddCount]
  | succ k ih =>
    have hp := ih (fun j hj => hfloor j (by omega))
    have hs := step_cube_bound (orbit k n) (hfloor k (by omega))
    have hpos : 0 ≤ (2 : ℤ) ^ (3 * k) := by positivity
    have hpos' : 0 ≤ (2 : ℤ) ^ (5 * bit (orbit k n)) := by positivity
    change (2 : ℤ) ^ (3 * (k + 1)) * shortcut (orbit k n) ^ 3 ≤
      (2 : ℤ) ^ (5 * (oddCount k n + bit (orbit k n))) * n ^ 3
    calc
      _ = (2 : ℤ) ^ (3 * k) * ((2 : ℤ) ^ 3 * shortcut (orbit k n) ^ 3) := by
        rw [show 3 * (k + 1) = 3 * k + 3 by omega, pow_add]
        ring
      _ ≤ (2 : ℤ) ^ (3 * k) * ((2 : ℤ) ^ (5 * bit (orbit k n)) * orbit k n ^ 3) :=
        mul_le_mul_of_nonneg_left hs hpos
      _ = (2 : ℤ) ^ (5 * bit (orbit k n)) * ((2 : ℤ) ^ (3 * k) * orbit k n ^ 3) := by ring
      _ ≤ (2 : ℤ) ^ (5 * bit (orbit k n)) * ((2 : ℤ) ^ (5 * oddCount k n) * n ^ 3) :=
        mul_le_mul_of_nonneg_left hp hpos'
      _ = _ := by
        rw [Nat.mul_add, pow_add]
        ring

/-- A non-descending segment starting at least at 6 has odd density ≥ 3/5.
    The strict version in the mathematical derivation additionally uses
    the strict odd-step inequality and the existence of an odd step. -/
theorem nondescending_odd_count (k : ℕ) (n : ℤ) (hn : 6 ≤ n)
    (hstay : ∀ j : ℕ, j ≤ k → n ≤ orbit j n) :
    3 * k ≤ 5 * oddCount k n := by
  have h := weighted_growth k n (fun j hj => le_trans hn (hstay j (by omega)))
  have hn0 : 0 ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hn3 : 0 < n ^ 3 := by positivity
  have hlast : n ≤ orbit k n := hstay k (by omega)
  have hc : n ^ 3 ≤ orbit k n ^ 3 := by gcongr
  have hpos : 0 ≤ (2 : ℤ) ^ (3 * k) := by positivity
  have hh := le_trans (mul_le_mul_of_nonneg_left hc hpos) h
  by_contra hbad
  have hlt : 5 * oddCount k n < 3 * k := by omega
  have hp : (2 : ℤ) ^ (5 * oddCount k n) < (2 : ℤ) ^ (3 * k) := by
    exact pow_lt_pow_right₀ (by norm_num) hlt
  have hcontra := mul_lt_mul_of_pos_right hp hn3
  exact (not_lt_of_ge hh) hcontra

#print axioms odd_cube_strict
#print axioms step_cube_bound
#print axioms weighted_growth
#print axioms nondescending_odd_count

end CollatzRunyan.ParityEntropy
