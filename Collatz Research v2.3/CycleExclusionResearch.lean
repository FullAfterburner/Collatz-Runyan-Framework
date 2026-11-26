import Mathlib

/-!
# Collatz–Runyan: cycle exclusion research

Standalone arithmetic for odd-run telescoping and a conditional grid bound.
The logarithmic cycle identity, aggregation over maximal odd runs,
certified logarithm approximation, and external finite verification are
not formalized here. In particular, this file does not exclude all cycles.
-/
namespace CollatzRunyan.CycleExclusionResearch

def shortcut (x : ℤ) : ℤ :=
  if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

def orbit (k : ℕ) (n : ℤ) : ℤ :=
  match k with
  | 0 => n
  | j + 1 => shortcut (orbit j n)

theorem twice_shortcut_odd (x : ℤ) (h : x % 2 ≠ 0) :
    2 * shortcut x = 3 * x + 1 := by
  unfold shortcut
  rw [if_neg h]
  omega

/-- A positive minimum of a forward-invariant cycle cannot be even. -/
theorem cycle_min_odd (m : ℤ) (hm : 0 < m)
    (hmin : m ≤ shortcut m) : m % 2 ≠ 0 := by
  intro h
  have he : 2 * shortcut m = m := by
    unfold shortcut
    rw [if_pos h]
    omega
  linarith only [hm, hmin, he]

/-- The cross-multiplied one-step telescoping identity. -/
theorem odd_step_telescope (x : ℤ) (h : x % 2 ≠ 0) :
    (3 * x + 1) * (shortcut x + 1) =
      3 * (x + 1) * shortcut x := by
  have hs := twice_shortcut_odd x h
  nlinarith only [hs]

/-- The exact shifted affine formula for a consecutive odd run. -/
theorem odd_run_shift (k : ℕ) (n : ℤ)
    (hodd : ∀ j : ℕ, j < k → orbit j n % 2 ≠ 0) :
    (2 : ℤ)^k * (orbit k n + 1) = 3^k * (n + 1) := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
    have hp := ih (fun j hj => hodd j (by omega))
    have hs := twice_shortcut_odd (orbit k n) (hodd k (by omega))
    have hshift : 2 * (shortcut (orbit k n) + 1) =
        3 * (orbit k n + 1) := by linarith only [hs]
    change (2 : ℤ)^(k+1) * (shortcut (orbit k n) + 1) =
      3^(k+1) * (n + 1)
    calc
      _ = (2 : ℤ)^k * (2 * (shortcut (orbit k n) + 1)) := by
        rw [pow_succ]; ring
      _ = (2 : ℤ)^k * (3 * (orbit k n + 1)) := by rw [hshift]
      _ = 3 * ((2 : ℤ)^k * (orbit k n + 1)) := by ring
      _ = 3 * (3^k * (n + 1)) := by rw [hp]
      _ = _ := by rw [pow_succ]; ring

/-- Cross-multiplied strict endpoint factor bound for a positive odd run. -/
theorem run_endpoint_bound (u v : ℤ) (hu : 0 < u) :
    (u + 1) * v < (u + 1) * (v + 1) := by
  nlinarith only [hu]

/-- Bezout identity for the upper rational approximation p/q to log_2 3. -/
theorem grid_identity (k a : ℤ) :
    5409303924479 * (753110839881 * k - 1193652440098 * a) =
      a + 753110839881 * (5409303924479 * k - 8573543875303 * a) := by
  ring

set_option maxHeartbeats 2000000 in
/-- With at most 10^12 odd steps, a nonnegative grid coordinate is at least 6. -/
theorem grid_at_least_six (k a z : ℤ)
    (ha : 0 < a) (hcap : a ≤ 1000000000000) (hz : 0 ≤ z)
    (he : z = 5409303924479 * k - 8573543875303 * a) :
    6 ≤ z := by
  let w : ℤ := 753110839881 * k - 1193652440098 * a
  have hw : 5409303924479 * w = a + 753110839881 * z := by
    dsimp [w]
    rw [he]
    exact grid_identity k a
  clear_value w
  have hwpos : 0 < w := by linarith only [hw, ha, hz]
  have hw1 : 1 ≤ w := by
    clear hw he ha hcap hz
    omega
  by_contra hbad
  have hz5 : z ≤ 5 := by
    clear hw he ha hcap hz hwpos hw1
    omega
  linarith only [hw, hw1, hcap, hz5]

set_option maxHeartbeats 2000000 in
/-- Conditional numerical lower bound on odd runs. The normalized gap
inequality is an explicit hypothesis, not a custom axiom. -/
theorem cycle_run_count_bound (m k a r z : ℤ)
    (hm : 2361183241434822606848 ≤ m)
    (ha : 0 < a) (hcap : a ≤ 1000000000000) (hz : 0 ≤ z)
    (he : z = 5409303924479 * k - 8573543875303 * a)
    (hgap : 2 * m * z < 3 * 5409303924479 * r) :
    1746016327 ≤ r := by
  have hz6 := grid_at_least_six k a z ha hcap hz he
  have hm0 : 0 ≤ m := by linarith only [hm]
  have hmz : 6 * m ≤ m * z := by
    calc
      6 * m = m * 6 := by ring
      _ ≤ m * z := mul_le_mul_of_nonneg_left hz6 hm0
  have hs : 12 * m < 3 * 5409303924479 * r := by
    linarith only [hmz, hgap]
  by_contra hbad
  have hr : r ≤ 1746016326 := by
    clear hm ha hcap hz he hgap hz6 hm0 hmz hs
    omega
  linarith only [hm, hs, hr]

#print axioms cycle_min_odd
#print axioms odd_step_telescope
#print axioms odd_run_shift
#print axioms run_endpoint_bound
#print axioms grid_identity
#print axioms grid_at_least_six
#print axioms cycle_run_count_bound

end CollatzRunyan.CycleExclusionResearch
