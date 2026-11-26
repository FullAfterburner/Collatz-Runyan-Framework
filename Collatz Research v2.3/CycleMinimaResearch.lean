import Mathlib

/-!
# Collatz–Runyan: local minima transition research
Exact odd/even run transitions and an integer-only 8/5 growth bound.
The chain lemma assumes positive local minima and the stated transition
inequalities. No logarithmic estimates or universal cycle exclusion are
asserted by this module.
-/
namespace CollatzRunyan.CycleMinimaResearch

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


theorem twice_shortcut_even (x : ℤ) (h : x % 2 = 0) :
    2 * shortcut x = x := by
  unfold shortcut
  rw [if_pos h]
  omega

theorem orbit_add (k l : ℕ) (n : ℤ) :
    orbit (k + l) n = orbit l (orbit k n) := by
  induction l with
  | zero => simp [orbit]
  | succ l ih =>
    change shortcut (orbit (k + l) n) = shortcut (orbit l (orbit k n))
    exact congrArg shortcut ih

theorem even_run_scale (k : ℕ) (n : ℤ)
    (heven : ∀ j : ℕ, j < k → orbit j n % 2 = 0) :
    (2 : ℤ)^k * orbit k n = n := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
    have hp := ih (fun j hj => heven j (by omega))
    have hs := twice_shortcut_even (orbit k n) (heven k (by omega))
    change (2 : ℤ)^(k+1) * shortcut (orbit k n) = n
    calc
      _ = (2 : ℤ)^k * (2 * shortcut (orbit k n)) := by rw [pow_succ]; ring
      _ = (2 : ℤ)^k * orbit k n := by rw [hs]
      _ = n := hp

/-- An actual odd run followed by an even run gives the compressed equation. -/
theorem local_minimum_transition (a b : ℕ) (m : ℤ)
    (hodd : ∀ j : ℕ, j < a → orbit j m % 2 ≠ 0)
    (heven : ∀ j : ℕ, j < b → orbit j (orbit a m) % 2 = 0) :
    (2 : ℤ)^(a+b) * orbit (a+b) m + (2 : ℤ)^a = 3^a * (m+1) := by
  have ho := odd_run_shift a m hodd
  have he := even_run_scale b (orbit a m) heven
  rw [← orbit_add a b m] at he
  calc
    _ = (2 : ℤ)^a * ((2 : ℤ)^b * orbit (a+b) m + 1) := by rw [pow_add]; ring
    _ = (2 : ℤ)^a * (orbit a m + 1) := by rw [he]
    _ = _ := ho

/-- Powers of two divide the starting value shifted by one. -/
theorem odd_run_core (a : ℕ) (m : ℤ)
    (hodd : ∀ j : ℕ, j < a → orbit j m % 2 ≠ 0) :
    (2 : ℤ)^a ∣ m+1 := by
  have h : IsCoprime (2 : ℤ) 3 := by
    refine ⟨-1, 1, ?_⟩
    norm_num
  have hp : IsCoprime ((2 : ℤ)^a) ((3 : ℤ)^a) := h.pow
  have hd : (2 : ℤ)^a ∣ (3 : ℤ)^a * (m+1) :=
    ⟨orbit a m + 1, (odd_run_shift a m hodd).symm⟩
  exact hp.dvd_of_dvd_mul_left hd

/-- A local minimum reached after a nonempty odd run is not divisible by 3. -/
theorem next_minimum_not_multiple_three (a b : ℕ) (u v : ℤ)
    (ha : 0 < a) (h : (2 : ℤ)^b * v + 1 = (3 : ℤ)^a * u) :
    ¬ (3 : ℤ) ∣ v := by
  intro hv
  obtain ⟨w, hw⟩ := hv
  cases a with
  | zero => omega
  | succ a =>
    rw [pow_succ, hw] at h
    have he : 3 * ((3 : ℤ)^a * u - (2 : ℤ)^b * w) = 1 := by
      linear_combination -h
    omega

/-- A rational-exponent surrogate for log₂(3) < 8/5. -/
theorem power_ratio_bound (a : ℕ) :
    ((3 : ℤ)^a)^5 ≤ ((2 : ℤ)^a)^8 := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    calc
      _ = ((3 : ℤ)^a)^5 * 243 := by rw [pow_succ (3 : ℤ) a, mul_pow] <;> norm_num
      _ ≤ ((2 : ℤ)^a)^8 * 243 := mul_le_mul_of_nonneg_right ih (by norm_num)
      _ ≤ ((2 : ℤ)^a)^8 * 256 := by
        exact mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
      _ = _ := by rw [pow_succ (2 : ℤ) a, mul_pow] <;> norm_num

/-- Integer-only local-minimum growth bound, with explicit compressed data. -/
theorem local_minimum_growth (a b : ℕ) (m v u : ℤ)
    (hv : 0 < v) (hu : 0 < u)
    (hm : m+1 = (2 : ℤ)^a * u)
    (h : (2 : ℤ)^b * v + 1 = (3 : ℤ)^a * u) :
    (v+1)^5 ≤ (m+1)^8 := by
  have hbpos : 0 < (2 : ℤ)^b := by positivity
  have hb : 1 ≤ (2 : ℤ)^b := by omega
  have hx : v+1 ≤ (3 : ℤ)^a * u := by
    have hh := mul_le_mul_of_nonneg_right hb (le_of_lt hv)
    linarith only [hh, h]
  have hu3pos : 0 < u^3 := by positivity
  have hu3 : 1 ≤ u^3 := by omega
  have hu58 : u^5 ≤ u^8 := by
    calc
      u^5 = u^5 * 1 := by ring
      _ ≤ u^5 * u^3 := mul_le_mul_of_nonneg_left hu3 (by positivity)
      _ = u^8 := by ring
  calc
    (v+1)^5 ≤ ((3 : ℤ)^a * u)^5 := by gcongr
    _ = ((3 : ℤ)^a)^5 * u^5 := by rw [mul_pow]
    _ ≤ ((2 : ℤ)^a)^8 * u^8 :=
      mul_le_mul (power_ratio_bound a) hu58 (by positivity) (by positivity)
    _ = (m+1)^8 := by rw [hm, mul_pow]

/-- Iterate the bound without real powers or logarithms. -/
theorem minima_chain_bound (m : ℕ → ℤ) (i : ℕ)
    (hpos : ∀ j, 0 < m j)
    (hstep : ∀ j, (m (j+1)+1)^5 ≤ (m j+1)^8) :
    (m i+1)^((5 : ℕ)^i) ≤ (m 0+1)^((8 : ℕ)^i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hp := hpos (i+1)
    have hpi := hpos i
    have h0 := hpos 0
    calc
      (m (i+1)+1)^((5 : ℕ)^(i+1)) = ((m (i+1)+1)^5)^((5 : ℕ)^i) := by
        rw [pow_succ, ← pow_mul, Nat.mul_comm 5 (5^i)]
      _ ≤ ((m i+1)^8)^((5 : ℕ)^i) := by
        have hs := hstep i
        gcongr
      _ = ((m i+1)^((5 : ℕ)^i))^8 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm 8 (5^i)]
      _ ≤ ((m 0+1)^((8 : ℕ)^i))^8 := by gcongr
      _ = (m 0+1)^((8 : ℕ)^(i+1)) := by rw [← pow_mul, pow_succ (8 : ℕ) i]

#print axioms even_run_scale
#print axioms local_minimum_transition
#print axioms odd_run_core
#print axioms next_minimum_not_multiple_three
#print axioms power_ratio_bound
#print axioms local_minimum_growth
#print axioms minima_chain_bound

end CollatzRunyan.CycleMinimaResearch
