import Mathlib

/-!
# Collatz–Runyan: global parity rigidity

Standalone integer arithmetic model of the shortcut map. On nonnegative
integers it agrees with the usual shortcut Collatz map. The orbit is
iterated with the first step taken before the recursive call.

This module proves a collision criterion for matching finite parity
prefixes and a universal upper growth bound. It does NOT assert Collatz
convergence or exclusion of nontrivial cycles.
-/

namespace CollatzRunyan.GlobalParity

def shortcut (n : ℤ) : ℤ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

def orbit : ℕ → ℤ → ℤ
  | 0, n => n
  | k + 1, n => orbit k (shortcut n)

def SameParityPrefix : ℕ → ℤ → ℤ → Prop
  | 0, _, _ => True
  | k + 1, u, v =>
      u % 2 = v % 2 ∧ SameParityPrefix k (shortcut u) (shortcut v)

theorem two_mul_shortcut_even (n : ℤ) (h : n % 2 = 0) :
    2 * shortcut n = n := by
  unfold shortcut
  rw [if_pos h]
  omega

theorem two_mul_shortcut_odd (n : ℤ) (h : n % 2 ≠ 0) :
    2 * shortcut n = 3 * n + 1 := by
  unfold shortcut
  rw [if_neg h]
  omega

theorem prefix_affine_difference (k : ℕ) (u v : ℤ)
    (h : SameParityPrefix k u v) :
    ∃ a : ℕ, (2 : ℤ) ^ k * (orbit k u - orbit k v) =
      (3 : ℤ) ^ a * (u - v) := by
  induction k generalizing u v with
  | zero => exact ⟨0, by simp [orbit]⟩
  | succ k ih =>
    change u % 2 = v % 2 ∧ SameParityPrefix k (shortcut u) (shortcut v) at h
    obtain ⟨a, ha⟩ := ih (shortcut u) (shortcut v) h.2
    by_cases hu : u % 2 = 0
    · have hv : v % 2 = 0 := h.1.symm.trans hu
      have hs : 2 * (shortcut u - shortcut v) = u - v := by
        have he := two_mul_shortcut_even u hu
        have hf := two_mul_shortcut_even v hv
        omega
      refine ⟨a, ?_⟩
      change (2 : ℤ) ^ (k + 1) *
        (orbit k (shortcut u) - orbit k (shortcut v)) = _
      calc
        _ = 2 * ((2 : ℤ) ^ k *
            (orbit k (shortcut u) - orbit k (shortcut v))) := by
              rw [pow_succ]; ring
        _ = 2 * ((3 : ℤ) ^ a * (shortcut u - shortcut v)) := by rw [ha]
        _ = (3 : ℤ) ^ a * (2 * (shortcut u - shortcut v)) := by ring
        _ = _ := by rw [hs]
    · have hv : v % 2 ≠ 0 := by
        intro hz
        exact hu (h.1.trans hz)
      have hs : 2 * (shortcut u - shortcut v) = 3 * (u - v) := by
        have he := two_mul_shortcut_odd u hu
        have hf := two_mul_shortcut_odd v hv
        omega
      refine ⟨a + 1, ?_⟩
      change (2 : ℤ) ^ (k + 1) *
        (orbit k (shortcut u) - orbit k (shortcut v)) = _
      calc
        _ = 2 * ((2 : ℤ) ^ k *
            (orbit k (shortcut u) - orbit k (shortcut v))) := by
              rw [pow_succ]; ring
        _ = 2 * ((3 : ℤ) ^ a * (shortcut u - shortcut v)) := by rw [ha]
        _ = (3 : ℤ) ^ a * (2 * (shortcut u - shortcut v)) := by ring
        _ = (3 : ℤ) ^ a * (3 * (u - v)) := by rw [hs]
        _ = _ := by rw [pow_succ]; ring

theorem prefix_difference_dvd (k : ℕ) (u v : ℤ)
    (h : SameParityPrefix k u v) : (2 : ℤ) ^ k ∣ u - v := by
  obtain ⟨a, ha⟩ := prefix_affine_difference k u v h
  have hc : IsCoprime (2 : ℤ) 3 := by
    refine ⟨-1, 1, ?_⟩
    norm_num
  have hp : IsCoprime ((2 : ℤ) ^ k) ((3 : ℤ) ^ a) := hc.pow
  have hd : (2 : ℤ) ^ k ∣ (3 : ℤ) ^ a * (u - v) :=
    ⟨orbit k u - orbit k v, ha.symm⟩
  exact hp.dvd_of_dvd_mul_left hd

theorem prefix_collision_of_small_difference (k : ℕ) (u v : ℤ)
    (h : SameParityPrefix k u v)
    (hsmall : (u - v).natAbs < ((2 : ℤ) ^ k).natAbs) : u = v := by
  by_contra hne
  have hd : u - v ≠ 0 := by omega
  have hle := Int.natAbs_le_of_dvd_ne_zero (prefix_difference_dvd k u v h) hd
  exact (not_lt_of_ge hle) hsmall

theorem shortcut_nonneg (n : ℤ) (hn : 0 ≤ n) : 0 ≤ shortcut n := by
  by_cases h : n % 2 = 0
  · have he := two_mul_shortcut_even n h
    omega
  · have ho := two_mul_shortcut_odd n h
    omega

theorem shortcut_growth (n : ℤ) (hn : 0 ≤ n) :
    2 * (shortcut n + 1) ≤ 3 * (n + 1) := by
  by_cases h : n % 2 = 0
  · have he := two_mul_shortcut_even n h
    omega
  · have ho := two_mul_shortcut_odd n h
    omega

theorem orbit_growth (k : ℕ) (n : ℤ) (hn : 0 ≤ n) :
    (2 : ℤ) ^ k * (orbit k n + 1) ≤ (3 : ℤ) ^ k * (n + 1) := by
  induction k generalizing n with
  | zero => simp [orbit]
  | succ k ih =>
    have hi := ih (shortcut n) (shortcut_nonneg n hn)
    have hs := shortcut_growth n hn
    change (2 : ℤ) ^ (k + 1) * (orbit k (shortcut n) + 1) ≤ _
    calc
      _ = 2 * ((2 : ℤ) ^ k * (orbit k (shortcut n) + 1)) := by
        rw [pow_succ]; ring
      _ ≤ 2 * ((3 : ℤ) ^ k * (shortcut n + 1)) :=
        mul_le_mul_of_nonneg_left hi (by norm_num)
      _ = (3 : ℤ) ^ k * (2 * (shortcut n + 1)) := by ring
      _ ≤ (3 : ℤ) ^ k * (3 * (n + 1)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [pow_succ]; ring

#print axioms prefix_affine_difference
#print axioms prefix_difference_dvd
#print axioms prefix_collision_of_small_difference
#print axioms shortcut_growth
#print axioms orbit_growth

end CollatzRunyan.GlobalParity
