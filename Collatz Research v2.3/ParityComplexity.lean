import Mathlib

/-!
# Collatz–Runyan: finite parity complexity

Standalone module, reusing the previously verified integer parity-prefix
arithmetic in a separate namespace. The new results concern finite sets
of distinct values. No convergence assumption is made. The analytic
asymptotic consequences are not formalized here.
-/

namespace CollatzRunyan.ParityComplexity

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

/-- Encode the first k parity bits, least significant bit first. -/
def parityCode : ℕ → ℤ → ℤ
  | 0, _ => 0
  | k + 1, n => n % 2 + 2 * parityCode k (shortcut n)

/-- Equality of codes implies equality of all corresponding parity bits. -/
theorem code_eq_implies_prefix (k : ℕ) (u v : ℤ)
    (h : parityCode k u = parityCode k v) : SameParityPrefix k u v := by
  induction k generalizing u v with
  | zero => trivial
  | succ k ih =>
    change u % 2 + 2 * parityCode k (shortcut u) =
      v % 2 + 2 * parityCode k (shortcut v) at h
    change u % 2 = v % 2 ∧ SameParityPrefix k (shortcut u) (shortcut v)
    have hb : u % 2 = v % 2 := by omega
    have ht : parityCode k (shortcut u) = parityCode k (shortcut v) := by omega
    exact ⟨hb, ih _ _ ht⟩

/-- Equal codes force the values to be congruent modulo 2^k. -/
theorem code_difference_dvd (k : ℕ) (u v : ℤ)
    (h : parityCode k u = parityCode k v) : (2 : ℤ) ^ k ∣ u - v := by
  exact prefix_difference_dvd k u v (code_eq_implies_prefix k u v h)

/-- On the interval [0, 2^k), the parity code is injective. -/
theorem code_collision_in_interval (k : ℕ) (u v : ℤ)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hu : u < (2 : ℤ) ^ k) (hv : v < (2 : ℤ) ^ k)
    (h : parityCode k u = parityCode k v) : u = v := by
  by_cases huv : v ≤ u
  · have hs : (u - v).natAbs < ((2 : ℤ) ^ k).natAbs :=
      Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) (by omega)
    exact prefix_collision_of_small_difference k u v
      (code_eq_implies_prefix k u v h) hs
  · have hs : (v - u).natAbs < ((2 : ℤ) ^ k).natAbs :=
      Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) (by omega)
    exact (prefix_collision_of_small_difference k v u
      (code_eq_implies_prefix k v u h.symm) hs).symm

/-- Every distinct value in the interval contributes a distinct code. -/
theorem finite_code_card (k : ℕ) (S : Finset ℤ)
    (hS : ∀ x ∈ S, 0 ≤ x ∧ x < (2 : ℤ) ^ k) :
    (S.image (parityCode k)).card = S.card := by
  apply Finset.card_image_of_injOn
  intro u hu v hv heq
  have hu' := hS u (by simpa using hu)
  have hv' := hS v (by simpa using hv)
  exact code_collision_in_interval k u v hu'.1 hv'.1 hu'.2 hv'.2 heq

/-- Count distinct codes at the first N starting positions of an orbit. -/
def finiteComplexity (k N : ℕ) (n : ℤ) : ℕ :=
  ((Finset.range N).image (fun j => parityCode k (orbit j n))).card

/-- If the first N orbit values are distinct and below 2^k,
    all N parity blocks are distinct. -/
theorem finite_orbit_complexity (k N : ℕ) (n : ℤ)
    (hinj : ∀ i j : ℕ, i < N → j < N → orbit i n = orbit j n → i = j)
    (hbound : ∀ i : ℕ, i < N → 0 ≤ orbit i n ∧ orbit i n < (2 : ℤ) ^ k) :
    finiteComplexity k N n = N := by
  unfold finiteComplexity
  have h : Set.InjOn (fun j : ℕ => parityCode k (orbit j n))
      (↑(Finset.range N) : Set ℕ) := by
    intro i hi j hj heq
    have hi' : i < N := by simpa using hi
    have hj' : j < N := by simpa using hj
    have hbi := hbound i hi'
    have hbj := hbound j hj'
    apply hinj i j hi' hj'
    exact code_collision_in_interval k (orbit i n) (orbit j n)
      hbi.1 hbj.1 hbi.2 hbj.2 heq
  rw [Finset.card_image_of_injOn h, Finset.card_range]

#print axioms code_eq_implies_prefix
#print axioms code_difference_dvd
#print axioms code_collision_in_interval
#print axioms finite_code_card
#print axioms finite_orbit_complexity

end CollatzRunyan.ParityComplexity
