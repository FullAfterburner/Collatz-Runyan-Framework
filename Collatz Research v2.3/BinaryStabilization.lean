import Mathlib

/-!
# Collatz–Runyan: binary stabilization
Standalone arithmetic layer. The forward prefix lemmas are copied from the
previously audited ParityComplexity module. The new results prove the reverse
congruence, canonical residue reconstruction, lifting, and finite stabilization.
No universal descent assertion is made.
-/

namespace CollatzRunyan.BinaryStabilization

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

/-- Congruence modulo 2^k forces the same k parity bits. -/
theorem dvd_implies_prefix (k : ℕ) (u v : ℤ)
    (h : (2 : ℤ) ^ k ∣ u - v) : SameParityPrefix k u v := by
  induction k generalizing u v with
  | zero => trivial
  | succ k ih =>
    obtain ⟨z, hz⟩ := h
    have he : u - v = 2 * ((2 : ℤ) ^ k * z) := by
      calc
        u - v = (2 : ℤ) ^ (k + 1) * z := hz
        _ = _ := by rw [pow_succ]; ring
    have hb : u % 2 = v % 2 := by omega
    change u % 2 = v % 2 ∧ SameParityPrefix k (shortcut u) (shortcut v)
    refine ⟨hb, ih _ _ ?_⟩
    by_cases hu : u % 2 = 0
    · have hv : v % 2 = 0 := hb.symm.trans hu
      have hu' := two_mul_shortcut_even u hu
      have hv' := two_mul_shortcut_even v hv
      refine ⟨z, ?_⟩
      omega
    · have hv : v % 2 ≠ 0 := by
        intro hv
        exact hu (hb.trans hv)
      have hu' := two_mul_shortcut_odd u hu
      have hv' := two_mul_shortcut_odd v hv
      refine ⟨3 * z, ?_⟩
      have hm : (2 : ℤ) ^ k * (3 * z) = 3 * ((2 : ℤ) ^ k * z) := by ring
      omega

theorem prefix_iff_dvd (k : ℕ) (u v : ℤ) :
    SameParityPrefix k u v ↔ (2 : ℤ) ^ k ∣ u - v :=
  ⟨prefix_difference_dvd k u v, dvd_implies_prefix k u v⟩

theorem prefix_implies_code_eq (k : ℕ) (u v : ℤ)
    (h : SameParityPrefix k u v) : parityCode k u = parityCode k v := by
  induction k generalizing u v with
  | zero => rfl
  | succ k ih =>
    change u % 2 = v % 2 ∧ SameParityPrefix k (shortcut u) (shortcut v) at h
    change u % 2 + 2 * parityCode k (shortcut u) =
      v % 2 + 2 * parityCode k (shortcut v)
    rw [h.1, ih _ _ h.2]

theorem code_eq_iff_dvd (k : ℕ) (u v : ℤ) :
    parityCode k u = parityCode k v ↔ (2 : ℤ) ^ k ∣ u - v := by
  exact ⟨code_difference_dvd k u v,
    fun h => prefix_implies_code_eq k u v (dvd_implies_prefix k u v h)⟩

/-- The least nonnegative representative of the parity-prefix class. -/
def residue (k : ℕ) (n : ℤ) : ℤ := n % ((2 : ℤ) ^ k)

theorem residue_bounds (k : ℕ) (n : ℤ) :
    0 ≤ residue k n ∧ residue k n < (2 : ℤ) ^ k := by
  have hp : 0 < (2 : ℤ) ^ k := by positivity
  exact ⟨Int.emod_nonneg n (ne_of_gt hp), Int.emod_lt_of_pos n hp⟩

theorem residue_same_code (k : ℕ) (n : ℤ) :
    parityCode k n = parityCode k (residue k n) := by
  apply (code_eq_iff_dvd k n (residue k n)).2
  refine ⟨n / ((2 : ℤ) ^ k), ?_⟩
  unfold residue
  have he := Int.emod_def n ((2 : ℤ) ^ k)
  omega

theorem residue_unique (k : ℕ) (n r : ℤ)
    (hr0 : 0 ≤ r) (hr : r < (2 : ℤ) ^ k)
    (hc : parityCode k r = parityCode k n) : r = residue k n := by
  have hb := residue_bounds k n
  exact code_collision_in_interval k r (residue k n) hr0 hb.1 hr hb.2
    (hc.trans (residue_same_code k n))

/-- Every additional parity bit either preserves the representative or
    adds one copy of the old modulus. -/
theorem residue_lift (k : ℕ) (n : ℤ) :
    residue (k + 1) n = residue k n ∨
    residue (k + 1) n = residue k n + (2 : ℤ) ^ k := by
  have hd : (2 : ℤ) ^ k ∣ (2 : ℤ) ^ (k + 1) := by
    exact ⟨2, by rw [pow_succ]⟩
  have he : residue (k + 1) n % ((2 : ℤ) ^ k) = residue k n := by
    exact Int.emod_emod_of_dvd n hd
  have hb := residue_bounds (k + 1) n
  rw [pow_succ] at hb
  by_cases hs : residue (k + 1) n < (2 : ℤ) ^ k
  · left
    rw [Int.emod_eq_of_lt hb.1 hs] at he
    exact he
  · right
    have h0 : 0 ≤ residue (k + 1) n - (2 : ℤ) ^ k := by omega
    have h1 : residue (k + 1) n - (2 : ℤ) ^ k < (2 : ℤ) ^ k := by omega
    have hmod : (residue (k + 1) n - (2 : ℤ) ^ k) % ((2 : ℤ) ^ k) =
        residue (k + 1) n % ((2 : ℤ) ^ k) := by
      rw [Int.sub_emod]
      simp
    rw [Int.emod_eq_of_lt h0 h1, he] at hmod
    omega

/-- Stabilization holds as soon as the modulus exceeds a nonnegative n. -/
theorem residue_stabilizes_at (k : ℕ) (n : ℤ) (hn : 0 ≤ n)
    (hb : n < (2 : ℤ) ^ k) : residue k n = n :=
  Int.emod_eq_of_lt hn hb

theorem residue_stabilizes_from (K : ℕ) (n : ℤ) (hn : 0 ≤ n)
    (hb : n < (2 : ℤ) ^ K) : ∀ k : ℕ, K ≤ k → residue k n = n := by
  intro k hk
  apply residue_stabilizes_at k n hn
  exact lt_of_lt_of_le hb (pow_le_pow_right₀ (by norm_num) hk)

#print axioms dvd_implies_prefix
#print axioms prefix_iff_dvd
#print axioms code_eq_iff_dvd
#print axioms residue_same_code
#print axioms residue_unique
#print axioms residue_lift
#print axioms residue_stabilizes_from

end CollatzRunyan.BinaryStabilization
