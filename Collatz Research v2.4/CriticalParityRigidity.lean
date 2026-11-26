import Mathlib

/-!
# Critical parity rigidity
A greedy integer schedule keeps the multiplicative coefficient in [1,3).
Its offset forces linear growth but the range of possible visits is too
small for indefinitely many distinct visits. This is a restricted schedule,
not a proof for all critical-density or supercritical Collatz trajectories.
-/
namespace CollatzRunyan.CriticalParityRigidity

def criticalCount : ℕ → ℕ
  | 0 => 0
  | k + 1 => if (3 : ℤ) ^ criticalCount k < (2 : ℤ) ^ (k+1)
      then criticalCount k + 1 else criticalCount k

def criticalOffset : ℕ → ℤ
  | 0 => 0
  | k + 1 => if (3 : ℤ) ^ criticalCount k < (2 : ℤ) ^ (k+1)
      then 3 * criticalOffset k + (2 : ℤ)^k else criticalOffset k

def shortcut (n : ℤ) : ℤ :=
  if n % 2 = 0 then n / 2 else (3*n+1)/2

def orbit (n : ℤ) : ℕ → ℤ
  | 0 => n
  | k+1 => shortcut (orbit n k)

theorem critical_increment (k : ℕ) :
    criticalCount (k+1) = criticalCount k ∨
    criticalCount (k+1) = criticalCount k+1 := by
  by_cases h : (3 : ℤ)^criticalCount k < (2 : ℤ)^(k+1)
  · right
    simp only [criticalCount, if_pos h]
  · left
    simp only [criticalCount, if_neg h]

theorem critical_window (k : ℕ) :
    (2 : ℤ)^k ≤ (3 : ℤ)^criticalCount k ∧
    (3 : ℤ)^criticalCount k < 3*(2 : ℤ)^k := by
  induction k with
  | zero => norm_num [criticalCount]
  | succ k ih =>
    by_cases h : (3 : ℤ)^criticalCount k < (2 : ℤ)^(k+1)
    · simp only [criticalCount, if_pos h]
      simp only [pow_succ]
      rw [pow_succ] at h
      constructor <;> omega
    · simp only [criticalCount, if_neg h]
      simp only [pow_succ]
      rw [pow_succ] at h
      constructor <;> omega

theorem critical_offset_bounds (k : ℕ) :
    (criticalCount k : ℤ)*(3 : ℤ)^criticalCount k ≤ 6*criticalOffset k ∧
    3*criticalOffset k ≤ (criticalCount k : ℤ)*(3 : ℤ)^criticalCount k := by
  induction k with
  | zero => norm_num [criticalCount, criticalOffset]
  | succ k ih =>
    have hw := critical_window k
    by_cases h : (3 : ℤ)^criticalCount k < (2 : ℤ)^(k+1)
    · simp only [criticalCount, criticalOffset, if_pos h]
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      rw [pow_succ] at h
      constructor <;> nlinarith [ih.1, ih.2, hw.1]
    · simpa only [criticalCount, criticalOffset, if_neg h] using ih

theorem critical_affine_bounds (k : ℕ) (n y : ℤ) (hn : 0 ≤ n)
    (he : (2 : ℤ)^k*y = (3 : ℤ)^criticalCount k*n + criticalOffset k) :
    6*n+(criticalCount k : ℤ) ≤ 6*y ∧ y ≤ 3*n+(criticalCount k : ℤ) := by
  have hw := critical_window k
  have hb := critical_offset_bounds k
  have hm : 0 < (2 : ℤ)^k := by positivity
  have ha : 0 ≤ (criticalCount k : ℤ) := by positivity
  have hn1 := mul_le_mul_of_nonneg_right hw.1 hn
  have ha1 := mul_le_mul_of_nonneg_right hw.1 ha
  have hn2 := mul_le_mul_of_nonneg_right (le_of_lt hw.2) hn
  have ha2 := mul_le_mul_of_nonneg_right (le_of_lt hw.2) ha
  have hl : (2 : ℤ)^k*(6*n+(criticalCount k : ℤ)) ≤ (2 : ℤ)^k*(6*y) := by
    nlinarith [hb.1]
  have hu : (2 : ℤ)^k*y ≤ (2 : ℤ)^k*(3*n+(criticalCount k : ℤ)) := by
    nlinarith [hb.2]
  constructor
  · by_contra! h
    have hh := mul_lt_mul_of_pos_left h hm
    exact (not_lt_of_ge hl) hh
  · by_contra! h
    have hh := mul_lt_mul_of_pos_left h hm
    exact (not_lt_of_ge hu) hh

theorem critical_two_steps (k : ℕ) : criticalCount k+1 ≤ criticalCount (k+2) := by
  have h0 := critical_increment k
  have h1 := critical_increment (k+1)
  change criticalCount (k+2) = criticalCount (k+1) ∨
    criticalCount (k+2) = criticalCount (k+1)+1 at h1
  by_contra! h
  have he : criticalCount (k+2) = criticalCount k := by
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> omega
  have hw := critical_window k
  have hv := critical_window (k+2)
  rw [he] at hv
  have hp : (2 : ℤ)^(k+2) = (2 : ℤ)^k*4 := by
    rw [pow_add]; norm_num
  rw [hp] at hv
  have hpos : 0 < (2 : ℤ)^k := by positivity
  omega

theorem critical_three_steps (k : ℕ) : criticalCount (k+3) ≤ criticalCount k+2 := by
  have h0 := critical_increment k
  have h1 := critical_increment (k+1)
  have h2 := critical_increment (k+2)
  change criticalCount (k+2) = criticalCount (k+1) ∨
    criticalCount (k+2) = criticalCount (k+1)+1 at h1
  change criticalCount (k+3) = criticalCount (k+2) ∨
    criticalCount (k+3) = criticalCount (k+2)+1 at h2
  by_contra! h
  have he : criticalCount (k+3) = criticalCount k+3 := by
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> omega
  have hw := critical_window k
  have hv := critical_window (k+3)
  rw [he] at hv
  have hp : (2 : ℤ)^(k+3) = (2 : ℤ)^k*8 := by rw [pow_add]; norm_num
  have hq : (3 : ℤ)^(criticalCount k+3) = (3 : ℤ)^criticalCount k*27 := by
    rw [pow_add]; norm_num
  rw [hp, hq] at hv
  have hpos : 0 < (2 : ℤ)^k := by positivity
  omega

theorem critical_count_lower (r : ℕ) : r ≤ criticalCount (2*r) := by
  induction r with
  | zero => omega
  | succ r ih =>
    have h := critical_two_steps (2*r)
    have he : 2*(r+1) = 2*r+2 := by omega
    change r+1 ≤ criticalCount (2*(r+1))
    rw [he]
    omega

theorem critical_even_lower (r : ℕ) : criticalCount (3*r)+r ≤ 3*r := by
  induction r with
  | zero => norm_num [criticalCount]
  | succ r ih =>
    have h := critical_three_steps (3*r)
    have he : 3*(r+1) = 3*r+3 := by omega
    change criticalCount (3*(r+1))+(r+1) ≤ 3*(r+1)
    rw [he]
    omega

/-- The actual orbit has the affine coefficients of the greedy schedule
    if its parity decisions match that schedule up to the requested time. -/
theorem critical_actual_affine (n : ℤ) (k : ℕ)
    (h : ∀ j < k, (orbit n j % 2 ≠ 0) ↔
      (3 : ℤ)^criticalCount j < (2 : ℤ)^(j+1)) :
    (2 : ℤ)^k*orbit n k = (3 : ℤ)^criticalCount k*n+criticalOffset k := by
  induction k with
  | zero => simp [orbit, criticalCount, criticalOffset]
  | succ k ih =>
    have hi := ih (fun j hj => h j (by omega))
    have hc := h k (by omega)
    by_cases hs : (3 : ℤ)^criticalCount k < (2 : ℤ)^(k+1)
    · have ho := hc.mpr hs
      have ht : 2*shortcut (orbit n k) = 3*orbit n k+1 := by
        unfold shortcut
        rw [if_neg ho]
        omega
      simp only [orbit, criticalCount, criticalOffset, if_pos hs]
      calc
        _ = (2 : ℤ)^k*(2*shortcut (orbit n k)) := by rw [pow_succ]; ring
        _ = (2 : ℤ)^k*(3*orbit n k+1) := by rw [ht]
        _ = 3*((2 : ℤ)^k*orbit n k)+(2 : ℤ)^k := by ring
        _ = 3*((3 : ℤ)^criticalCount k*n+criticalOffset k)+(2 : ℤ)^k := by rw [hi]
        _ = _ := by rw [pow_succ]; ring
    · have he : orbit n k % 2 = 0 := by
        by_contra hh
        exact hs (hc.mp hh)
      have ht : 2*shortcut (orbit n k) = orbit n k := by
        unfold shortcut
        rw [if_pos he]
        omega
      simp only [orbit, criticalCount, criticalOffset, if_neg hs]
      calc
        _ = (2 : ℤ)^k*(2*shortcut (orbit n k)) := by rw [pow_succ]; ring
        _ = (2 : ℤ)^k*orbit n k := by rw [ht]
        _ = _ := hi

/-- Pigeonhole endpoint: if the k+1 visits of a matching prefix are
    distinct, their translated natural values fit into a finite interval. -/
theorem critical_distinct_prefix_bound (n : ℤ) (k : ℕ) (hn : 0 ≤ n)
    (h : ∀ j < k, (orbit n j % 2 ≠ 0) ↔
      (3 : ℤ)^criticalCount j < (2 : ℤ)^(j+1))
    (hmono : ∀ j ≤ k, criticalCount j ≤ criticalCount k)
    (hinj : Function.Injective (fun j : Fin (k+1) => orbit n j.val)) :
    (k : ℤ) ≤ 2*n+(criticalCount k : ℤ) := by
  let f : Fin (k+1) → Fin ((2*n+(criticalCount k : ℤ)).toNat+1) := fun j =>
    ⟨(orbit n j.val-n).toNat, by
      have hj : j.val ≤ k := by
        have hjlt := j.isLt
        omega
      have hb := critical_affine_bounds j.val n (orbit n j.val) hn
        (critical_actual_affine n j.val (fun i hi => h i (by omega)))
      have hc : (criticalCount j.val : ℤ) ≤ (criticalCount k : ℤ) := by
        exact_mod_cast hmono j.val hj
      omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hil := i.isLt
    have hjl := j.isLt
    apply hinj
    change orbit n i.val = orbit n j.val
    have he : (orbit n i.val-n).toNat = (orbit n j.val-n).toNat :=
      congrArg Fin.val hij
    have hi := critical_affine_bounds i.val n (orbit n i.val) hn
      (critical_actual_affine n i.val (fun t ht => h t (by omega)))
    have hj := critical_affine_bounds j.val n (orbit n j.val) hn
      (critical_actual_affine n j.val (fun t ht => h t (by omega)))
    have hi0 : 0 ≤ orbit n i.val-n := by
      have hci : 0 ≤ (criticalCount i.val : ℤ) := by positivity
      omega
    have hj0 : 0 ≤ orbit n j.val-n := by
      have hcj : 0 ≤ (criticalCount j.val : ℤ) := by positivity
      omega
    omega
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

#print axioms critical_increment
#print axioms critical_window
#print axioms critical_offset_bounds
#print axioms critical_affine_bounds
#print axioms critical_two_steps
#print axioms critical_three_steps
#print axioms critical_count_lower
#print axioms critical_even_lower
#print axioms critical_actual_affine
#print axioms critical_distinct_prefix_bound

end CollatzRunyan.CriticalParityRigidity
