import Mathlib

/-!
# Coalescent coefficient rigidity — candidate
An injective shortcut orbit cannot visit both odd x and 4*x+1.
Compress the eligible odd ranks using disjoint pairs and charge only
one correction per compressed rank. Target: ninth-power record bound
with tenth-power coefficient. Not a proof of the Collatz conjecture.
Not yet compiled in Lean.
-/
namespace CollatzRunyan.CoalescentCoefficientRigidity

open scoped BigOperators

def shortcut (x : ℕ) : ℕ :=
  if x % 2 = 0 then x / 2 else (3*x+1)/2

def orbit (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k+1 => shortcut (orbit n k)

def oddCount (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => if orbit n k % 2 = 0 then oddCount n k else oddCount n k+1

def factor (x : ℕ) : ℚ := if x % 2 = 0 then 1/2 else 3/2

def coefficient (n k : ℕ) : ℚ := (3 : ℚ)^oddCount n k / (2 : ℚ)^k

theorem coefficient_step (n k : ℕ) :
    coefficient n (k+1) = coefficient n k * factor (orbit n k) := by
  by_cases h : orbit n k % 2 = 0
  · simp only [coefficient, oddCount, factor, if_pos h, pow_succ]
    rw [div_mul_div_comm, mul_one]
  · simp only [coefficient, oddCount, factor, if_neg h, pow_succ]
    rw [div_mul_div_comm]


/-- A nonmultiple of three stays a nonmultiple of three. -/
theorem shortcut_three_free (x : ℕ) (h3 : x % 3 ≠ 0) :
    shortcut x % 3 ≠ 0 := by
  by_cases h : x % 2 = 0
  · simp only [shortcut, if_pos h]
    omega
  · simp only [shortcut, if_neg h]
    omega

theorem orbit_three_free (n : ℕ) (h3 : n % 3 ≠ 0) (k : ℕ) :
    orbit n k % 3 ≠ 0 := by
  induction k with
  | zero => simpa [orbit] using h3
  | succ k ih => exact shortcut_three_free (orbit n k) ih

/-- Odd three-free integers have at most one representative per rank x/3. -/
theorem odd_rank_injective (x y : ℕ) (hx : x % 2 ≠ 0) (hy : y % 2 ≠ 0)
    (hx3 : x % 3 ≠ 0) (hy3 : y % 3 ≠ 0) (h : x / 3 = y / 3) : x = y := by
  omega

theorem odd_rank_bounds (x : ℕ) (hx : 2 ≤ x) (ho : x % 2 ≠ 0)
    (h3 : x % 3 ≠ 0) : 1 ≤ x / 3 ∧ 3*(x/3)+1 ≤ x := by
  omega

/-- The larger odd sibling merges after three shortcut steps. -/
theorem sibling_steps (x : ℕ) (hx : x % 2 ≠ 0) :
    shortcut (shortcut (shortcut (4*x+1))) = shortcut x := by
  have h1 : shortcut (4*x+1) = 2*(3*x+1) := by
    simp only [shortcut, if_neg (show (4*x+1)%2 ≠ 0 by omega)]
    omega
  have h2 : shortcut (2*(3*x+1)) = 3*x+1 := by
    simp only [shortcut, if_pos (show (2*(3*x+1))%2 = 0 by omega)]
    omega
  rw [h1, h2]
  simp only [shortcut, if_pos (show (3*x+1)%2 = 0 by omega), if_neg hx]

/-- An injective orbit cannot contain both odd siblings, in either order. -/
theorem sibling_exclusion (n i j : ℕ) (hinj : Function.Injective (orbit n))
    (ho : orbit n i % 2 ≠ 0) : orbit n j ≠ 4*orbit n i+1 := by
  intro h
  have he : orbit n (j+3) = orbit n (i+1) := by
    change shortcut (shortcut (shortcut (orbit n j))) = shortcut (orbit n i)
    rw [h]
    exact sibling_steps _ ho
  have ht := hinj he
  have h1 : shortcut (4*orbit n i+1) = 2*(3*orbit n i+1) := by
    simp only [shortcut, if_neg (show (4*orbit n i+1)%2 ≠ 0 by omega)]
    omega
  have h2 : shortcut (2*(3*orbit n i+1)) = 3*orbit n i+1 := by
    simp only [shortcut, if_pos (show (2*(3*orbit n i+1))%2 = 0 by omega)]
    omega
  have hv : orbit n (j+2) = 3*orbit n i+1 := by
    change shortcut (shortcut (orbit n j)) = _
    rw [h, h1, h2]
  have hi : i = j+2 := by omega
  have hh : orbit n i = 3*orbit n i+1 := by
    calc
      orbit n i = orbit n (j+2) := congrArg (orbit n) hi
      _ = _ := hv
  omega

/-- Pair 6t+1 with 24t+5 for t≥1. Keep the exceptional value 5. -/
def representative (x : ℕ) : ℕ :=
  if x % 24 = 5 ∧ 29 ≤ x then x/4 else x

theorem representative_bounds (x : ℕ) (hx : 2 ≤ x)
    (ho : x % 2 ≠ 0) (h3 : x % 3 ≠ 0) :
    5 ≤ representative x ∧ representative x ≤ x ∧
    representative x % 2 ≠ 0 ∧ representative x % 3 ≠ 0 ∧
    (representative x = 5 ∨ representative x % 24 ≠ 5) := by
  unfold representative
  split <;> rename_i h
  · obtain ⟨hm, hb⟩ := h
    omega
  · omega

/-- Equality of representatives of distinct odd values forces a sibling pair. -/
theorem representative_collision (x y : ℕ)
    (h : representative x = representative y) :
    x = y ∨ x = 4*y+1 ∨ y = 4*x+1 := by
  unfold representative at h
  split at h <;> split at h <;> omega

theorem representative_visit_injective (n i j : ℕ)
    (hinj : Function.Injective (orbit n))
    (hi : orbit n i % 2 ≠ 0) (hj : orbit n j % 2 ≠ 0)
    (h : representative (orbit n i) = representative (orbit n j)) : i = j := by
  rcases representative_collision _ _ h with he | he | he
  · exact hinj he
  · exact False.elim (sibling_exclusion n j i hinj hj he)
  · exact False.elim (sibling_exclusion n i j hinj hi he)

/-- The removed ranks are 9,17,25,... . -/
def compress (r : ℕ) : ℕ := r - (r-1)/8

def visitRank (x : ℕ) : ℕ := compress (representative x / 3)

theorem representative_rank_allowed (x : ℕ) (hx : 2 ≤ x)
    (ho : x % 2 ≠ 0) (h3 : x % 3 ≠ 0) :
    1 ≤ representative x / 3 ∧
    (representative x / 3 = 1 ∨ (representative x / 3) % 8 ≠ 1) := by
  obtain ⟨hmin, hle, hodd, hthree, hres⟩ := representative_bounds x hx ho h3
  rcases hres with h5 | h24 <;> omega

/-- Compression is injective on the ranks that were not removed. -/
theorem compress_injective (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (ha : r = 1 ∨ r%8 ≠ 1) (hb : s = 1 ∨ s%8 ≠ 1)
    (he : compress r = compress s) : r = s := by
  -- Work in blocks of eight original ranks and seven compressed ranks.
  -- The only allowed block with remainder zero is the exceptional rank 1.
  have decompose (a : ℕ) (ha1 : 1 ≤ a)
      (ha2 : a = 1 ∨ a % 8 ≠ 1) :
      ∃ q t : ℕ, a = 8*q+t+1 ∧ compress a = 7*q+t+1 ∧
        t < 8 ∧ (1 ≤ t ∨ (q = 0 ∧ t = 0)) := by
    let q := (a-1)/8
    let t := (a-1)%8
    have hdiv : t+8*q = a-1 := Nat.mod_add_div (a-1) 8
    have ht : t < 8 := Nat.mod_lt (a-1) (by decide)
    have hea : a = 8*q+t+1 := by omega
    have hec : compress a = 7*q+t+1 := by
      unfold compress
      change a-q = 7*q+t+1
      omega
    refine ⟨q, t, hea, hec, ht, ?_⟩
    by_cases hz : t = 0
    · right
      have ha0 : a = 1 := by
        rcases ha2 with h1 | hne
        · exact h1
        · exfalso
          apply hne
          rw [hea, hz]
          omega
      exact ⟨by omega, hz⟩
    · left
      omega
  obtain ⟨q, u, hr1, hr2, hu, hqu⟩ := decompose r hr ha
  obtain ⟨p, v, hs1, hs2, hv, hpv⟩ := decompose s hs hb
  have hc : 7*q+u+1 = 7*p+v+1 := hr2.symm.trans (he.trans hs2)
  rcases hqu with hu1 | ⟨hq0, hu0⟩ <;>
    rcases hpv with hv1 | ⟨hp0, hv0⟩ <;> omega

theorem visit_rank_bounds (x : ℕ) (hx : 2 ≤ x)
    (ho : x % 2 ≠ 0) (h3 : x % 3 ≠ 0) :
    1 ≤ visitRank x ∧ visitRank x ≤ x/3 ∧
      10*max 1 (visitRank x-1)+5 ≤ 3*x := by
  obtain ⟨hmin, hle, hodd, hthree, hres⟩ := representative_bounds x hx ho h3
  have hr : 1 ≤ representative x/3 := by omega
  have hlow : 3*(representative x/3)+1 ≤ representative x := by omega
  have hx5 : 5 ≤ x := by omega
  unfold visitRank compress
  have hcap : 10*(representative x/3 - (representative x/3-1)/8) ≤ 3*x+5 := by omega
  refine ⟨by omega, by omega, ?_⟩
  by_cases h : 1 ≤ representative x/3 - (representative x/3-1)/8 - 1
  · rw [max_eq_right h]
    omega
  · rw [max_eq_left (by omega : representative x/3 - (representative x/3-1)/8 - 1 ≤ 1)]
    omega

theorem visit_rank_injective (n i j : ℕ) (hinj : Function.Injective (orbit n))
    (hthree : n % 3 ≠ 0) (hsi : 2 ≤ orbit n i) (hsj : 2 ≤ orbit n j)
    (hi : orbit n i % 2 ≠ 0) (hj : orbit n j % 2 ≠ 0)
    (h : visitRank (orbit n i) = visitRank (orbit n j)) : i = j := by
  have h3i := orbit_three_free n hthree i
  have h3j := orbit_three_free n hthree j
  obtain ⟨hri, hai⟩ := representative_rank_allowed _ hsi hi h3i
  obtain ⟨hrj, haj⟩ := representative_rank_allowed _ hsj hj h3j
  obtain ⟨_, _, hio, hi3, _⟩ := representative_bounds _ hsi hi h3i
  obtain ⟨_, _, hjo, hj3, _⟩ := representative_bounds _ hsj hj h3j
  have he := compress_injective _ _ hri hrj hai haj h
  exact representative_visit_injective n i j hinj hi hj
    (odd_rank_injective _ _ hio hjo hi3 hj3 he)

def rankMajor (r : ℕ) : ℚ :=
  if r = 0 then 1 else
    (((max 1 (r-1) : ℕ) : ℚ)+1) / ((max 1 (r-1) : ℕ) : ℚ)

def major (x : ℕ) : ℚ :=
  if x % 2 = 0 then 1 else rankMajor (visitRank x)

theorem rank_major_ge_one (r : ℕ) : 1 ≤ rankMajor r := by
  by_cases h : r = 0
  · simp [rankMajor, h]
  · have hm : (1 : ℚ) ≤ ((max 1 (r-1) : ℕ) : ℚ) := by
      exact_mod_cast (le_max_left 1 (r-1))
    rw [rankMajor, if_neg h]
    apply (le_div_iff₀ (by linarith : 0 < ((max 1 (r-1) : ℕ) : ℚ))).2
    linarith

theorem major_ge_one (x : ℕ) : 1 ≤ major x := by
  by_cases h : x % 2 = 0
  · simp [major, h]
  · simpa [major, h] using rank_major_ge_one (visitRank x)

theorem rank_major_range (R : ℕ) (hR : 1 ≤ R) :
    (∏ r ∈ Finset.range (R+1), rankMajor r) = 2*(R : ℚ) := by
  induction R with
  | zero => omega
  | succ R ih =>
    by_cases h : R = 0
    · subst R
      norm_num [Finset.prod_range_succ, rankMajor]
    · have hr : 1 ≤ R := by omega
      have hrq : (0 : ℚ) < (R : ℚ) := by exact_mod_cast (show 0 < R by omega)
      have hn : R+1 ≠ 0 := by omega
      rw [Finset.prod_range_succ, ih hr, rankMajor, if_neg hn]
      rw [show R+1-1 = R by omega, max_eq_right hr, Nat.cast_succ]
      field_simp [ne_of_gt hrq] <;> ring

/-- Symmetric tenth-power bound with all nonnegative coefficients. -/
theorem tenth_correction (u : ℚ) (hu : 0 ≤ u) :
    (u+1)^10*(u-5) ≤ u^10*(u+5) := by
  have h : 0 ≤ u^10*(u+5)-(u+1)^10*(u-5) := by
    rw [show u^10*(u+5)-(u+1)^10*(u-5) =
      5*u^9+105*u^8+390*u^7+798*u^6+1050*u^5+930*u^4+
      555*u^3+215*u^2+49*u+5 by ring]
    positivity
  exact sub_nonneg.mp h

theorem ranked_ten_bound (u d : ℚ) (hd : 1 ≤ d) (hu : 10*d+5 ≤ u) :
    (u+1)^10*d ≤ u^10*(d+1) := by
  have hu0 : 0 ≤ u := by linarith
  have hp : u^10 ≤ (u+1)^10 := by gcongr <;> linarith
  have hbase := tenth_correction u hu0
  have hg := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hp)
  have h : 0 ≤ 10*(u^10*(d+1)-(u+1)^10*d) := by
    calc
      0 ≤ (u^10*(u+5)-(u+1)^10*(u-5)) +
          (u-(10*d+5))*((u+1)^10-u^10) := add_nonneg (sub_nonneg.mpr hbase) hg
      _ = _ := by ring
  linarith

theorem tenth_step_bound (x : ℕ) (hx : 2 ≤ x) (h3 : x % 3 ≠ 0) :
    (shortcut x : ℚ)^10 ≤ (factor x)^10 * (x : ℚ)^10 * major x := by
  by_cases h : x % 2 = 0
  · have he : 2*shortcut x = x := by
      simp only [shortcut, if_pos h]
      omega
    have heq : (2 : ℚ)*(shortcut x : ℚ) = (x : ℚ) := by exact_mod_cast he
    have ht : (shortcut x : ℚ) = (1/2 : ℚ)*(x : ℚ) := by linarith
    rw [ht, factor, if_pos h, major, if_pos h, mul_pow, mul_one]
  · have ho : 2*shortcut x = 3*x+1 := by
      simp only [shortcut, if_neg h]
      omega
    have hoq : (2 : ℚ)*(shortcut x : ℚ) = 3*(x : ℚ)+1 := by exact_mod_cast ho
    have ht : (shortcut x : ℚ) = (3*(x : ℚ)+1)/2 := by linarith
    obtain ⟨hr, _, hlow⟩ := visit_rank_bounds x hx h h3
    have hd : (1 : ℚ) ≤ ((max 1 (visitRank x-1) : ℕ) : ℚ) := by
      exact_mod_cast (le_max_left 1 (visitRank x-1))
    have hlq : 10*((max 1 (visitRank x-1) : ℕ) : ℚ)+5 ≤ 3*(x : ℚ) := by exact_mod_cast hlow
    have hbound := ranked_ten_bound (3*(x : ℚ)) ((max 1 (visitRank x-1) : ℕ) : ℚ) hd hlq
    have hn : visitRank x ≠ 0 := by omega
    rw [ht, factor, if_neg h, major, if_neg h, rankMajor, if_neg hn, ← mul_div_assoc]
    apply (le_div_iff₀ (by linarith : 0 < ((max 1 (visitRank x-1) : ℕ) : ℚ))).2
    calc
      _ = ((3*(x : ℚ)+1)^10*((max 1 (visitRank x-1) : ℕ) : ℚ))/2^10 := by ring
      _ ≤ ((3*(x : ℚ))^10*(((max 1 (visitRank x-1) : ℕ) : ℚ)+1))/2^10 :=
        div_le_div_of_nonneg_right hbound (by norm_num)
      _ = _ := by ring

theorem orbit_product_bound (n k : ℕ) (hthree : n % 3 ≠ 0)
    (hsmall : ∀ j < k, 2 ≤ orbit n j) :
    (orbit n k : ℚ)^10 ≤ (coefficient n k * (n : ℚ))^10 *
      (∏ j ∈ Finset.range k, major (orbit n j)) := by
  induction k with
  | zero => simp [orbit, coefficient, oddCount]
  | succ k ih =>
    have hi := ih (fun j hj => hsmall j (by omega))
    have hs := tenth_step_bound (orbit n k) (hsmall k (by omega)) (orbit_three_free n hthree k)
    have hf : 0 ≤ factor (orbit n k) := by unfold factor; split <;> norm_num
    have hm : 0 ≤ major (orbit n k) := le_trans (by norm_num) (major_ge_one _)
    rw [coefficient_step, Finset.prod_range_succ]
    change (shortcut (orbit n k) : ℚ)^10 ≤ _
    calc
      _ ≤ (factor (orbit n k))^10 * (orbit n k : ℚ)^10 * major (orbit n k) := hs
      _ ≤ (factor (orbit n k))^10 * ((coefficient n k * (n : ℚ))^10 *
          (∏ j ∈ Finset.range k, major (orbit n j))) * major (orbit n k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (pow_nonneg hf _)) hm
      _ = _ := by ring


theorem injective_avoids_small (n : ℕ) (hinj : Function.Injective (orbit n)) (j : ℕ) :
    2 ≤ orbit n j := by
  by_contra! h
  have hc : orbit n j = 0 ∨ orbit n j = 1 := by omega
  rcases hc with h0 | h1
  · have he : orbit n (j+1) = orbit n j := by simp [orbit, h0, shortcut]
    have hh := hinj he
    omega
  · have he : orbit n (j+2) = orbit n j := by norm_num [orbit, h1, shortcut]
    have hh := hinj he
    omega

/-- Only odd visits are charged; each compressed odd rank appears once. -/
theorem distinct_visit_product (n k R : ℕ) (hR : 2 ≤ R)
    (hthree : n % 3 ≠ 0) (hinj : Function.Injective (orbit n))
    (hmax : ∀ j < k, orbit n j ≤ R) :
    (∏ j ∈ Finset.range k, major (orbit n j)) ≤ (R : ℚ) := by
  classical
  let s := (Finset.range k).filter (fun j => orbit n j % 2 ≠ 0)
  let ranks := s.image (fun j => visitRank (orbit n j))
  have hs : ranks ⊆ Finset.range (R/3+1) := by
    intro r hr
    change r ∈ s.image (fun j => visitRank (orbit n j)) at hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    have hjk : j < k := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hv := (visit_rank_bounds _ (injective_avoids_small n hinj j)
      (Finset.mem_filter.mp hj).2 (orbit_three_free n hthree j)).2.1
    exact Finset.mem_range.mpr (by have h := hmax j hjk; omega)
  have he : (∏ r ∈ ranks, rankMajor r) = ∏ j ∈ s, rankMajor (visitRank (orbit n j)) := by
    apply Finset.prod_image
    intro i hi j hj hij
    exact visit_rank_injective n i j hinj hthree (injective_avoids_small n hinj i)
      (injective_avoids_small n hinj j) (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hij
  have hf : (∏ j ∈ s, rankMajor (visitRank (orbit n j))) =
      ∏ j ∈ Finset.range k, major (orbit n j) := by
    dsimp [s]
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro j hj
    by_cases h : orbit n j % 2 = 0 <;> simp [major, h]
  have hp (t : Finset ℕ) : (1 : ℚ) ≤ ∏ r ∈ t, rankMajor r := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert r t hr ih =>
      rw [Finset.prod_insert hr]
      have hm := rank_major_ge_one r
      have ht : 0 ≤ ∏ x ∈ t, rankMajor x := le_trans (by norm_num) ih
      calc
        1 ≤ ∏ x ∈ t, rankMajor x := ih
        _ = 1 * (∏ x ∈ t, rankMajor x) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hm ht
  have hd : (∏ r ∈ Finset.range (R/3+1) \ ranks, rankMajor r) *
      (∏ r ∈ ranks, rankMajor r) =
      ∏ r ∈ Finset.range (R/3+1), rankMajor r := Finset.prod_sdiff hs
  have hle : (∏ r ∈ ranks, rankMajor r) ≤ ∏ r ∈ Finset.range (R/3+1), rankMajor r := by
    rw [← hd]
    calc
      _ = 1 * (∏ r ∈ ranks, rankMajor r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hp _) (le_trans (by norm_num) (hp ranks))
  rw [he, hf] at hle
  have hRq : (2 : ℚ) ≤ (R : ℚ) := by exact_mod_cast hR
  by_cases hz : R/3 = 0
  · rw [hz] at hle
    norm_num [rankMajor] at hle
    exact le_trans hle (by linarith)
  · rw [rank_major_range _ (by omega)] at hle
    have hfloor : 3*((R/3 : ℕ) : ℚ) ≤ (R : ℚ) := by
      exact_mod_cast (show 3*(R/3) ≤ R by omega)
    have hnon : (0 : ℚ) ≤ ((R/3 : ℕ) : ℚ) := by positivity
    exact le_trans hle (by linarith)

theorem exists_prefix_max (n k : ℕ) :
    ∃ j ≤ k, ∀ i ≤ k, orbit n i ≤ orbit n j := by
  induction k with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro i hi
    have h : i = 0 := by omega
    simp [h]
  | succ k ih =>
    obtain ⟨j, hj, hmax⟩ := ih
    by_cases h : orbit n (k+1) ≤ orbit n j
    · refine ⟨j, by omega, ?_⟩
      intro i hi
      by_cases hi' : i ≤ k
      · exact hmax i hi'
      · have he : i = k+1 := by omega
        simpa [he] using h
    · refine ⟨k+1, le_rfl, ?_⟩
      intro i hi
      by_cases hi' : i ≤ k
      · exact le_trans (hmax i hi') (le_of_lt (lt_of_not_ge h))
      · have he : i = k+1 := by omega
        simp [he]


/-- Actual record bound on a three-free injective orbit. -/
theorem record_ninth_bound (n j : ℕ) (hthree : n % 3 ≠ 0)
    (hinj : Function.Injective (orbit n)) (hmax : ∀ i < j, orbit n i ≤ orbit n j) :
    (orbit n j : ℚ)^9 ≤ (coefficient n j * (n : ℚ))^10 := by
  have hj := injective_avoids_small n hinj j
  have hjq : 0 < (orbit n j : ℚ) := by exact_mod_cast (show 0 < orbit n j by omega)
  have hp := orbit_product_bound n j hthree (fun i _ => injective_avoids_small n hinj i)
  have hd := distinct_visit_product n j (orbit n j) hj hthree hinj hmax
  have hc : 0 ≤ coefficient n j := by unfold coefficient; positivity
  have hb : (orbit n j : ℚ)^10 ≤ (coefficient n j * (n : ℚ))^10 * (orbit n j : ℚ) :=
    le_trans hp (mul_le_mul_of_nonneg_left hd (by positivity))
  by_contra! h
  have hh := mul_lt_mul_of_pos_right h hjq
  have he : (orbit n j : ℚ)^9 * (orbit n j : ℚ) = (orbit n j : ℚ)^10 := by ring
  rw [he] at hh
  exact (not_lt_of_ge hb) hh

theorem prefix_coefficient_growth (n k : ℕ) (hthree : n % 3 ≠ 0) (hinj : Function.Injective (orbit n)) :
    ∃ j ≤ k, (k : ℚ)^9 ≤ (coefficient n j * (n : ℚ))^10 := by
  obtain ⟨j, hj, hmax⟩ := exists_prefix_max n k
  let f : Fin (k+1) → Fin (orbit n j+1) := fun i =>
    ⟨orbit n i.val, by have hi := i.isLt; have hm := hmax i.val (by omega); omega⟩
  have hf : Function.Injective f := by
    intro i l he
    apply Fin.ext
    apply hinj
    exact congrArg Fin.val he
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  have hk : k ≤ orbit n j := by omega
  have hkq : (k : ℚ) ≤ (orbit n j : ℚ) := by exact_mod_cast hk
  have hpow : (k : ℚ)^9 ≤ (orbit n j : ℚ)^9 := by
    gcongr <;> first | exact hkq | positivity
  exact ⟨j, hj, le_trans hpow (record_ninth_bound n j hthree hinj (fun i hi => hmax i (by omega)))⟩


#print axioms coefficient_step
#print axioms shortcut_three_free
#print axioms orbit_three_free
#print axioms odd_rank_injective
#print axioms odd_rank_bounds
#print axioms sibling_steps
#print axioms sibling_exclusion
#print axioms representative_bounds
#print axioms representative_collision
#print axioms representative_visit_injective
#print axioms representative_rank_allowed
#print axioms compress_injective
#print axioms visit_rank_bounds
#print axioms visit_rank_injective
#print axioms rank_major_ge_one
#print axioms major_ge_one
#print axioms rank_major_range
#print axioms tenth_correction
#print axioms ranked_ten_bound
#print axioms tenth_step_bound
#print axioms orbit_product_bound
#print axioms injective_avoids_small
#print axioms distinct_visit_product
#print axioms exists_prefix_max
#print axioms record_ninth_bound
#print axioms prefix_coefficient_growth

end CollatzRunyan.CoalescentCoefficientRigidity
