import Mathlib

/-!
# Full odd-predecessor family coalescence (candidate)

A relation 3*y+1 = 4^r*(3*x+1) forces the odd starting values to
coalesce. An injective shortcut orbit meets such a family at most once.
Eligible odd values have a smaller eligible representative outside two
removed residue classes, with one exceptional value 5. The remaining
residue set has 27 members per block of 96 integers.

This module does not formalize the subsequent logarithmic product bound,
assert divergence exclusion, or claim a proof of the Collatz conjecture.
-/
namespace CollatzRunyan.FamilyCoalescenceRigidity

def shortcut (x : ℕ) : ℕ :=
  if x % 2 = 0 then x / 2 else (3*x+1)/2

def orbit (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k+1 => shortcut (orbit n k)

def Eligible (x : ℕ) : Prop :=
  5 ≤ x ∧ x % 2 ≠ 0 ∧ x % 3 ≠ 0

/-- x is at least as high in the same odd-predecessor family as y. -/
def Family (x y : ℕ) : Prop :=
  ∃ r : ℕ, 3*x+1 = 4^r*(3*y+1)

theorem orbit_add (n i j : ℕ) : orbit n (i+j) = orbit (orbit n i) j := by
  induction j with
  | zero => simp [orbit]
  | succ j ih =>
    change shortcut (orbit n (i+j)) = shortcut (orbit (orbit n i) j)
    exact congrArg shortcut ih

theorem orbit_shift (n k : ℕ) : orbit n (k+1) = orbit (shortcut n) k := by
  calc
    orbit n (k+1) = orbit n (1+k) := by rw [Nat.add_comm k 1]
    _ = orbit (orbit n 1) k := orbit_add n 1 k
    _ = orbit (shortcut n) k := by rfl

theorem shortcut_even (x : ℕ) : shortcut (2*x) = x := by
  simp only [shortcut, if_pos (show (2*x)%2 = 0 by omega)]
  omega

theorem shortcut_odd (x : ℕ) (hx : x % 2 ≠ 0) :
    2*shortcut x = 3*x+1 := by
  simp only [shortcut, if_neg hx]
  omega

theorem orbit_pow_two (x r : ℕ) : orbit (2^r*x) r = x := by
  induction r with
  | zero => simp [orbit]
  | succ r ih =>
    have hscale : 2^(r+1)*x = 2*(2^r*x) := by rw [pow_succ]; ring
    rw [hscale, orbit_shift, shortcut_even]
    exact ih

theorem family_step (x y r : ℕ) (hx : x % 2 ≠ 0) (hy : y % 2 ≠ 0)
    (h : 3*y+1 = 4^r*(3*x+1)) :
    shortcut y = 2^(2*r)*shortcut x := by
  have hx2 := shortcut_odd x hx
  have hy2 := shortcut_odd y hy
  have hp : (4 : ℕ)^r = 2^(2*r) := by rw [pow_mul]; norm_num
  have he : 2*shortcut y = 2*(2^(2*r)*shortcut x) := by
    calc
      2*shortcut y = 3*y+1 := hy2
      _ = 4^r*(3*x+1) := h
      _ = 2^(2*r)*(2*shortcut x) := by rw [hp, hx2]
      _ = _ := by ring
  omega

/-- The larger family member reaches the smaller member's successor. -/
theorem family_merge (x y r : ℕ) (hx : x % 2 ≠ 0) (hy : y % 2 ≠ 0)
    (h : 3*y+1 = 4^r*(3*x+1)) :
    orbit y (2*r+1) = shortcut x := by
  rw [orbit_shift, family_step x y r hx hy h]
  exact orbit_pow_two (shortcut x) (2*r)

/-- For a proper family member, its penultimate visit is 3*x+1, not x. -/
theorem family_penultimate (x y r : ℕ) (hx : x % 2 ≠ 0) (hy : y % 2 ≠ 0)
    (h : 3*y+1 = 4^(r+1)*(3*x+1)) :
    orbit y (2*r+2) = 3*x+1 := by
  have hs := family_step x y (r+1) hx hy h
  have hp : (2 : ℕ)^(2*(r+1)) = 2^(2*r+1)*2 := by
    rw [show 2*(r+1) = (2*r+1)+1 by omega, pow_succ]
  have hstep : shortcut y = 2^(2*r+1)*(3*x+1) := by
    rw [hs, hp, mul_assoc, shortcut_odd x hx]
  calc
    orbit y (2*r+2) = orbit (shortcut y) (2*r+1) := by
      simpa only [Nat.add_assoc] using orbit_shift y (2*r+1)
    _ = orbit (2^(2*r+1)*(3*x+1)) (2*r+1) := by rw [hstep]
    _ = 3*x+1 := orbit_pow_two (3*x+1) (2*r+1)

/-- No two distinct odd members of a family occur in an injective orbit. -/
theorem proper_family_exclusion (n i j r : ℕ)
    (hinj : Function.Injective (orbit n))
    (hi : orbit n i % 2 ≠ 0) (hj : orbit n j % 2 ≠ 0) :
    3*orbit n j+1 ≠ 4^(r+1)*(3*orbit n i+1) := by
  intro h
  have hv : orbit n (j+(2*r+2)) = 3*orbit n i+1 := by
    rw [orbit_add]
    exact family_penultimate _ _ r hi hj h
  have he : orbit n (j+(2*r+2)+1) = orbit n (i+1) := by
    change shortcut (orbit n (j+(2*r+2))) = shortcut (orbit n i)
    rw [hv]
    simp only [shortcut, if_pos (show (3*orbit n i+1)%2 = 0 by omega), if_neg hi]
  have ht := hinj he
  have hidx : i = j+(2*r+2) := by omega
  have hbad : orbit n i = 3*orbit n i+1 := by
    calc
      orbit n i = orbit n (j+(2*r+2)) := congrArg (orbit n) hidx
      _ = _ := hv
  omega

theorem family_refl (x : ℕ) : Family x x := by
  exact ⟨0, by simp⟩

theorem family_trans (x y z : ℕ) (hxy : Family x y) (hyz : Family y z) :
    Family x z := by
  obtain ⟨a, ha⟩ := hxy
  obtain ⟨b, hb⟩ := hyz
  refine ⟨a+b, ?_⟩
  rw [ha, hb, pow_add, mul_assoc]

/-- Members with a common lower representative are comparable by powers of four. -/
theorem family_comparable (x y z : ℕ) (hx : Family x z) (hy : Family y z) :
    Family x y ∨ Family y x := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  by_cases hab : a ≤ b
  · right
    let d := b-a
    have hd : b = a+d := by dsimp [d]; omega
    refine ⟨d, ?_⟩
    calc
      3*y+1 = 4^b*(3*z+1) := hb
      _ = 4^d*(4^a*(3*z+1)) := by rw [hd, pow_add]; ring
      _ = 4^d*(3*x+1) := by rw [ha]
  · left
    let d := a-b
    have hd : a = b+d := by dsimp [d]; omega
    refine ⟨d, ?_⟩
    calc
      3*x+1 = 4^a*(3*z+1) := ha
      _ = 4^d*(4^b*(3*z+1)) := by rw [hd, pow_add]; ring
      _ = 4^d*(3*y+1) := by rw [hb]

theorem family_visit_unique (n i j : ℕ) (hinj : Function.Injective (orbit n))
    (hi : orbit n i % 2 ≠ 0) (hj : orbit n j % 2 ≠ 0)
    (h : Family (orbit n j) (orbit n i)) : i = j := by
  obtain ⟨r, hr⟩ := h
  cases r with
  | zero =>
    simp only [pow_zero, one_mul] at hr
    exact hinj (by omega)
  | succ r =>
    exact False.elim (proper_family_exclusion n i j r hinj hi hj hr)

theorem shared_family_visit_unique (n i j z : ℕ)
    (hinj : Function.Injective (orbit n))
    (hi : orbit n i % 2 ≠ 0) (hj : orbit n j % 2 ≠ 0)
    (hx : Family (orbit n i) z) (hy : Family (orbit n j) z) : i = j := by
  rcases family_comparable _ _ _ hx hy with h | h
  · exact (family_visit_unique n j i hinj hj hi h).symm
  · exact family_visit_unique n i j hinj hi hj h

/-- The least eligible member of the lower family exists by well-ordering. -/
theorem family_minimum (x : ℕ) (hx : Eligible x) :
    ∃ y : ℕ, Eligible y ∧ Family x y ∧
      ∀ z : ℕ, Eligible z → Family x z → y ≤ z := by
  classical
  let P : ℕ → Prop := fun y => Eligible y ∧ Family x y
  have he : ∃ y, P y := ⟨x, hx, family_refl x⟩
  have hp : P (Nat.find he) := Nat.find_spec he
  refine ⟨Nat.find he, hp.1, hp.2, ?_⟩
  intro z hz hf
  exact Nat.find_min' he (show P z from ⟨hz, hf⟩)

/-- The first removed residue class has a smaller eligible family member. -/
theorem removed_first (y : ℕ) (hy : 29 ≤ y) (hr : y % 24 = 5) :
    Eligible (y/4) ∧ Family y (y/4) ∧ y/4 < y := by
  refine ⟨?_, ?_, by omega⟩
  · unfold Eligible
    omega
  · refine ⟨1, ?_⟩
    norm_num <;> omega

/-- The second removed class jumps over an ineligible parent divisible by 3. -/
theorem removed_second (y : ℕ) (hr : y % 96 = 85) :
    Eligible (y/16) ∧ Family y (y/16) ∧ y/16 < y := by
  refine ⟨?_, ?_, by omega⟩
  · unfold Eligible
    omega
  · refine ⟨2, ?_⟩
    norm_num <;> omega

theorem eligible_representative (x : ℕ) (hx : Eligible x) :
    ∃ y : ℕ, Eligible y ∧ Family x y ∧ y ≤ x ∧
      (y = 5 ∨ y % 24 ≠ 5) ∧ y % 96 ≠ 85 := by
  obtain ⟨y, hy, hxy, hmin⟩ := family_minimum x hx
  refine ⟨y, hy, hxy, hmin x hx (family_refl x), ?_, ?_⟩
  · by_cases h5 : y = 5
    · exact Or.inl h5
    · right
      intro hr
      have hy5 : 5 ≤ y := hy.1
      obtain ⟨hz, hf, hlt⟩ := removed_first y (by omega) hr
      have hle := hmin (y/4) hz (family_trans x y (y/4) hxy hf)
      omega
  · intro hr
    obtain ⟨hz, hf, hlt⟩ := removed_second y hr
    have hle := hmin (y/16) hz (family_trans x y (y/16) hxy hf)
    omega

/-- Residues of the nonexceptional representatives, in a block of 96. -/
def allowedResidues : Finset ℕ :=
  (Finset.range 96).filter (fun r => r%2 ≠ 0 ∧ r%3 ≠ 0 ∧ r%24 ≠ 5 ∧ r ≠ 85)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem allowed_residue_card : allowedResidues.card = 27 := by decide

theorem representative_residue (y : ℕ) (hy : Eligible y)
    (hfirst : y = 5 ∨ y%24 ≠ 5) (hsecond : y%96 ≠ 85) :
    y = 5 ∨ y%96 ∈ allowedResidues := by
  rcases hfirst with h5 | hfirst
  · exact Or.inl h5
  · right
    rcases hy with ⟨_, hodd, hthree⟩
    have hdiv : y%96+96*(y/96) = y := Nat.mod_add_div y 96
    have h2 : y%96%2 = y%2 := by omega
    have h3 : y%96%3 = y%3 := by omega
    have h24 : y%96%24 = y%24 := by omega
    simp only [allowedResidues, Finset.mem_filter, Finset.mem_range, h2, h3, h24]
    exact ⟨Nat.mod_lt _ (by decide), hodd, hthree, hfirst, hsecond⟩

#print axioms orbit_add
#print axioms orbit_shift
#print axioms shortcut_even
#print axioms shortcut_odd
#print axioms orbit_pow_two
#print axioms family_step
#print axioms family_merge
#print axioms family_penultimate
#print axioms proper_family_exclusion
#print axioms family_refl
#print axioms family_trans
#print axioms family_comparable
#print axioms family_visit_unique
#print axioms shared_family_visit_unique
#print axioms family_minimum
#print axioms removed_first
#print axioms removed_second
#print axioms eligible_representative
#print axioms allowed_residue_card
#print axioms representative_residue

end CollatzRunyan.FamilyCoalescenceRigidity
