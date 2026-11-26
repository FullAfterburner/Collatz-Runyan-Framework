import ParityDriftConflict
import CollatzCorrectionBounds

/-! Bridge for supplied exact odd-to-odd blocks. No global orbit
existence, divergence exclusion, or cycle exclusion is asserted. -/
namespace CollatzRunyan.CollatzIterationBridge
open CollatzRunyan.SparseCoefficientRigidity
open CollatzRunyan.CollatzAdelicDrift (binaryBudget)
open CollatzRunyan.CollatzAdelicCompatibility (normalized normalized_of_factor)

theorem orbit_add_bridge (n a b : ℕ) :
    orbit n (a+b) = orbit (orbit n a) b := by
  induction b with
  | zero => simp [orbit]
  | succ b ih =>
    change shortcut (orbit n (a+b)) = shortcut (orbit (orbit n a) b)
    exact congrArg shortcut ih

theorem oddCount_add_bridge (n a b : ℕ) :
    oddCount n (a+b) = oddCount n a + oddCount (orbit n a) b := by
  induction b with
  | zero => simp [oddCount]
  | succ b ih =>
    change (if orbit n (a+b) % 2 = 0 then oddCount n (a+b)
      else oddCount n (a+b)+1) = oddCount n a +
      (if orbit (orbit n a) b % 2 = 0 then oddCount (orbit n a) b
      else oddCount (orbit n a) b+1)
    rw [orbit_add_bridge, ih]
    split <;> omega

theorem even_block (y r : ℕ) :
    orbit (2^r*y) r = y ∧ oddCount (2^r*y) r = 0 := by
  induction r with
  | zero => simp [orbit, oddCount]
  | succ r ih =>
    have he : 2^(r+1)*y = 2*(2^r*y) := by rw [pow_succ]; ring
    have hs : shortcut (2*(2^r*y)) = 2^r*y := by
      simp only [shortcut, if_pos (show (2*(2^r*y))%2 = 0 by omega)]
      omega
    rw [he, show r+1 = 1+r by omega, orbit_add_bridge, oddCount_add_bridge]
    have ho : orbit (2*(2^r*y)) 1 = 2^r*y := hs
    have hc : oddCount (2*(2^r*y)) 1 = 0 := by
      simp [oddCount, orbit, show (2*(2^r*y))%2 = 0 by omega]
    rw [ho, hc, zero_add]
    exact ih

theorem odd_block (x y r : ℕ) (hx : x%2 ≠ 0)
    (h : 3*x+1 = 2^(r+1)*y) :
    orbit x (r+1) = y ∧ oddCount x (r+1) = 1 := by
  have he : 2^(r+1)*y = 2*(2^r*y) := by rw [pow_succ]; ring
  have hs : shortcut x = 2^r*y := by
    simp only [shortcut, if_neg hx]
    rw [h, he]
    omega
  rw [show r+1 = 1+r by omega, orbit_add_bridge, oddCount_add_bridge]
  have ho : orbit x 1 = 2^r*y := hs
  have hc : oddCount x 1 = 1 := by simp [oddCount, orbit, hx]
  rw [ho, hc]
  obtain ⟨ha, hb⟩ := even_block y r
  simp [ha, hb]

/-- The supplied exponents are r i + 1; odd endpoints make them exact. -/
def budget (r : ℕ → ℕ) (m : ℕ) : ℕ := binaryBudget (fun i => r i+1) m

theorem orbit_agreement (a r : ℕ → ℕ) (ho : ∀ i, a i%2 ≠ 0)
    (hs : ∀ i, 3*a i+1 = 2^(r i+1)*a (i+1)) (m : ℕ) :
    orbit (a 0) (budget r m) = a m ∧ oddCount (a 0) (budget r m) = m := by
  induction m with
  | zero => simp [budget, binaryBudget, orbit, oddCount]
  | succ m ih =>
    change orbit (a 0) (budget r m+(r m+1)) = a (m+1) ∧
      oddCount (a 0) (budget r m+(r m+1)) = m+1
    rw [orbit_add_bridge, oddCount_add_bridge, ih.1, ih.2]
    obtain ⟨ha, hb⟩ := odd_block (a m) (a (m+1)) (r m) (ho m) (hs m)
    rw [ha, hb]
    exact ⟨rfl, rfl⟩

theorem coefficient_agreement (a r : ℕ → ℕ) (ho : ∀ i, a i%2 ≠ 0)
    (hs : ∀ i, 3*a i+1 = 2^(r i+1)*a (i+1)) (m : ℕ) :
    coefficient (a 0) (budget r m) = (3 : ℚ)^m / (2 : ℚ)^budget r m := by
  unfold coefficient
  rw [(orbit_agreement a r ho hs m).2]

theorem normalized_agreement (a r : ℕ → ℕ)
    (hs : ∀ i, 3*a i+1 = 2^(r i+1)*a (i+1)) (i : ℕ) :
    (a (i+1) : ℚ) = normalized (a i : ℚ) (r i+1) := by
  apply Eq.symm
  apply normalized_of_factor
  exact_mod_cast hs i

theorem eventual_budget_bound (a r : ℕ → ℕ) (ho : ∀ i, a i%2 ≠ 0)
    (hs : ∀ i, 3*a i+1 = 2^(r i+1)*a (i+1))
    (hinj : Function.Injective (orbit (a 0))) :
    ∃ N : ℕ, ∀ m ≥ N, 5*budget r m < 8*m := by
  obtain ⟨N, hN⟩ := ParityDriftConflict.eventual_above_five_eighths (a 0) hinj
  have hb : ∀ m, m ≤ budget r m := by
    intro m
    induction m with
    | zero => simp [budget, binaryBudget]
    | succ m ih =>
      change m+1 ≤ budget r m+(r m+1)
      omega
  refine ⟨N, fun m hm => ?_⟩
  have h := hN (budget r m) (le_trans hm (hb m))
  rw [(orbit_agreement a r ho hs m).2] at h
  exact h

end CollatzRunyan.CollatzIterationBridge
