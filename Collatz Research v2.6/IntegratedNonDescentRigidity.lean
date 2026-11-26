import CollatzIterationBridge

/-! Conditional restrictions on supplied exact odd-to-odd trajectories.
No universal descent or existence of such trajectories is asserted. -/
namespace CollatzRunyan.IntegratedNonDescentRigidity
open CollatzRunyan.SparseCoefficientRigidity (orbit)
open CollatzRunyan.CollatzIterationBridge
open CollatzRunyan.CollatzCorrectionBounds (nondescending_budget)

theorem prefix_budget_bound (a r : ℕ → ℕ)
    (ho : ∀ i, a i % 2 ≠ 0)
    (hs : ∀ i, 3*a i+1 = 2^(r i+1)*a (i+1))
    (m : ℕ) (hb : ∀ i < m, a 0 ≤ a i)
    (he : a 0 ≤ a m) :
    (2 : ℚ)^budget r m ≤ (3 + 1 / (a 0 : ℚ))^m := by
  have hp : ∀ i, 0 < (a i : ℚ) := by
    intro i
    have hi := ho i
    have hn : 0 < a i := by omega
    exact_mod_cast hn
  have hq : ∀ i < m, (a 0 : ℚ) ≤ (a i : ℚ) := by
    intro i hi
    exact_mod_cast hb i hi
  have hqe : (a 0 : ℚ) ≤ (a m : ℚ) := by exact_mod_cast he
  exact nondescending_budget (fun i => (a i : ℚ)) (fun i => r i+1)
    hp (normalized_agreement a r hs) (a 0 : ℚ) (hp 0) m hq hqe

theorem integrated_bounds (a r : ℕ → ℕ)
    (ho : ∀ i, a i % 2 ≠ 0)
    (hs : ∀ i, 3*a i+1 = 2^(r i+1)*a (i+1))
    (hinj : Function.Injective (orbit (a 0)))
    (hnd : ∀ i, a 0 ≤ a i) :
    ∃ N : ℕ, ∀ m ≥ N, 5*budget r m < 8*m ∧
      (2 : ℚ)^budget r m ≤ (3 + 1 / (a 0 : ℚ))^m := by
  obtain ⟨N, hN⟩ := eventual_budget_bound a r ho hs hinj
  exact ⟨N, fun m hm => ⟨hN m hm,
    prefix_budget_bound a r ho hs m (fun i _ => hnd i) (hnd m)⟩⟩

/-- An independent recurring budget lower bound would exclude injectivity. -/
theorem recurring_budget_forces_repeat (a r : ℕ → ℕ)
    (ho : ∀ i, a i % 2 ≠ 0)
    (hs : ∀ i, 3*a i+1 = 2^(r i+1)*a (i+1))
    (hrec : ∀ N : ℕ, ∃ m ≥ N, 8*m ≤ 5*budget r m) :
    ¬ Function.Injective (orbit (a 0)) := by
  intro hinj
  obtain ⟨N, hN⟩ := eventual_budget_bound a r ho hs hinj
  obtain ⟨m, hm, hb⟩ := hrec N
  exact (not_lt_of_ge hb) (hN m hm)

#print axioms prefix_budget_bound
#print axioms integrated_bounds
#print axioms recurring_budget_forces_repeat
end CollatzRunyan.IntegratedNonDescentRigidity
