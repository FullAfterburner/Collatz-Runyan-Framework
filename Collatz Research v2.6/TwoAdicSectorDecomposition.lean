import BinaryConjugation

/-! Finite integer valuation strata and their two odd residue sectors.
This is an integer-level precursor to a decomposition of the 2-adic integers.
The residue sector is not a physical matter/antimatter identification. -/
namespace CollatzRunyan.TwoAdicSectorDecomposition
open CollatzRunyan.BinaryConjugation

def OddUnit (u : ℤ) : Prop := u % 2 = 1

def UnitSector (u : ℤ) : Prop := u % 4 = 1

theorem oddUnit_neg (u : ℤ) : OddUnit (-u) ↔ OddUnit u := by
  unfold OddUnit
  omega

theorem oddUnit_residues (u : ℤ) (h : OddUnit u) :
    u % 4 = 1 ∨ u % 4 = 3 := by
  unfold OddUnit at h
  omega

theorem unitSector_neg (u : ℤ) (h : OddUnit u) :
    UnitSector (-u) ↔ ¬ UnitSector u := by
  unfold UnitSector
  unfold OddUnit at h
  omega

theorem power_ne_zero (k : ℕ) : (2 : ℤ)^k ≠ 0 := by
  positivity

theorem exactValuation_factor (k : ℕ) (z : ℤ) :
    ExactValuation k z ↔ ∃ u : ℤ, z = (2 : ℤ)^k * u ∧ OddUnit u := by
  unfold ExactValuation
  constructor
  · rintro ⟨⟨u, hu⟩, hn⟩
    refine ⟨u, hu, ?_⟩
    unfold OddUnit
    by_contra h
    have he : u = 2 * (u / 2) := by omega
    apply hn
    refine ⟨u / 2, ?_⟩
    rw [hu, pow_succ]
    calc
      (2 : ℤ)^k * u = (2 : ℤ)^k * (2 * (u / 2)) := congrArg (fun t : ℤ => (2 : ℤ)^k * t) he
      _ = _ := by ring
  · rintro ⟨u, hu, ho⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    rintro ⟨v, hv⟩
    have he : (2 : ℤ)^k * u = (2 : ℤ)^k * (2 * v) := by
      calc
        (2 : ℤ)^k * u = z := hu.symm
        _ = (2 : ℤ)^(k+1) * v := hv
        _ = _ := by rw [pow_succ]; ring
    have hc : u = 2 * v := by
      exact mul_left_cancel₀ (power_ne_zero k) he
    unfold OddUnit at ho
    omega

theorem factor_unique (k : ℕ) (z u v : ℤ)
    (hu : z = (2 : ℤ)^k * u) (hv : z = (2 : ℤ)^k * v) : u = v := by
  exact mul_left_cancel₀ (power_ne_zero k) (hu.symm.trans hv)

theorem exactValuation_unique_factor (k : ℕ) (z : ℤ)
    (h : ExactValuation k z) :
    ∃! u : ℤ, z = (2 : ℤ)^k * u ∧ OddUnit u := by
  obtain ⟨u, hu, ho⟩ := (exactValuation_factor k z).mp h
  exact ⟨u, ⟨hu, ho⟩, fun v hv => factor_unique k z v u hv.1 hu⟩

theorem reflected_factor (k : ℕ) (z u : ℤ)
    (h : z = (2 : ℤ)^k * u) (ho : OddUnit u) :
    -z = (2 : ℤ)^k * (-u) ∧ OddUnit (-u) := by
  exact ⟨by rw [h, mul_neg], (oddUnit_neg u).mpr ho⟩

theorem canonical_sector (u : ℤ) (h : OddUnit u) :
    UnitSector u ∨ UnitSector (-u) := by
  by_cases hs : UnitSector u
  · exact Or.inl hs
  · exact Or.inr ((unitSector_neg u h).mpr hs)

theorem canonical_sector_exclusive (u : ℤ) (h : OddUnit u) :
    ¬ (UnitSector u ∧ UnitSector (-u)) := by
  rintro ⟨hp, hn⟩
  exact ((unitSector_neg u h).mp hn) hp

example : ExactValuation 2 412 := by
  apply (exactValuation_factor 2 412).mpr
  refine ⟨103, ?_, ?_⟩
  · norm_num
  · norm_num [OddUnit]
example : UnitSector (137 : ℤ) ∧ ¬ UnitSector (-137 : ℤ) := by
  norm_num [UnitSector]

end CollatzRunyan.TwoAdicSectorDecomposition
