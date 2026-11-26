import Mathlib

/-!
# Collatz–Runyan: finite record-time obstruction

This standalone file proves the finite counting and polynomial arithmetic
used in the conditional exclusion of divergence. It does not formalize
Tao's theorem, the logarithmic product estimate, the construction of
coefficient record times, or any unconditional stopping-time upper bound.
In the mathematical application, J counts distinct positive record values,
M is their maximum, K is the last record time, and A and B are constants.
-/

namespace CollatzRunyan.UniversalStoppingResearch

/-- J distinct positive natural numbers bounded by M require J ≤ M. -/
theorem positive_record_count (x : ℕ → ℕ) (J M : ℕ)
    (hinj : Function.Injective x)
    (hbound : ∀ j < J, 0 < x j ∧ x j ≤ M) : J ≤ M := by
  let S := (Finset.range J).image (fun j => x j - 1)
  have hi : Set.InjOn (fun j : ℕ => x j - 1)
      (↑(Finset.range J) : Set ℕ) := by
    intro i hi j hj heq
    have hi' : i < J := by simpa using hi
    have hj' : j < J := by simpa using hj
    have hpi := (hbound i hi').1
    have hpj := (hbound j hj').1
    change x i - 1 = x j - 1 at heq
    apply hinj
    omega
  have hc : S.card = J := by
    dsimp [S]
    rw [Finset.card_image_of_injOn hi, Finset.card_range]
  have hs : S ⊆ Finset.range M := by
    intro y hy
    change y ∈ (Finset.range J).image (fun j => x j - 1) at hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have hi' : i < J := Finset.mem_range.mp hi
    have hb := hbound i hi'
    apply Finset.mem_range.mpr
    omega
  have hh := Finset.card_le_card hs
  rw [hc, Finset.card_range] at hh
  exact hh

/-- The finite arithmetic obstruction at an arbitrary polynomial degree d.
If the maximum record value M has growth bound M^(d+2) ≤ A*(K+1),
and the elapsed time is at most B*J*M^d with J ≤ M, then M is bounded
independently of the number of records. -/
theorem record_max_bound (d M J K A B : ℕ)
    (hM : 0 < M) (hJ : J ≤ M)
    (hK : K ≤ B * J * M ^ d)
    (hg : M ^ (d + 2) ≤ A * (K + 1)) : M ≤ A * (B + 1) := by
  have hp : 0 < M ^ (d + 1) := pow_pos hM _
  have hp1 : 1 ≤ M ^ (d + 1) := by omega
  have hK' : K ≤ B * M ^ (d + 1) := by
    calc
      K ≤ B * J * M ^ d := hK
      _ ≤ B * M * M ^ d :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left B hJ)
      _ = B * M ^ (d + 1) := by rw [pow_succ]; ring
  have hK'' : K + 1 ≤ (B + 1) * M ^ (d + 1) := by
    calc
      K + 1 ≤ B * M ^ (d + 1) + M ^ (d + 1) :=
        Nat.add_le_add hK' hp1
      _ = (B + 1) * M ^ (d + 1) := by ring
  have hh : M ^ (d + 2) ≤ A * ((B + 1) * M ^ (d + 1)) :=
    le_trans hg (Nat.mul_le_mul_left A hK'')
  by_contra hn
  have hlt : A * (B + 1) < M := lt_of_not_ge hn
  have hm := Nat.mul_lt_mul_of_pos_right hlt hp
  have hcontra : A * ((B + 1) * M ^ (d + 1)) < M ^ (d + 2) := by
    calc
      A * ((B + 1) * M ^ (d + 1)) =
          (A * (B + 1)) * M ^ (d + 1) := by ring
      _ < M * M ^ (d + 1) := hm
      _ = M ^ (d + 2) := by
        rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]
        ring
  exact (not_lt_of_ge hh) hcontra

/-- There cannot be arbitrarily many distinct positive records satisfying
both the polynomial time bound and the small-growth bound with fixed A,B.
All analytic and Collatz-specific assumptions are explicit. -/
theorem finite_record_obstruction (x : ℕ → ℕ) (d J M K A B : ℕ)
    (hinj : Function.Injective x) (hM : 0 < M)
    (hbound : ∀ j < J, 0 < x j ∧ x j ≤ M)
    (hK : K ≤ B * J * M ^ d)
    (hg : M ^ (d + 2) ≤ A * (K + 1)) : J ≤ A * (B + 1) := by
  have hJ := positive_record_count x J M hinj hbound
  exact le_trans hJ (record_max_bound d M J K A B hM hJ hK hg)

/-- A family of record prefixes with the above bounds cannot exist for
all positive record counts J. -/
theorem no_infinite_record_family (x : ℕ → ℕ) (d A B : ℕ)
    (hinj : Function.Injective x)
    (h : ∀ J : ℕ, 0 < J → ∃ M K : ℕ, 0 < M ∧
      (∀ j < J, 0 < x j ∧ x j ≤ M) ∧
      K ≤ B * J * M ^ d ∧ M ^ (d + 2) ≤ A * (K + 1)) : False := by
  let J := A * (B + 1) + 1
  have hJ : 0 < J := by dsimp [J]; omega
  obtain ⟨M, K, hM, hb, hK, hg⟩ := h J hJ
  have hc := finite_record_obstruction x d J M K A B hinj hM hb hK hg
  dsimp [J] at hc
  omega

#print axioms positive_record_count
#print axioms record_max_bound
#print axioms finite_record_obstruction
#print axioms no_infinite_record_family

end CollatzRunyan.UniversalStoppingResearch
