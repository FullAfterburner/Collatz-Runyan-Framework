import ConjugateCoefficientRigidity

/-!
# Collatz–Runyan: Conjugate Cycle Rigidity

Cycle equations, divisibility and uniqueness for fixed obstruction and
correction. No claim that arbitrary affine candidates are genuine cycles.
Hypotheses are explicit; no physical interpretation is assumed.
-/

namespace CollatzRunyan.BinaryConjugation

def cycleObstruction (k a : ℕ) : ℤ := (2 : ℤ)^k - (3 : ℤ)^a

def CycleCandidate (k a : ℕ) (z c : ℤ) : Prop :=
  cycleObstruction k a * z = c

theorem cycleCandidate_neg_iff (k a : ℕ) (z c : ℤ) :
    CycleCandidate k a (-z) (-c) ↔ CycleCandidate k a z c := by
  unfold CycleCandidate
  rw [mul_neg]
  constructor <;> intro h <;> linarith

theorem cycleCandidate_unique (k a : ℕ) (z w c : ℤ)
    (hD : cycleObstruction k a ≠ 0)
    (hz : CycleCandidate k a z c) (hw : CycleCandidate k a w c) : z = w := by
  unfold CycleCandidate at hz hw
  have h : cycleObstruction k a * (z - w) = 0 := by
    rw [mul_sub, hz, hw, sub_self]
  rcases mul_eq_zero.mp h with hzero | hzero
  · exact (hD hzero).elim
  · exact sub_eq_zero.mp hzero

theorem cycleCandidate_exists_iff (k a : ℕ) (c : ℤ) :
    (∃ z : ℤ, CycleCandidate k a z c) ↔ cycleObstruction k a ∣ c := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩

theorem cycleDivisibility_conjugate (k a : ℕ) (c : ℤ) :
    cycleObstruction k a ∣ -c ↔ cycleObstruction k a ∣ c := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    calc
      c = -(-c) := by simp
      _ = -(cycleObstruction k a * z) := by rw [hz]
      _ = cycleObstruction k a * -z := by ring
  · rintro ⟨z, hz⟩
    exact ⟨-z, by rw [hz, mul_neg]⟩

theorem cycleObstruction_ne_zero (k a : ℕ) (hk : 0 < k) :
    cycleObstruction k a ≠ 0 := by
  intro h
  have heq : (2 : ℤ)^k = (3 : ℤ)^a := by
    unfold cycleObstruction at h
    exact sub_eq_zero.mp h
  have hmod : (2 : ℤ)^k % 2 = (3 : ℤ)^a % 2 :=
    congrArg (fun x : ℤ => x % 2) heq
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [pow_succ, Int.mul_emod] at hmod
  have hodd : ∀ b : ℕ, (3 : ℤ)^b % 2 = 1 := by
    intro b
    induction b with
    | zero => norm_num
    | succ b ih => rw [pow_succ, Int.mul_emod, ih]; norm_num
  rw [hodd] at hmod
  simp at hmod

theorem actualCycle_candidate (k a : ℕ) (s : State)
    (h : evolve k s = s) :
    CycleCandidate k a (signed s) (correction k a s) := by
  exact (affine_cycle_iff k a s _ h).mp (affine_correction k a s)

theorem actualCycle_conjugate_candidate (k a : ℕ) (s : State)
    (h : evolve k s = s) :
    CycleCandidate k a (signed (conjugate s)) (-correction k a s) := by
  rw [signed_conjugate]
  exact (cycleCandidate_neg_iff k a _ _).mpr (actualCycle_candidate k a s h)

theorem actualCycle_signed_unique (k a : ℕ) (s t : State)
    (hk : 0 < k) (hs : evolve k s = s) (ht : evolve k t = t)
    (hc : correction k a s = correction k a t) : signed s = signed t := by
  apply cycleCandidate_unique k a _ _ (correction k a s) (cycleObstruction_ne_zero k a hk)
  · exact actualCycle_candidate k a s hs
  · rw [hc]
    exact actualCycle_candidate k a t ht

theorem exactCycle_conjugate_with_candidate (p a : ℕ) (s : State)
    (h : ExactPeriod p s) :
    ExactPeriod p (conjugate s) ∧
      CycleCandidate p a (signed (conjugate s)) (-correction p a s) := by
  exact ⟨(exactPeriod_conjugate p s).mpr h,
    actualCycle_conjugate_candidate p a s h.2.1⟩

example : CycleCandidate 2 1 1 1 := by norm_num [CycleCandidate, cycleObstruction]
example : CycleCandidate 2 1 (-1) (-1) := by norm_num [CycleCandidate, cycleObstruction]

end CollatzRunyan.BinaryConjugation
