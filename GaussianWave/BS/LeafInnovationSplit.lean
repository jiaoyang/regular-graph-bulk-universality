import GaussianWave.BS.GaussianBallConsistency

/-!
# Actual old/new innovation-coordinate splitting

The final innovation layer is indexed by the leaves of the previous branch.
The constructed equivalences retain exactly the literal earlier coordinates.
They provide the common core and disjoint extension blocks used by SSA.
-/
noncomputable section
namespace GaussianWave.BS

def BranchLeaf (q : ℕ) : ℕ → Type
  | 0 => Unit
  | k + 1 => Fin q × BranchLeaf q k

instance branchLeafFintype (q k : ℕ) : Fintype (BranchLeaf q k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k ih => letI := ih; exact inferInstanceAs (Fintype (Fin q × BranchLeaf q k))

instance branchLeafDecidableEq (q k : ℕ) : DecidableEq (BranchLeaf q k) := Classical.decEq _

theorem card_branchLeaf (q k : ℕ) : Fintype.card (BranchLeaf q k) = q ^ k := by
  induction k with
  | zero => simp [BranchLeaf]
  | succ k ih => simp [BranchLeaf, Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

abbrev NewBranchInnovation (m k : ℕ) := BranchLeaf (m + 1) k × Fin m

def branchInnovationSplitTo (m : ℕ) : (k : ℕ) → BranchInnovation (m + 1) (k + 1) →
    BranchInnovation (m + 1) k ⊕ NewBranchInnovation m k
  | 0, j => Sum.elim (fun i => Sum.inr ((), i)) (fun aj => Empty.elim aj.2) j
  | k + 1, j => Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun aj =>
      Sum.elim (fun old => Sum.inl (Sum.inr (aj.1, old)))
        (fun new => Sum.inr ((aj.1, new.1), new.2)) (branchInnovationSplitTo m k aj.2)) j

def branchInnovationSplitFrom (m : ℕ) : (k : ℕ) →
    (BranchInnovation (m + 1) k ⊕ NewBranchInnovation m k) → BranchInnovation (m + 1) (k + 1)
  | 0, j => Sum.elim Empty.elim (fun new => Sum.inl new.2) j
  | k + 1, j => Sum.elim
      (Sum.elim (fun i => Sum.inl i) (fun aj => Sum.inr (aj.1, branchInnovationSplitFrom m k (Sum.inl aj.2))))
      (fun new => Sum.inr (new.1.1, branchInnovationSplitFrom m k (Sum.inr (new.1.2, new.2)))) j

theorem branchInnovationSplit_inverse (m k : ℕ) :
    Function.LeftInverse (branchInnovationSplitFrom m k) (branchInnovationSplitTo m k) ∧
      Function.RightInverse (branchInnovationSplitFrom m k) (branchInnovationSplitTo m k) := by
  induction k with
  | zero =>
      constructor
      · intro j
        cases j with
        | inl i => rfl
        | inr aj => exact Empty.elim aj.2
      · intro j
        cases j with
        | inl old => exact Empty.elim old
        | inr new => rcases new with ⟨u, i⟩; cases u; rfl
  | succ k ih =>
      constructor
      · intro j
        cases j with
        | inl i => rfl
        | inr aj =>
            cases h : branchInnovationSplitTo m k aj.2 with
            | inl old =>
                simp only [branchInnovationSplitTo, Sum.elim_inr, h, Sum.elim_inl,
                  branchInnovationSplitFrom]
                rw [← h, ih.1 aj.2]
            | inr new =>
                simp only [branchInnovationSplitTo, Sum.elim_inr, h, branchInnovationSplitFrom]
                rw [← h, ih.1 aj.2]
      · intro j
        cases j with
        | inl old =>
            cases old with
            | inl i => rfl
            | inr aj =>
                change Sum.elim (fun old => Sum.inl (Sum.inr (aj.1, old)))
                  (fun new => Sum.inr ((aj.1, new.1), new.2))
                    (branchInnovationSplitTo m k (branchInnovationSplitFrom m k (Sum.inl aj.2))) = _
                rw [ih.2 (Sum.inl aj.2)]
                rfl
        | inr new =>
            change Sum.elim (fun old => Sum.inl (Sum.inr (new.1.1, old)))
              (fun new' => Sum.inr ((new.1.1, new'.1), new'.2))
                (branchInnovationSplitTo m k (branchInnovationSplitFrom m k (Sum.inr (new.1.2, new.2)))) = _
            rw [ih.2 (Sum.inr (new.1.2, new.2))]
            rfl

def branchInnovationSplit (m k : ℕ) :
    BranchInnovation (m + 1) (k + 1) ≃ BranchInnovation (m + 1) k ⊕ NewBranchInnovation m k where
  toFun := branchInnovationSplitTo m k
  invFun := branchInnovationSplitFrom m k
  left_inv := (branchInnovationSplit_inverse m k).1
  right_inv := (branchInnovationSplit_inverse m k).2

theorem branchInnovationSplit_old (m k : ℕ) (j : BranchInnovation (m + 1) k) :
    branchInnovationSplit m k (branchInnovationInclusion (m + 1) k j) = Sum.inl j := by
  induction k with
  | zero => exact Empty.elim j
  | succ k ih =>
      cases j with
      | inl i => rfl
      | inr aj =>
          change Sum.elim (fun old => Sum.inl (Sum.inr (aj.1, old)))
            (fun new => Sum.inr ((aj.1, new.1), new.2))
              (branchInnovationSplit m k (branchInnovationInclusion (m + 1) k aj.2)) = _
          rw [ih aj.2]
          rfl

def forestInnovationSplitTo (A : Type*) (m k : ℕ)
    (j : A ⊕ (A × BranchInnovation (m + 1) (k + 1))) :
    (A ⊕ (A × BranchInnovation (m + 1) k)) ⊕ (A × NewBranchInnovation m k) :=
  Sum.elim (fun a => Sum.inl (Sum.inl a))
    (fun aj => Sum.elim (fun old => Sum.inl (Sum.inr (aj.1, old)))
      (fun new => Sum.inr (aj.1, new)) (branchInnovationSplit m k aj.2)) j

def forestInnovationSplitFrom (A : Type*) (m k : ℕ)
    (j : (A ⊕ (A × BranchInnovation (m + 1) k)) ⊕ (A × NewBranchInnovation m k)) :
    A ⊕ (A × BranchInnovation (m + 1) (k + 1)) :=
  Sum.elim (Sum.elim Sum.inl (fun aj => Sum.inr (aj.1, (branchInnovationSplit m k).symm (Sum.inl aj.2))))
    (fun an => Sum.inr (an.1, (branchInnovationSplit m k).symm (Sum.inr an.2))) j

def forestInnovationSplit (A : Type*) (m k : ℕ) :
    (A ⊕ (A × BranchInnovation (m + 1) (k + 1))) ≃
      (A ⊕ (A × BranchInnovation (m + 1) k)) ⊕ (A × NewBranchInnovation m k) where
  toFun := forestInnovationSplitTo A m k
  invFun := forestInnovationSplitFrom A m k
  left_inv j := by
    cases j with
    | inl a => rfl
    | inr aj =>
        cases h : branchInnovationSplit m k aj.2 with
        | inl old =>
            simp only [forestInnovationSplitTo, Sum.elim_inr, h, Sum.elim_inl,
              forestInnovationSplitFrom]
            rw [← h, Equiv.symm_apply_apply]
        | inr new =>
            simp only [forestInnovationSplitTo, Sum.elim_inr, h, forestInnovationSplitFrom]
            rw [← h, Equiv.symm_apply_apply]
  right_inv j := by
    cases j with
    | inl old =>
        cases old with
        | inl a => rfl
        | inr aj =>
            change Sum.elim (fun old => Sum.inl (Sum.inr (aj.1, old)))
              (fun new => Sum.inr (aj.1, new))
                (branchInnovationSplit m k ((branchInnovationSplit m k).symm (Sum.inl aj.2))) = _
            rw [Equiv.apply_symm_apply]
            rfl
    | inr an =>
        change Sum.elim (fun old => Sum.inl (Sum.inr (an.1, old))) (fun new => Sum.inr (an.1, new))
          (branchInnovationSplit m k ((branchInnovationSplit m k).symm (Sum.inr an.2))) = _
        rw [Equiv.apply_symm_apply]
        rfl

abbrev vertexInnovationSplit (m k : ℕ) := forestInnovationSplit (Fin (m + 2)) m k
abbrev edgeInnovationSplit (m k : ℕ) := forestInnovationSplit Bool m k

end GaussianWave.BS
