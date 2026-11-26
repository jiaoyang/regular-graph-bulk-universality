import GaussianWave.BS.InnovationGaussianBlocks

/-!
# Old internal vertices and the new leaf layer
-/
noncomputable section
namespace GaussianWave.BS

def oldNewStepEquiv {R A F O N : Type*} (e : F ≃ O ⊕ N) :
    (R ⊕ (A × F)) ≃ (R ⊕ (A × O)) ⊕ (A × N) where
  toFun := Sum.elim (fun r => Sum.inl (Sum.inl r))
    (fun af => Sum.elim (fun old => Sum.inl (Sum.inr (af.1, old)))
      (fun new => Sum.inr (af.1, new)) (e af.2))
  invFun := Sum.elim (Sum.elim Sum.inl (fun ao => Sum.inr (ao.1, e.symm (Sum.inl ao.2))))
    (fun an => Sum.inr (an.1, e.symm (Sum.inr an.2)))
  left_inv j := by
    cases j with
    | inl r => rfl
    | inr af =>
        cases h : e af.2 with
        | inl old =>
            simp only [Sum.elim_inr, h, Sum.elim_inl]
            rw [← h, Equiv.symm_apply_apply]
        | inr new =>
            simp only [Sum.elim_inr, h]
            rw [← h, Equiv.symm_apply_apply]
  right_inv j := by
    cases j with
    | inl old =>
        cases old with
        | inl r => rfl
        | inr ao => simp only [Sum.elim_inl, Sum.elim_inr, Equiv.apply_symm_apply]
    | inr an => simp only [Sum.elim_inr, Equiv.apply_symm_apply]

def branchInternalNodeSplit (q : ℕ) : (k : ℕ) →
    BranchInternalNode q (k + 1) ≃ BranchInternalNode q k ⊕ BranchLeaf q k
  | 0 =>
      { toFun := Sum.elim Sum.inr (fun aj => Empty.elim aj.2)
        invFun := Sum.elim Empty.elim Sum.inl
        left_inv := by intro j; cases j with
          | inl u => rfl
          | inr aj => exact Empty.elim aj.2
        right_inv := by intro j; cases j with
          | inl old => exact Empty.elim old
          | inr u => rfl }
  | k + 1 => oldNewStepEquiv (branchInternalNodeSplit q k)

/-- The node split is the same literal split as the old/new innovation
equivalence; the coordinate within each sibling block is preserved. -/
theorem branchInnovationSplit_node (m k : ℕ)
    (node : BranchInternalNode (m + 1) (k + 1)) (i : Fin m) :
    branchInnovationSplit m k ((branchInnovationNodeEquiv m (k + 1)).symm (node, i)) =
      Sum.elim (fun old => Sum.inl ((branchInnovationNodeEquiv m k).symm (old, i)))
        (fun leaf => Sum.inr (leaf, i)) (branchInternalNodeSplit (m + 1) k node) := by
  induction k with
  | zero =>
      cases node with
      | inl u => rfl
      | inr an => exact Empty.elim an.2
  | succ k ih =>
      cases node with
      | inl u => rfl
      | inr an =>
          change Sum.elim (fun old => Sum.inl (Sum.inr (an.1, old)))
            (fun new => Sum.inr ((an.1, new.1), new.2))
              (branchInnovationSplit m k ((branchInnovationNodeEquiv m (k + 1)).symm (an.2, i))) = _
          rw [ih an.2]
          have hnode : branchInternalNodeSplit (m + 1) (k + 1) (Sum.inr an) =
              Sum.elim (fun old => Sum.inl (Sum.inr (an.1, old))) (fun leaf => Sum.inr (an.1, leaf))
                (branchInternalNodeSplit (m + 1) k an.2) := rfl
          rw [hnode]
          cases h : branchInternalNodeSplit (m + 1) k an.2 with
          | inl old => rfl
          | inr leaf => rfl

end GaussianWave.BS
