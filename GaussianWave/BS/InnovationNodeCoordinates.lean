import GaussianWave.BS.LocalVertexChart

/-!
# Literal internal-node labels for every sibling-innovation block
-/
noncomputable section
namespace GaussianWave.BS

def BranchInternalNode (q : ℕ) : ℕ → Type
  | 0 => Empty
  | k + 1 => Unit ⊕ (Fin q × BranchInternalNode q k)

instance branchInternalNodeFintype (q k : ℕ) : Fintype (BranchInternalNode q k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ k ih => letI := ih; exact inferInstanceAs (Fintype (Unit ⊕ (Fin q × BranchInternalNode q k)))

instance branchInternalNodeDecidableEq (q k : ℕ) : DecidableEq (BranchInternalNode q k) := Classical.decEq _

def nodeBlockStepEquiv {A J F N : Type*} (e : F ≃ N × J) :
    (J ⊕ (A × F)) ≃ (Unit ⊕ (A × N)) × J where
  toFun := Sum.elim (fun j => (Sum.inl (), j))
    (fun af => (Sum.inr (af.1, (e af.2).1), (e af.2).2))
  invFun nj := Sum.elim (fun _ => Sum.inl nj.2)
    (fun an => Sum.inr (an.1, e.symm (an.2, nj.2))) nj.1
  left_inv j := by
    cases j with
    | inl i => rfl
    | inr af => simp only [Sum.elim_inr, Equiv.symm_apply_apply, Prod.mk.eta]
  right_inv nj := by
    rcases nj with ⟨node, j⟩
    cases node with
    | inl u => cases u; rfl
    | inr an => simp only [Sum.elim_inr, Equiv.apply_symm_apply]

def branchInnovationNodeEquiv (m : ℕ) : (k : ℕ) →
    BranchInnovation (m + 1) k ≃ BranchInternalNode (m + 1) k × Fin m
  | 0 => Equiv.equivOfIsEmpty Empty (Empty × Fin m)
  | k + 1 => nodeBlockStepEquiv (branchInnovationNodeEquiv m k)

def branchNoiseNodeEquiv (q : ℕ) : (k : ℕ) → BranchNoise q k ≃ BranchInternalNode q k × Fin q
  | 0 => Equiv.equivOfIsEmpty Empty (Empty × Fin q)
  | k + 1 => nodeBlockStepEquiv (branchNoiseNodeEquiv q k)

/-- Each raw innovation uses only the independent Gaussian vector attached
to its own internal vertex. -/
theorem branchNoiseInnovation_at_node (m k : ℕ) (scale : ℝ)
    (z : BranchNoise (m + 1) k → ℝ) (node : BranchInternalNode (m + 1) k) (i : Fin m) :
    branchNoiseInnovation m k scale z ((branchInnovationNodeEquiv m k).symm (node, i)) =
      scale * (z ((branchNoiseNodeEquiv (m + 1) k).symm (node, i.succ)) -
        z ((branchNoiseNodeEquiv (m + 1) k).symm (node, 0))) := by
  induction k with
  | zero => exact Empty.elim node
  | succ k ih =>
      cases node with
      | inl u => cases u; rfl
      | inr an => exact ih (fun j => z (Sum.inr (an.1, j))) an.2

end GaussianWave.BS
