import GaussianWave.BS.UniformTreeCoverLaw
import GaussianWave.BS.BranchFamilyActions

/-! Reindexing the actual uniform local permutations proves finite cover
invariance under the faithful branch stabilizer action. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

theorem branchGraphCover_mul {N m : ℕ} (G : RegularGraph N (m+2))
    (k : ℕ) {parent root : Fin N} (h : G.val.Adj parent root)
    (g a : BranchCoverOrdering (m+1) k) (v : BranchVertex (m+1) k) :
    branchGraphCover G k h (g*a) v =
      branchGraphCover G k h g (branchAutomorphism (m+1) k a v) := by
  induction k generalizing parent root with
  | zero => rfl
  | succ k ih =>
    cases v with
    | inl u => rfl
    | inr av =>
      exact ih (graphForwardNeighbor_adj G h (g.1 (a.1 av.1)))
        (g.2 (a.1 av.1)) (a.2 av.1) av.2

def vertexCoverSeedBranchEquiv (N m k : ℕ) (g : VertexBallStabilizer (m+2) k) :
    Equiv.Perm (VertexCoverSeed N m k) where
  toFun := fun z => (z.1,z.2.1,fun a =>
    @Mul.mul (BranchCoverOrdering (m+1) k) inferInstance (z.2.2 a) (g a))
  invFun := fun z => (z.1,z.2.1,fun a =>
    @Mul.mul (BranchCoverOrdering (m+1) k) inferInstance (z.2.2 a)
      (@Inv.inv (BranchCoverOrdering (m+1) k) inferInstance (g a)))
  left_inv := by
    rintro ⟨v,σ,h⟩
    exact Prod.ext rfl (Prod.ext rfl (funext (fun a => mul_inv_cancel_right (h a) (g a))))
  right_inv := by
    rintro ⟨v,σ,h⟩
    exact Prod.ext rfl (Prod.ext rfl (funext (fun a => inv_mul_cancel_right (h a) (g a))))

theorem vertexGraphCover_branch_reindex {N m : ℕ} (G : RegularGraph N (m+2))
    (k : ℕ) (g : VertexBallStabilizer (m+2) k) (seed : VertexCoverSeed N m k)
    (v : VertexBallVertex (m+2) k) :
    vertexGraphCover G k (vertexCoverSeedBranchEquiv N m k g seed) v =
      vertexGraphCover G k seed (g • v) := by
  cases v with
  | inl u => rfl
  | inr av =>
    change branchGraphCover G k _
      (@Mul.mul (BranchCoverOrdering (m+1) k) inferInstance (seed.2.2 av.1) (g av.1)) av.2 =
      branchGraphCover G k _ (seed.2.2 av.1) (branchAutomorphism (m+1) k (g av.1) av.2)
    exact branchGraphCover_mul G k
      (canonicalPortLabeling G seed.1 (seed.2.1 av.1)).property (seed.2.2 av.1) (g av.1) av.2

theorem finiteVertexCoverImageLaw_branch_invariant {N m : ℕ} (G : RegularGraph N (m+2))
    (k : ℕ) (g : VertexBallStabilizer (m+2) k) :
    Measure.map (fun x : VertexBallVertex (m+2) k → Fin N => fun v => x (g • v))
      (finiteVertexCoverImageLaw G k) = finiteVertexCoverImageLaw G k := by
  rw [finiteVertexCoverImageLaw, uniformAtomicLaw_map _ _
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))]
  have he : (fun x : VertexBallVertex (m+2) k → Fin N => fun v => x (g • v)) ∘
      vertexGraphCover G k = vertexGraphCover G k ∘ vertexCoverSeedBranchEquiv N m k g := by
    funext seed v
    exact (vertexGraphCover_branch_reindex G k g seed v).symm
  rw [he, uniformAtomicLaw_reindex]

end GaussianWave.BS
