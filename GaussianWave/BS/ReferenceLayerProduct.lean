import GaussianWave.BS.ForestReferenceProductCoordinates

/-!
# Genuine product law of each new Gaussian innovation layer
-/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

def curryBlocksEquiv (A B X : Type*) [MeasurableSpace X] : ((A × B) → X) ≃ᵐ (A → B → X) where
  toEquiv := Equiv.curry A B X
  measurable_toFun := by
    apply measurable_pi_lambda
    intro a
    apply measurable_pi_lambda
    intro b
    exact measurable_pi_apply (a, b)
  measurable_invFun := measurable_uncurryBlocks

theorem measurePreserving_curryBlocks {A B X : Type*} [Fintype A] [Fintype B] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (curryBlocksEquiv A B X) (Measure.pi (fun _ : A × B => μ))
      (Measure.pi (fun _ : A => Measure.pi (fun _ : B => μ))) := by
  have h : MeasurePreserving (curryBlocksEquiv A B X).symm
      (Measure.pi (fun _ : A => Measure.pi (fun _ : B => μ)))
      (Measure.pi (fun _ : A × B => μ)) :=
    ⟨(curryBlocksEquiv A B X).symm.measurable, pi_uncurryBlocks (fun _ _ => μ)⟩
  exact h.symm

def newBranchGaussianLaw (m k : ℕ) (scale : ℝ) : Measure (NewBranchInnovation m k → ℝ) :=
  Measure.map flattenChannels (Measure.pi (fun _ : BranchLeaf (m + 1) k => siblingInnovationGaussian m scale))

instance newBranchGaussianLaw_probability (m k : ℕ) (scale : ℝ) :
    IsProbabilityMeasure (newBranchGaussianLaw m k scale) := by
  unfold newBranchGaussianLaw
  letI : IsProbabilityMeasure (Measure.pi
      (fun _ : BranchLeaf (m + 1) k => siblingInnovationGaussian m scale)) :=
    Measure.pi.instIsProbabilityMeasure _
  exact isProbabilityMeasure_map
    (measurable_flattenChannels (κ := BranchLeaf (m + 1) k) (ι := Fin m)).aemeasurable

def newLayerDecode (A : Type*) (m k : ℕ)
    (f : (A × BranchLeaf (m + 1) k) → Fin m → ℝ) : A → NewBranchInnovation m k → ℝ :=
  fun a ni => f (a, ni.1) ni.2

theorem newLayerDecode_law (A : Type*) [Fintype A] (m k : ℕ) (scale : ℝ) :
    Measure.map (newLayerDecode A m k)
      (Measure.pi (fun _ : A × BranchLeaf (m + 1) k => siblingInnovationGaussian m scale)) =
      Measure.pi (fun _ : A => newBranchGaussianLaw m k scale) := by
  have hc := measurePreserving_curryBlocks (A := A) (B := BranchLeaf (m + 1) k)
    (siblingInnovationGaussian m scale)
  have hf := measurePreserving_pi
    (fun _ : A => Measure.pi (fun _ : BranchLeaf (m + 1) k => siblingInnovationGaussian m scale))
    (fun _ : A => newBranchGaussianLaw m k scale)
    (f := fun _ => flattenChannels) (fun _ =>
      (show MeasurePreserving flattenChannels
        (Measure.pi (fun _ : BranchLeaf (m + 1) k => siblingInnovationGaussian m scale))
        (newBranchGaussianLaw m k scale) from ⟨measurable_flattenChannels, rfl⟩))
  exact (hf.comp hc).map_eq

def forestNodePartitionEquiv (A : Type*) (m k : ℕ) :
    (A × BranchInternalNode (m + 1) (k + 1)) ≃
      (A × BranchInternalNode (m + 1) k) ⊕ (A × BranchLeaf (m + 1) k) :=
  (Equiv.prodCongr (Equiv.refl A) (branchInternalNodeSplit (m + 1) k)).trans
    (Equiv.prodSumDistrib A (BranchInternalNode (m + 1) k) (BranchLeaf (m + 1) k))

@[simp] theorem forestNodePartitionEquiv_symm_old (A : Type*) (m k : ℕ)
    (an : A × BranchInternalNode (m + 1) k) :
    (forestNodePartitionEquiv A m k).symm (Sum.inl an) =
      (an.1, (branchInternalNodeSplit (m + 1) k).symm (Sum.inl an.2)) := rfl

@[simp] theorem forestNodePartitionEquiv_symm_new (A : Type*) (m k : ℕ)
    (al : A × BranchLeaf (m + 1) k) :
    (forestNodePartitionEquiv A m k).symm (Sum.inr al) =
      (al.1, (branchInternalNodeSplit (m + 1) k).symm (Sum.inr al.2)) := rfl

theorem branchInnovationSplit_symm_node_old (m k : ℕ)
    (node : BranchInternalNode (m + 1) k) (i : Fin m) :
    (branchInnovationSplit m k).symm (Sum.inl ((branchInnovationNodeEquiv m k).symm (node, i))) =
      (branchInnovationNodeEquiv m (k + 1)).symm
        ((branchInternalNodeSplit (m + 1) k).symm (Sum.inl node), i) := by
  apply (branchInnovationSplit m k).injective
  rw [Equiv.apply_symm_apply, branchInnovationSplit_node, Equiv.apply_symm_apply]
  rfl

theorem branchInnovationSplit_symm_node_new (m k : ℕ)
    (leaf : BranchLeaf (m + 1) k) (i : Fin m) :
    (branchInnovationSplit m k).symm (Sum.inr (leaf, i)) =
      (branchInnovationNodeEquiv m (k + 1)).symm
        ((branchInternalNodeSplit (m + 1) k).symm (Sum.inr leaf), i) := by
  apply (branchInnovationSplit m k).injective
  rw [Equiv.apply_symm_apply, branchInnovationSplit_node, Equiv.apply_symm_apply]
  rfl

end GaussianWave.BS
