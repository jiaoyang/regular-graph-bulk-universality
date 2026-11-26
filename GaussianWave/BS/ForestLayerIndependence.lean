import GaussianWave.BS.ReferenceLayerProduct

/-!
# Actual independence of the new Gaussian innovation layer

This is a measure identity for the explicitly constructed reference law.  No
independence or Markov property of that reference law is an input.
-/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

def forestInnovationSplitCoordinates (A : Type*) (m k : ℕ)
    (x : ForestInnovation A m (k + 1) → ℝ) :
    (ForestInnovation A m k → ℝ) × (A → NewBranchInnovation m k → ℝ) :=
  (fun j => x ((forestInnovationSplit A m k).symm (Sum.inl j)),
    fun a j => x ((forestInnovationSplit A m k).symm (Sum.inr (a, j))))

theorem measurable_forestInnovationSplitCoordinates (A : Type*) (m k : ℕ) :
    Measurable (forestInnovationSplitCoordinates A m k) := by
  apply Measurable.prodMk
  · exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  · exact measurable_pi_lambda _ (fun _ => measurable_pi_lambda _ (fun _ => measurable_pi_apply _))

def forestNodeLayerPartition (A : Type*) (m k : ℕ)
    (p : (A → ℝ) × ((A × BranchInternalNode (m + 1) (k + 1)) → Fin m → ℝ)) :
    ((A → ℝ) × ((A × BranchInternalNode (m + 1) k) → Fin m → ℝ)) ×
      ((A × BranchLeaf (m + 1) k) → Fin m → ℝ) :=
  ((p.1, fun an => p.2 ((forestNodePartitionEquiv A m k).symm (Sum.inl an))),
    fun al => p.2 ((forestNodePartitionEquiv A m k).symm (Sum.inr al)))

theorem measurable_forestNodeLayerPartition (A : Type*) (m k : ℕ) :
    Measurable (forestNodeLayerPartition A m k) := by
  unfold forestNodeLayerPartition
  fun_prop

theorem measurable_newLayerDecode (A : Type*) (m k : ℕ) :
    Measurable (newLayerDecode A m k) := by
  exact measurable_pi_lambda _ (fun _ => measurable_pi_lambda _ (fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)))

theorem forestInnovationSplitCoordinates_decode (A : Type*) (m k : ℕ)
    (p : (A → ℝ) × ((A × BranchInternalNode (m + 1) (k + 1)) → Fin m → ℝ)) :
    forestInnovationSplitCoordinates A m k (forestNodeDecode A m (k + 1) p) =
      Prod.map (forestNodeDecode A m k) (newLayerDecode A m k)
        (forestNodeLayerPartition A m k p) := by
  apply Prod.ext
  · funext j
    cases j with
    | inl a => rfl
    | inr aj =>
      change forestNodeDecode A m (k + 1) p
          (Sum.inr (aj.1, (branchInnovationSplit m k).symm (Sum.inl aj.2))) = _
      have hj : aj.2 = (branchInnovationNodeEquiv m k).symm
          (branchInnovationNodeEquiv m k aj.2) :=
        ((branchInnovationNodeEquiv m k).symm_apply_apply aj.2).symm
      rw [hj, branchInnovationSplit_symm_node_old]
      simp [forestNodeDecode, forestNodeLayerPartition]
  · funext a j
    rcases j with ⟨leaf, i⟩
    change forestNodeDecode A m (k + 1) p
      (Sum.inr (a, (branchInnovationSplit m k).symm (Sum.inr (leaf, i)))) = _
    rw [branchInnovationSplit_symm_node_new]
    simp [forestNodeDecode, forestNodeLayerPartition, newLayerDecode]

theorem forestNodeLayerPartition_law {A : Type*} [Fintype A] [DecidableEq A]
    (m k : ℕ) (scale : ℝ) (R : Matrix A A ℝ) :
    Measure.map (forestNodeLayerPartition A m k)
      ((linearImageGaussian R).prod (Measure.pi
        (fun _ : A × BranchInternalNode (m + 1) (k + 1) => siblingInnovationGaussian m scale))) =
      ((linearImageGaussian R).prod (Measure.pi
        (fun _ : A × BranchInternalNode (m + 1) k => siblingInnovationGaussian m scale))).prod
          (Measure.pi (fun _ : A × BranchLeaf (m + 1) k => siblingInnovationGaussian m scale)) :=
  root_product_partition (forestNodePartitionEquiv A m k) (linearImageGaussian R)
    (siblingInnovationGaussian m scale)

/-- The literal previous innovation vector and all new branch blocks are
independent under the actual finite Gaussian reference. -/
theorem forestGaussianInnovationLaw_split {A : Type*} [Fintype A] [DecidableEq A]
    (m k : ℕ) (scale : ℝ) (R : Matrix A A ℝ) :
    Measure.map (forestInnovationSplitCoordinates A m k)
      (forestGaussianInnovationLaw m (k + 1) scale R) =
      (forestGaussianInnovationLaw m k scale R).prod
        (Measure.pi (fun _ : A => newBranchGaussianLaw m k scale)) := by
  rw [forestGaussianInnovationLaw_eq_decoded_product]
  rw [Measure.map_map (measurable_forestInnovationSplitCoordinates A m k)
    (measurable_forestNodeDecode A m (k + 1))]
  have hcomp : forestInnovationSplitCoordinates A m k ∘ forestNodeDecode A m (k + 1) =
      (Prod.map (forestNodeDecode A m k) (newLayerDecode A m k)) ∘
        forestNodeLayerPartition A m k := funext (forestInnovationSplitCoordinates_decode A m k)
  rw [hcomp, ← Measure.map_map
    ((measurable_forestNodeDecode A m k).prodMap (measurable_newLayerDecode A m k))
    (measurable_forestNodeLayerPartition A m k), forestNodeLayerPartition_law]
  rw [← Measure.map_prod_map]
  · rw [← forestGaussianInnovationLaw_eq_decoded_product, newLayerDecode_law]
  · exact measurable_forestNodeDecode A m k
  · exact measurable_newLayerDecode A m k

end GaussianWave.BS
