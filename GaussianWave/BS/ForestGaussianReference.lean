import GaussianWave.BS.GaussianSumProduct

/-!
# Actual root Gaussian times independent internal-node innovations
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def forestNodeEquiv (A : Type*) {F N J : Type*} (e : F ≃ N × J) :
    (A ⊕ (A × F)) ≃ A ⊕ ((A × N) × J) where
  toFun := Sum.elim Sum.inl (fun af => Sum.inr ((af.1, (e af.2).1), (e af.2).2))
  invFun := Sum.elim Sum.inl (fun anj => Sum.inr (anj.1.1, e.symm (anj.1.2, anj.2)))
  left_inv j := by
    cases j with
    | inl a => rfl
    | inr af => simp only [Sum.elim_inr, Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv j := by
    cases j with
    | inl a => rfl
    | inr anj => simp only [Sum.elim_inr, Equiv.apply_symm_apply, Prod.mk.eta]

def forestGaussianInnovation {A : Type*} [Fintype A] (m k : ℕ) (scale : ℝ) (R : Matrix A A ℝ) :
    ((A ⊕ (A × BranchNoise (m + 1) k)) → ℝ) →ₗ[ℝ] (ForestInnovation A m k → ℝ) where
  toFun z := Sum.elim (R.mulVec (fun a => z (Sum.inl a)))
    (fun aj => branchNoiseInnovation m k scale (fun j => z (Sum.inr (aj.1, j))) aj.2)
  map_add' z w := by
    ext j
    cases j with
    | inl a => exact congrFun (R.mulVecLin.map_add _ _) a
    | inr aj => exact congrFun (branchNoiseInnovation_add m k scale _ _) aj.2
  map_smul' r z := by
    ext j
    cases j with
    | inl a => exact congrFun (R.mulVecLin.map_smul r _) a
    | inr aj => exact congrFun (branchNoiseInnovation_smul m k scale r _) aj.2

def forestGaussianInnovationLaw {A : Type*} [Fintype A] (m k : ℕ) (scale : ℝ) (R : Matrix A A ℝ) :
    Measure (ForestInnovation A m k → ℝ) :=
  Measure.map (forestGaussianInnovation m k scale R) (standardVector (A ⊕ (A × BranchNoise (m + 1) k)))

instance forestGaussianInnovationLaw_probability {A : Type*} [Fintype A] (m k : ℕ) (scale : ℝ) (R : Matrix A A ℝ) :
    IsProbabilityMeasure (forestGaussianInnovationLaw m k scale R) :=
  isProbabilityMeasure_map (forestGaussianInnovation m k scale R).continuous_of_finiteDimensional.measurable.aemeasurable

theorem diagonalBlockFactor_mulVec_inl {I J A B : Type*} [Fintype I] [Fintype J]
    (R : Matrix A I ℝ) (L : Matrix B J ℝ) (z : I ⊕ J → ℝ) (a : A) :
    (Matrix.fromBlocks R 0 0 L).mulVec z (Sum.inl a) = R.mulVec (fun i => z (Sum.inl i)) a := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem diagonalBlockFactor_mulVec_inr {I J A B : Type*} [Fintype I] [Fintype J]
    (R : Matrix A I ℝ) (L : Matrix B J ℝ) (z : I ⊕ J → ℝ) (b : B) :
    (Matrix.fromBlocks R 0 0 L).mulVec z (Sum.inr b) = L.mulVec (fun j => z (Sum.inr j)) b := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem forestGaussianInnovation_node_factor {A : Type*} [Fintype A] [DecidableEq A]
    (m k : ℕ) (scale : ℝ) (R : Matrix A A ℝ) :
    Measure.map (fun x => fun j => x ((forestNodeEquiv A (branchInnovationNodeEquiv m k)).symm j))
      (forestGaussianInnovationLaw m k scale R) =
      linearImageGaussian (Matrix.fromBlocks R 0 0
        (independentBlockFactor (A := A × BranchInternalNode (m + 1) k) (rawSiblingFactor m scale))) := by
  let eN := forestNodeEquiv A (branchNoiseNodeEquiv (m + 1) k)
  let eI := forestNodeEquiv A (branchInnovationNodeEquiv m k)
  let L := independentBlockFactor (A := A × BranchInternalNode (m + 1) k) (rawSiblingFactor m scale)
  let M := Matrix.fromBlocks R 0 0 L
  unfold forestGaussianInnovationLaw
  rw [Measure.map_map (by fun_prop)
    (forestGaussianInnovation m k scale R).continuous_of_finiteDimensional.measurable]
  have hf : (fun z : (A ⊕ (A × BranchNoise (m + 1) k)) → ℝ => fun j =>
      forestGaussianInnovation m k scale R z (eI.symm j)) =
      (fun z => M.mulVec (fun j => z (eN.symm j))) := by
    funext z j
    cases j with
    | inl a =>
        rw [diagonalBlockFactor_mulVec_inl]
        rfl
    | inr ani =>
        rw [diagonalBlockFactor_mulVec_inr, independentBlockFactor_mulVec, rawSiblingFactor_mulVec]
        exact branchNoiseInnovation_at_node m k scale (fun j => z (Sum.inr (ani.1.1, j))) ani.1.2 ani.2
  change Measure.map (fun z => fun j => forestGaussianInnovation m k scale R z (eI.symm j)) _ = _
  rw [hf]
  change Measure.map (M.mulVec ∘
    (fun z : (A ⊕ (A × BranchNoise (m + 1) k)) → ℝ => fun j => z (eN.symm j))) _ = _
  rw [← Measure.map_map (measurable_finiteMatrixAction M) (by fun_prop),
    standardVector_map_coordinateRestriction _ eN.symm.injective]
  rfl

/-- The actual reference root law is independent of every sibling block;
all sibling blocks at distinct internal vertices are independent. -/
theorem forestGaussianInnovation_node_product {A : Type*} [Fintype A] [DecidableEq A]
    (m k : ℕ) (scale : ℝ) (R : Matrix A A ℝ) :
    Measure.map (fun x => fun j => x ((forestNodeEquiv A (branchInnovationNodeEquiv m k)).symm j))
      (forestGaussianInnovationLaw m k scale R) =
      sumVectorProductLaw (linearImageGaussian R)
        (Measure.map flattenChannels (Measure.pi (fun _ : A × BranchInternalNode (m + 1) k =>
          siblingInnovationGaussian m scale))) := by
  rw [forestGaussianInnovation_node_factor, linearImageGaussian_diagonalBlocks,
    independentBlockFactor_gaussian_product]
  rfl

def vertexRootInnovationFactor (m : ℕ) (energy : ℝ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  fun a j => physicalStarMatrix (m + 2) (energy / (m + 2)) a.succ j -
    physicalStarMatrix (m + 2) (energy / (m + 2)) 0 j

theorem vertexRootInnovationFactor_mulVec (m : ℕ) (energy : ℝ) (z : Fin (m + 2) → ℝ) (a : Fin (m + 2)) :
    (vertexRootInnovationFactor m energy).mulVec z a =
      physicalStarMap (m + 2) (energy / (m + 2)) z a.succ - physicalStarMap (m + 2) (energy / (m + 2)) z 0 := by
  simp only [vertexRootInnovationFactor, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
  rfl

theorem vertexGaussianInnovation_eq_forest (m k : ℕ) (energy : ℝ) :
    vertexGaussianInnovationLinear m k energy =
      forestGaussianInnovation m k (Real.sqrt (siblingVariance (m + 2) energy)) (vertexRootInnovationFactor m energy) := by
  ext z j
  cases j with
  | inl a => exact (vertexRootInnovationFactor_mulVec m energy _ a).symm
  | inr aj => rfl

theorem edgeGaussianInnovation_eq_forest (m k : ℕ) (energy : ℝ) :
    edgeGaussianInnovationLinear m k energy =
      forestGaussianInnovation m k (Real.sqrt (siblingVariance (m + 2) energy))
        (physicalEdgeMatrix (energy / (m + 2))) := by
  ext z j
  cases j <;> rfl

theorem forest_vertex_reference_physical_law (m k : ℕ) (energy : ℝ) :
    Measure.map (vertexBallBuildLinear m k energy)
      (forestGaussianInnovationLaw m k (Real.sqrt (siblingVariance (m + 2) energy)) (vertexRootInnovationFactor m energy)) =
      vertexGaussianBallLaw m k energy := by
  rw [forestGaussianInnovationLaw, Measure.map_map (vertexBallBuildLinear m k energy).continuous_of_finiteDimensional.measurable
    (forestGaussianInnovation m k _ _).continuous_of_finiteDimensional.measurable]
  rw [← vertexGaussianInnovation_eq_forest]
  rfl

theorem forest_edge_reference_physical_law (m k : ℕ) (energy : ℝ) :
    Measure.map (edgeBallBuildLinear m k energy)
      (forestGaussianInnovationLaw m k (Real.sqrt (siblingVariance (m + 2) energy))
        (physicalEdgeMatrix (energy / (m + 2)))) = edgeGaussianBallLaw m k energy := by
  rw [forestGaussianInnovationLaw, Measure.map_map (edgeBallBuildLinear m k energy).continuous_of_finiteDimensional.measurable
    (forestGaussianInnovation m k _ _).continuous_of_finiteDimensional.measurable]
  rw [← edgeGaussianInnovation_eq_forest]
  rfl

end GaussianWave.BS
