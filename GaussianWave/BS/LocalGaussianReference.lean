import GaussianWave.BS.GaussianOverlapLaws
import GaussianWave.BS.ForestLayerIndependence
import GaussianWave.BS.LocalEdgeChart
import GaussianWave.BS.LocalVertexChart

/-! The actual common-core plus one-new-block Gaussian laws in the
physical overlap charts. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

theorem probability_pi_eval {A X : Type*} [Fintype A] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (a : A) :
    Measure.map (fun x : A → X => x a) (Measure.pi (fun _ : A => μ)) = μ := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply a) hs]
  have hset : (fun x : A → X => x a) ⁻¹' s =
      Set.pi Set.univ (fun i => if i = a then s else Set.univ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro h i
      split_ifs with hi
      · simpa only [hi] using h
      · trivial
    · intro h
      simpa using h a
  rw [hset, Measure.pi_pi]
  simp only [apply_ite, measure_univ]
  simp

theorem core_new_projection_product {A X Z : Type*} [Fintype A]
    [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [IsProbabilityMeasure ν] (a : A) :
    Measure.map (fun p : Z × (A → X) => (p.1, p.2 a))
      (μ.prod (Measure.pi (fun _ : A => ν))) = μ.prod ν := by
  have h := Measure.map_prod_map (f := (id : Z → Z)) (g := fun x : A → X => x a)
    μ (Measure.pi (fun _ : A => ν)) measurable_id (measurable_pi_apply a)
  simpa only [Measure.map_id, probability_pi_eval] using h.symm

theorem forestGaussianInnovationLaw_local {A : Type*} [Fintype A] [DecidableEq A]
    (m k : ℕ) (scale : ℝ) (R : Matrix A A ℝ) (a : A) :
    Measure.map (forestLocalProjection A m k a)
      (forestGaussianInnovationLaw m (k + 1) scale R) =
      sumVectorProductLaw (forestGaussianInnovationLaw m k scale R)
        (newBranchGaussianLaw m k scale) := by
  have hsplit := forestGaussianInnovationLaw_split m k scale R
  have hlocal : (forestLocalProjection A m k a : _ → _) =
      concatenateVector ∘ (fun p => (p.1, p.2 a)) ∘ forestInnovationSplitCoordinates A m k := by
    funext x j
    cases j <;> rfl
  rw [hlocal, ← Function.comp_assoc, ← Measure.map_map
    (measurable_concatenateVector.comp (by fun_prop)) (measurable_forestInnovationSplitCoordinates A m k),
    hsplit]
  unfold sumVectorProductLaw
  rw [← Measure.map_map measurable_concatenateVector (by fun_prop), core_new_projection_product]

theorem localEdgeReconstruction_reference (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (a : Fin (m + 2)) :
    Measure.map (localEdgeReconstruction m k energy a)
      (sumVectorProductLaw
        (forestGaussianInnovationLaw m k (Real.sqrt (siblingVariance (m + 2) energy))
          (vertexRootInnovationFactor m energy))
        (newBranchGaussianLaw m k (Real.sqrt (siblingVariance (m + 2) energy)))) =
      edgeGaussianBallLaw m (k + 1) energy := by
  rw [← forestGaussianInnovationLaw_local m k _ (vertexRootInnovationFactor m energy) a,
    Measure.map_map (localEdgeReconstruction m k energy a).continuous_of_finiteDimensional.measurable
      (forestLocalProjection (Fin (m + 2)) m k a).continuous_of_finiteDimensional.measurable]
  have hcomp : (localEdgeReconstruction m k energy a : _ → _) ∘
      forestLocalProjection (Fin (m + 2)) m k a =
      (fun x => fun v => x (edgeInVertexCover m k a v)) ∘ vertexBallBuildLinear m (k + 1) energy :=
    funext (localEdgeReconstruction_projection m k energy a)
  rw [hcomp, ← Measure.map_map (by fun_prop)
    (vertexBallBuildLinear m (k + 1) energy).continuous_of_finiteDimensional.measurable,
    forest_vertex_reference_physical_law, vertexGaussianBallLaw_edge_window m k energy he a]

theorem localVertexReconstruction_reference (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (b : Bool) :
    Measure.map (localVertexReconstruction m k energy b)
      (sumVectorProductLaw
        (forestGaussianInnovationLaw m k (Real.sqrt (siblingVariance (m + 2) energy))
          (physicalEdgeMatrix (energy / (m + 2))))
        (newBranchGaussianLaw m k (Real.sqrt (siblingVariance (m + 2) energy)))) =
      vertexGaussianBallLaw m k energy := by
  rw [← forestGaussianInnovationLaw_local m k _ (physicalEdgeMatrix (energy / (m + 2))) b,
    Measure.map_map (localVertexReconstruction m k energy b).continuous_of_finiteDimensional.measurable
      (forestLocalProjection Bool m k b).continuous_of_finiteDimensional.measurable]
  have hcomp : (localVertexReconstruction m k energy b : _ → _) ∘
      forestLocalProjection Bool m k b =
      (fun x => fun v => x (vertexInEdgeCover m k b v)) ∘ edgeBallBuildLinear m (k + 1) energy :=
    funext (localVertexReconstruction_projection m k energy b)
  rw [hcomp, ← Measure.map_map (by fun_prop)
    (edgeBallBuildLinear m (k + 1) energy).continuous_of_finiteDimensional.measurable,
    forest_edge_reference_physical_law, edgeGaussianBallLaw_vertex_window m k energy he b]

end GaussianWave.BS
