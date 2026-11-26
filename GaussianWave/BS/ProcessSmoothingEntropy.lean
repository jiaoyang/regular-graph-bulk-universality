import GaussianWave.BS.PositiveGaussianRegularization
import GaussianWave.BS.ProcessGaussianReference
import GaussianWave.BS.IndependentTreeSum
import GaussianWave.BS.ChannelSupportReduction
import GaussianWave.BS.InnovationEntropyCoordinates
import GaussianWave.BS.WhitenedGaussianSum

/-! Actual positive finite-entropy innovation densities of independently
Gaussian-smoothed processes. Channel whitening is transported through the
literal innovation maps; neither source densities nor source entropies are
assumed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

theorem independentChannelLaw_linearImageGaussian
    {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]
    [DecidableEq A] [DecidableEq I] (L : Matrix I J ℝ) :
    independentChannelLaw (fun _ : A => linearImageGaussian L) =
      linearImageGaussian (independentBlockFactor (A := A) L) := by
  rw [independentBlockFactor_gaussian_product]
  change Measure.map flattenChannels _ = Measure.map flattenChannels _
  congr 1
  apply congrArg Measure.pi
  funext a
  exact eq_gaussianCovarianceLaw _ _ (real_rowGram_posSemidef L)
    (linearImageGaussian_characteristic L)

theorem jointVertexInnovationProcessLaw_gaussian_factor (r m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    jointVertexInnovationProcessLaw (jointGaussianTreeProcessLaw r m energy) k =
      linearImageGaussian (independentBlockFactor (A := Fin r)
        (forestGaussianInnovationMatrix m k (Real.sqrt (siblingVariance (m + 2) energy))
          (vertexRootInnovationFactor m energy))) := by
  rw [← jointVertexInnovationReference_process_law r m k energy he,
    jointVertexInnovationReference_law, forestGaussianInnovationLaw_eq_linearImage,
    independentChannelLaw_linearImageGaussian]

theorem jointEdgeInnovationProcessLaw_gaussian_factor (r m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    jointEdgeInnovationProcessLaw (jointGaussianTreeProcessLaw r m energy) k =
      linearImageGaussian (independentBlockFactor (A := Fin r)
        (forestGaussianInnovationMatrix m k (Real.sqrt (siblingVariance (m + 2) energy))
          (physicalEdgeMatrix (energy / (m + 2))))) := by
  rw [← jointEdgeInnovationReference_process_law r m k energy he,
    jointEdgeInnovationReference_law, forestGaussianInnovationLaw_eq_linearImage,
    independentChannelLaw_linearImageGaussian]

theorem integrable_squareRadius_jointTreeWindow {r d : ℕ} {I : Type*} [Fintype I]
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (site : I → RegularTreeVertex d) :
    Integrable (squareRadius (I := Fin r × I)) (Measure.map (jointTreeWindow site) μ) := by
  apply (integrable_map_measure continuous_squareRadius.measurable.aestronglyMeasurable
    (measurable_jointTreeWindow site).aemeasurable).mpr
  exact integrable_finset_sum _ (fun av _ => hi (av.1, site av.2))

theorem integrable_squareRadius_linearMapImage {I J : Type*}
    [Fintype I] [Fintype J] (μ : Measure (I → ℝ))
    (hμ : Integrable (squareRadius (I := I)) μ) (L : (I → ℝ) →ₗ[ℝ] (J → ℝ)) :
    Integrable (squareRadius (I := J)) (Measure.map L μ) := by
  have hM : (LinearMap.toMatrix' L).mulVec = L :=
    congrArg DFunLike.coe (Matrix.toLin'_toMatrix' L)
  simpa only [hM] using integrable_squareRadius_matrixImage μ hμ (LinearMap.toMatrix' L)

theorem jointVertexInnovationProcessLaw_integrable_squareRadius {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (k : ℕ) :
    Integrable squareRadius (jointVertexInnovationProcessLaw μ k) :=
  integrable_squareRadius_linearMapImage _
    (integrable_squareRadius_jointTreeWindow μ hi _) (jointVertexBallExtract (Fin r) m k)

theorem jointEdgeInnovationProcessLaw_integrable_squareRadius {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (k : ℕ) :
    Integrable squareRadius (jointEdgeInnovationProcessLaw μ k) :=
  integrable_squareRadius_linearMapImage _
    (integrable_squareRadius_jointTreeWindow μ hi _) (jointEdgeBallExtract (Fin r) m k)

theorem jointVertexInnovationProcessLaw_independentTreeSum {r m : ℕ}
    (μ ν : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (k : ℕ) :
    jointVertexInnovationProcessLaw (independentTreeSumLaw μ ν) k =
      Measure.conv (jointVertexInnovationProcessLaw μ k) (jointVertexInnovationProcessLaw ν k) := by
  let L := jointVertexBallExtract (Fin r) m k
  let W := jointTreeWindow (r := r) (vertexBallEmbedding (m + 2) k)
  have hW : Measurable W := measurable_jointTreeWindow _
  have hL : Measurable L := L.continuous_of_finiteDimensional.measurable
  change Measure.map L (Measure.map W (independentTreeSumLaw μ ν)) =
    Measure.conv (Measure.map L (Measure.map W μ)) (Measure.map L (Measure.map W ν))
  simp only [Measure.map_map hL hW]
  rw [independentTreeSumLaw_map μ ν (L ∘ W) (hL.comp hW)
    (fun x y => L.map_add (W x) (W y)), independentAddLaw_one_eq_conv]

theorem jointEdgeInnovationProcessLaw_independentTreeSum {r m : ℕ}
    (μ ν : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (k : ℕ) :
    jointEdgeInnovationProcessLaw (independentTreeSumLaw μ ν) k =
      Measure.conv (jointEdgeInnovationProcessLaw μ k) (jointEdgeInnovationProcessLaw ν k) := by
  let L := jointEdgeBallExtract (Fin r) m k
  let W := jointTreeWindow (r := r) (edgeBallEmbedding m k)
  have hW : Measurable W := measurable_jointTreeWindow _
  have hL : Measurable L := L.continuous_of_finiteDimensional.measurable
  change Measure.map L (Measure.map W (independentTreeSumLaw μ ν)) =
    Measure.conv (Measure.map L (Measure.map W μ)) (Measure.map L (Measure.map W ν))
  simp only [Measure.map_map hL hW]
  rw [independentTreeSumLaw_map μ ν (L ∘ W) (hL.comp hW)
    (fun x y => L.map_add (W x) (W y)), independentAddLaw_one_eq_conv]

instance jointVertexInnovationProcessLaw_probability {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    [IsProbabilityMeasure μ] (k : ℕ) : IsProbabilityMeasure (jointVertexInnovationProcessLaw μ k) :=
  isProbabilityMeasure_map (jointVertexBallExtract (Fin r) m k).continuous_of_finiteDimensional.measurable.aemeasurable

instance jointEdgeInnovationProcessLaw_probability {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    [IsProbabilityMeasure μ] (k : ℕ) : IsProbabilityMeasure (jointEdgeInnovationProcessLaw μ k) :=
  isProbabilityMeasure_map (jointEdgeBallExtract (Fin r) m k).continuous_of_finiteDimensional.measurable.aemeasurable

def gaussianSumVertexInnovationDensity {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (k : ℕ) :
    PositiveEntropyDensity (volume : Measure ((Fin r × VertexBallInnovation (m + 2) k) → ℝ)) :=
  gaussianLinearRegularizationPositiveDensity (jointVertexInnovationProcessLaw μ k)
    (jointVertexInnovationProcessLaw_integrable_squareRadius μ hi k) _
    (independentBlockFactor_surjective _ (by
      rw [forestGaussianInnovationMatrix_mulVec]
      exact forestGaussianInnovation_surjective m k _ (siblingScale_ne_zero m energy he) _
        (vertexRootInnovationFactor_surjective m energy he)))

@[simp] theorem gaussianSumVertexInnovationDensity_law {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (k : ℕ) :
    (gaussianSumVertexInnovationDensity μ hi energy he k).law =
      jointVertexInnovationProcessLaw (independentTreeSumLaw μ (jointGaussianTreeProcessLaw r m energy)) k := by
  rw [gaussianSumVertexInnovationDensity, gaussianLinearRegularizationPositiveDensity_law,
    jointVertexInnovationProcessLaw_independentTreeSum,
    jointVertexInnovationProcessLaw_gaussian_factor r m k energy he]

def gaussianSumEdgeInnovationDensity {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (k : ℕ) :
    PositiveEntropyDensity (volume : Measure ((Fin r × EdgeBallInnovation (m + 2) k) → ℝ)) :=
  gaussianLinearRegularizationPositiveDensity (jointEdgeInnovationProcessLaw μ k)
    (jointEdgeInnovationProcessLaw_integrable_squareRadius μ hi k) _
    (independentBlockFactor_surjective _ (by
      rw [forestGaussianInnovationMatrix_mulVec]
      exact forestGaussianInnovation_surjective m k _ (siblingScale_ne_zero m energy he) _
        (physicalEdgeMatrix_surjective m energy he)))

@[simp] theorem gaussianSumEdgeInnovationDensity_law {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (k : ℕ) :
    (gaussianSumEdgeInnovationDensity μ hi energy he k).law =
      jointEdgeInnovationProcessLaw (independentTreeSumLaw μ (jointGaussianTreeProcessLaw r m energy)) k := by
  rw [gaussianSumEdgeInnovationDensity, gaussianLinearRegularizationPositiveDensity_law,
    jointEdgeInnovationProcessLaw_independentTreeSum,
    jointEdgeInnovationProcessLaw_gaussian_factor r m k energy he]

theorem channelwiseLinearMap_channelLift {κ I J : Type*} [Fintype κ]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (B : Matrix κ κ ℝ) (L : (I → ℝ) →ₗ[ℝ] (J → ℝ)) (x : (κ × I) → ℝ) :
    channelwiseLinearMap κ L ((channelLift B I).mulVec x) =
      (channelLift B J).mulVec (channelwiseLinearMap κ L x) := by
  ext ⟨a, j⟩
  rw [channelLift_mulVec]
  change L (fun i => (channelLift B I).mulVec x (a, i)) j = _
  simp_rw [channelLift_mulVec]
  have he : (fun i => ∑ b, B a b * x (b, i)) = ∑ b, B a b • (fun i => x (b, i)) := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, channelwiseLinearMap]
  rfl

theorem jointTreeWindow_channelProcessMap {r d : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (B : Matrix (Fin r) (Fin r) ℝ)
    (site : I → RegularTreeVertex d) (x : (Fin r × RegularTreeVertex d) → ℝ) :
    jointTreeWindow site (channelProcessMap B x) =
      (channelLift B I).mulVec (jointTreeWindow site x) := by
  ext ⟨a, i⟩
  exact (channelLift_mulVec B (jointTreeWindow site x) a i).symm

theorem channelLift_det_ne_zero {κ S : Type*} [Fintype κ] [Fintype S]
    [DecidableEq κ] [DecidableEq S] (B : Matrix κ κ ℝ) (hB : B.det ≠ 0) :
    (channelLift B S).det ≠ 0 := by
  have hmul : channelLift B S * channelLift B⁻¹ S = 1 := by
    rw [channelLift_mul, Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB), channelLift_one]
  have hdet := congrArg Matrix.det hmul
  intro hzero
  rw [Matrix.det_mul, hzero, zero_mul, Matrix.det_one] at hdet
  exact zero_ne_one hdet

theorem jointVertexInnovationProcessLaw_channelProcessMap {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    (B : Matrix (Fin r) (Fin r) ℝ) (k : ℕ) :
    jointVertexInnovationProcessLaw (Measure.map (channelProcessMap B) μ) k =
      Measure.map (channelLift B (VertexBallInnovation (m + 2) k)).mulVec
        (jointVertexInnovationProcessLaw μ k) := by
  rw [jointVertexInnovationProcessLaw, jointVertexProcessBallLaw,
    Measure.map_map (measurable_jointTreeWindow _) (continuous_channelProcessMap B).measurable,
    Measure.map_map (jointVertexBallExtract (Fin r) m k).continuous_of_finiteDimensional.measurable
      ((measurable_jointTreeWindow _).comp (continuous_channelProcessMap B).measurable),
    jointVertexInnovationProcessLaw, jointVertexProcessBallLaw,
    Measure.map_map (jointVertexBallExtract (Fin r) m k).continuous_of_finiteDimensional.measurable
      (measurable_jointTreeWindow _),
    Measure.map_map (measurable_finiteMatrixAction _) ((jointVertexBallExtract (Fin r) m k).continuous_of_finiteDimensional.measurable.comp
      (measurable_jointTreeWindow _))]
  congr 1
  funext x
  simpa only [Function.comp_apply, jointTreeWindow_channelProcessMap] using
    channelwiseLinearMap_channelLift B (vertexBallExtractLinear m k)
    (jointTreeWindow (vertexBallEmbedding (m + 2) k) x)

theorem jointEdgeInnovationProcessLaw_channelProcessMap {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    (B : Matrix (Fin r) (Fin r) ℝ) (k : ℕ) :
    jointEdgeInnovationProcessLaw (Measure.map (channelProcessMap B) μ) k =
      Measure.map (channelLift B (EdgeBallInnovation (m + 2) k)).mulVec
        (jointEdgeInnovationProcessLaw μ k) := by
  rw [jointEdgeInnovationProcessLaw, jointEdgeProcessBallLaw,
    Measure.map_map (measurable_jointTreeWindow _) (continuous_channelProcessMap B).measurable,
    Measure.map_map (jointEdgeBallExtract (Fin r) m k).continuous_of_finiteDimensional.measurable
      ((measurable_jointTreeWindow _).comp (continuous_channelProcessMap B).measurable),
    jointEdgeInnovationProcessLaw, jointEdgeProcessBallLaw,
    Measure.map_map (jointEdgeBallExtract (Fin r) m k).continuous_of_finiteDimensional.measurable
      (measurable_jointTreeWindow _),
    Measure.map_map (measurable_finiteMatrixAction _) ((jointEdgeBallExtract (Fin r) m k).continuous_of_finiteDimensional.measurable.comp
      (measurable_jointTreeWindow _))]
  congr 1
  funext x
  simpa only [Function.comp_apply, jointTreeWindow_channelProcessMap] using
    channelwiseLinearMap_channelLift B (edgeBallExtractLinear m k)
    (jointTreeWindow (edgeBallEmbedding m k) x)

/-- An arbitrary invertible channel change is applied to the entire smoothed
process, and the resulting literal raw C-ball innovation law has positive
finite entropy. -/
def channelGaussianSumVertexInnovationDensity {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ))
    (B : Matrix (Fin r) (Fin r) ℝ) (hB : B.det ≠ 0) (k : ℕ) :
    PositiveEntropyDensity (volume : Measure ((Fin r × VertexBallInnovation (m + 2) k) → ℝ)) :=
  (gaussianSumVertexInnovationDensity μ hi energy he k).linearEquiv
    (invertibleMatrixEquiv (channelLift B (VertexBallInnovation (m + 2) k))
      (channelLift_det_ne_zero B hB)).toLinearEquiv

@[simp] theorem channelGaussianSumVertexInnovationDensity_law {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ))
    (B : Matrix (Fin r) (Fin r) ℝ) (hB : B.det ≠ 0) (k : ℕ) :
    (channelGaussianSumVertexInnovationDensity μ hi energy he B hB k).law =
      jointVertexInnovationProcessLaw (Measure.map (channelProcessMap B)
        (independentTreeSumLaw μ (jointGaussianTreeProcessLaw r m energy))) k := by
  rw [channelGaussianSumVertexInnovationDensity, PositiveEntropyDensity.linearEquiv_law,
    gaussianSumVertexInnovationDensity_law, jointVertexInnovationProcessLaw_channelProcessMap]
  rfl

def channelGaussianSumEdgeInnovationDensity {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ))
    (B : Matrix (Fin r) (Fin r) ℝ) (hB : B.det ≠ 0) (k : ℕ) :
    PositiveEntropyDensity (volume : Measure ((Fin r × EdgeBallInnovation (m + 2) k) → ℝ)) :=
  (gaussianSumEdgeInnovationDensity μ hi energy he k).linearEquiv
    (invertibleMatrixEquiv (channelLift B (EdgeBallInnovation (m + 2) k))
      (channelLift_det_ne_zero B hB)).toLinearEquiv

@[simp] theorem channelGaussianSumEdgeInnovationDensity_law {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ))
    (B : Matrix (Fin r) (Fin r) ℝ) (hB : B.det ≠ 0) (k : ℕ) :
    (channelGaussianSumEdgeInnovationDensity μ hi energy he B hB k).law =
      jointEdgeInnovationProcessLaw (Measure.map (channelProcessMap B)
        (independentTreeSumLaw μ (jointGaussianTreeProcessLaw r m energy))) k := by
  rw [channelGaussianSumEdgeInnovationDensity, PositiveEntropyDensity.linearEquiv_law,
    gaussianSumEdgeInnovationDensity_law, jointEdgeInnovationProcessLaw_channelProcessMap]
  rfl

def whitenedGaussianSumVertexInnovationDensity {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (k : ℕ) :
    PositiveEntropyDensity (volume : Measure ((Fin r × VertexBallInnovation (m + 2) k) → ℝ)) :=
  channelGaussianSumVertexInnovationDensity μ hi energy he
    (positiveRootWhitening (treeRootCovariance μ) (treeRootCovariance_posSemidef μ hi))
    (positiveRootWhitening_det_ne_zero _ _) k

@[simp] theorem whitenedGaussianSumVertexInnovationDensity_law {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (k : ℕ) :
    (whitenedGaussianSumVertexInnovationDensity μ hi energy he k).law =
      jointVertexInnovationProcessLaw (whitenedGaussianSumLaw μ hi energy) k :=
  channelGaussianSumVertexInnovationDensity_law μ hi energy he _ _ k

def whitenedGaussianSumEdgeInnovationDensity {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (k : ℕ) :
    PositiveEntropyDensity (volume : Measure ((Fin r × EdgeBallInnovation (m + 2) k) → ℝ)) :=
  channelGaussianSumEdgeInnovationDensity μ hi energy he
    (positiveRootWhitening (treeRootCovariance μ) (treeRootCovariance_posSemidef μ hi))
    (positiveRootWhitening_det_ne_zero _ _) k

@[simp] theorem whitenedGaussianSumEdgeInnovationDensity_law {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (k : ℕ) :
    (whitenedGaussianSumEdgeInnovationDensity μ hi energy he k).law =
      jointEdgeInnovationProcessLaw (whitenedGaussianSumLaw μ hi energy) k :=
  channelGaussianSumEdgeInnovationDensity_law μ hi energy he _ _ k

end GaussianWave.BS
