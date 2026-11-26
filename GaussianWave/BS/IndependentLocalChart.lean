import GaussianWave.BS.IndependentLawSplit
import GaussianWave.BS.ColoredInnovationCharts
import GaussianWave.BS.BallExtraction

/-! Whole-channel lifts of actual local reference chart laws. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

theorem independentChannelLaw_localChart {κ I J K : Type*}
    [Fintype κ] [Fintype I] [Fintype J] [Fintype K]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (ν : Measure (J → ℝ)) [IsProbabilityMeasure ν]
    (L : ((I ⊕ J) → ℝ) ≃ₗ[ℝ] (K → ℝ)) :
    Measure.map (coloredSumLinearEquiv κ L)
      (sumVectorProductLaw (independentChannelLaw (fun _ : κ => μ))
        (independentChannelLaw (fun _ : κ => ν))) =
      independentChannelLaw (fun _ : κ => Measure.map L (sumVectorProductLaw μ ν)) := by
  letI : IsProbabilityMeasure (sumVectorProductLaw μ ν) := by
    unfold sumVectorProductLaw
    exact isProbabilityMeasure_map measurable_concatenateVector.aemeasurable
  have hL : Measurable (L : ((I ⊕ J) → ℝ) → (K → ℝ)) :=
    L.toLinearMap.continuous_of_finiteDimensional.measurable
  have hCL : Measurable (coloredSumLinearEquiv κ L : _ → _) :=
    (coloredSumLinearEquiv κ L).toLinearMap.continuous_of_finiteDimensional.measurable
  have hp := measurePreserving_arrowProdEquivProdArrow (I → ℝ) (J → ℝ) κ
    (fun _ => μ) (fun _ => ν)
  have hμ : MeasurePreserving (flattenChannels (κ := κ) (ι := I))
      (Measure.pi (fun _ : κ => μ)) (independentChannelLaw (fun _ : κ => μ)) :=
    ⟨measurable_flattenChannels, rfl⟩
  have hν : MeasurePreserving (flattenChannels (κ := κ) (ι := J))
      (Measure.pi (fun _ : κ => ν)) (independentChannelLaw (fun _ : κ => ν)) :=
    ⟨measurable_flattenChannels, rfl⟩
  have hc : MeasurePreserving concatenateVector
      ((independentChannelLaw (fun _ : κ => μ)).prod (independentChannelLaw (fun _ : κ => ν)))
      (sumVectorProductLaw (independentChannelLaw (fun _ : κ => μ))
        (independentChannelLaw (fun _ : κ => ν))) := ⟨measurable_concatenateVector, rfl⟩
  have hleft := (show MeasurePreserving (coloredSumLinearEquiv κ L)
      (sumVectorProductLaw (independentChannelLaw (fun _ : κ => μ))
        (independentChannelLaw (fun _ : κ => ν)))
      (Measure.map (coloredSumLinearEquiv κ L)
        (sumVectorProductLaw (independentChannelLaw (fun _ : κ => μ))
          (independentChannelLaw (fun _ : κ => ν)))) from ⟨hCL, rfl⟩).comp
    (hc.comp ((hμ.prod hν).comp hp))
  have hloc : MeasurePreserving ((L : _ → _) ∘ concatenateVector) (μ.prod ν)
      (Measure.map L (sumVectorProductLaw μ ν)) := by
    refine ⟨hL.comp measurable_concatenateVector, ?_⟩
    rw [sumVectorProductLaw, Measure.map_map hL measurable_concatenateVector]
  letI : IsProbabilityMeasure (Measure.map L (sumVectorProductLaw μ ν)) :=
    isProbabilityMeasure_map hL.aemeasurable
  have hi := measurePreserving_pi (fun _ : κ => μ.prod ν)
    (fun _ : κ => Measure.map L (sumVectorProductLaw μ ν)) (f := fun _ => (L : _ → _) ∘ concatenateVector)
    (fun _ => hloc)
  have hf : MeasurePreserving (flattenChannels (κ := κ) (ι := K))
      (Measure.pi (fun _ : κ => Measure.map L (sumVectorProductLaw μ ν)))
      (independentChannelLaw (fun _ : κ => Measure.map L (sumVectorProductLaw μ ν))) :=
    ⟨measurable_flattenChannels, rfl⟩
  have hright := hf.comp hi
  rw [← hleft.map_eq, ← hright.map_eq]
  congr 1
  funext p ⟨a, j⟩
  change coloredSumLinearEquiv κ L
    (concatenateVector (flattenChannels (fun c => (p c).1), flattenChannels (fun c => (p c).2))) (a, j) =
      L (concatenateVector (p a)) j
  rw [coloredSumLinearEquiv_apply]
  rfl

theorem coloredLocalEdgeInnovationEquiv_reference (κ : Type*) [Fintype κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) (a : Fin (m + 2)) :
    Measure.map (coloredLocalEdgeInnovationEquiv κ m k energy
        (ne_of_lt ((le_abs_self energy).trans_lt he)) a)
      (sumVectorProductLaw
        (independentChannelLaw (fun _ : κ => forestGaussianInnovationLaw m k
          (Real.sqrt (siblingVariance (m + 2) energy)) (vertexRootInnovationFactor m energy)))
        (independentChannelLaw (fun _ : κ => newBranchGaussianLaw m k
          (Real.sqrt (siblingVariance (m + 2) energy))))) =
      independentChannelLaw (fun _ : κ => forestGaussianInnovationLaw m (k + 1)
        (Real.sqrt (siblingVariance (m + 2) energy)) (physicalEdgeMatrix (energy / (m + 2)))) := by
  rw [coloredLocalEdgeInnovationEquiv, independentChannelLaw_localChart,
    localEdgeInnovationEquiv_reference m k energy he a]

theorem coloredLocalVertexInnovationEquiv_reference (κ : Type*) [Fintype κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) (b : Bool) :
    Measure.map (coloredLocalVertexInnovationEquiv κ m k energy
        (ne_of_lt ((le_abs_self energy).trans_lt he)) b)
      (sumVectorProductLaw
        (independentChannelLaw (fun _ : κ => forestGaussianInnovationLaw m k
          (Real.sqrt (siblingVariance (m + 2) energy)) (physicalEdgeMatrix (energy / (m + 2)))))
        (independentChannelLaw (fun _ : κ => newBranchGaussianLaw m k
          (Real.sqrt (siblingVariance (m + 2) energy))))) =
      independentChannelLaw (fun _ : κ => forestGaussianInnovationLaw m k
        (Real.sqrt (siblingVariance (m + 2) energy)) (vertexRootInnovationFactor m energy)) := by
  rw [coloredLocalVertexInnovationEquiv, independentChannelLaw_localChart,
    localVertexInnovationEquiv_reference m k energy he b]

end GaussianWave.BS
