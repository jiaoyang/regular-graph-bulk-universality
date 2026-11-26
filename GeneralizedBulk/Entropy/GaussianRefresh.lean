import GeneralizedBulk.Entropy.GaussianSteinBounded

/-! Refreshing a single coordinate with an independent standard Gaussian
preserves the actual finite Gaussian product law. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Entropy.Hermite
open GeneralizedBulk.Gaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

def extraCoordinateSplit (I : Type*) : ((I ⊕ Unit) → ℝ) ≃ᵐ (I → ℝ) × ℝ :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ Unit => ℝ)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.funUnique Unit ℝ))

theorem extraCoordinateSplit_measurePreserving :
    MeasurePreserving (extraCoordinateSplit I) (standardGaussian (I ⊕ Unit))
      ((standardGaussian I).prod standardNormal) := by
  have h1 := measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ Unit => standardNormal)
  have h2 := (MeasurePreserving.id (standardGaussian I)).prod (measurePreserving_funUnique standardNormal Unit)
  exact h2.comp h1

def refreshIndex (i j : I) : I ⊕ Unit := if j = i then Sum.inr () else Sum.inl j

theorem refreshIndex_injective (i : I) : Function.Injective (refreshIndex i) := by
  intro j k h
  by_cases hj : j = i <;> by_cases hk : k = i
  · exact hj.trans hk.symm
  · simp only [refreshIndex, hj, hk, ↓reduceIte] at h
    cases h
  · simp only [refreshIndex, hj, hk, ↓reduceIte] at h
    cases h
  · simpa only [refreshIndex, hj, hk, ↓reduceIte, Sum.inl.injEq] using h

theorem refreshSelection_measurePreserving (i : I) :
    MeasurePreserving (fun x : (I ⊕ Unit) → ℝ => fun j => x (refreshIndex i j))
      (standardGaussian (I ⊕ Unit)) (standardGaussian I) := by
  refine ⟨measurable_pi_lambda _ (fun j => measurable_pi_apply _), ?_⟩
  simpa only [iidLaw, Measure.infinitePi_eq_pi, standardGaussian] using
    iidLaw_map_injectiveSelection standardNormal (I ⊕ Unit) (refreshIndex i) (refreshIndex_injective i)

/-- The actual product-space refresh map used by coordinate Gaussian
integration by parts. -/
theorem update_measurePreserving (i : I) :
    MeasurePreserving (fun p : (I → ℝ) × ℝ => Function.update p.1 i p.2)
      ((standardGaussian I).prod standardNormal) (standardGaussian I) := by
  have hm := (refreshSelection_measurePreserving i).comp extraCoordinateSplit_measurePreserving.symm
  convert hm using 1
  funext p j
  by_cases hji : j = i
  · subst j
    simp [refreshIndex, extraCoordinateSplit, Function.comp_apply]
    rfl
  · simp [refreshIndex, extraCoordinateSplit, Function.comp_apply, Function.update_of_ne hji, hji]
    rfl


/-- Exact coordinate-refresh Fubini formula, with joint integrability derived
from the actual measure-preserving refresh map. -/
theorem integral_refresh (i : I) (F : (I → ℝ) → ℝ) (hF : Continuous F)
    (hFi : Integrable F (standardGaussian I)) :
    (∫ x, ∫ t, F (Function.update x i t) ∂standardNormal ∂standardGaussian I) =
      ∫ x, F x ∂standardGaussian I := by
  have hm := update_measurePreserving i
  have hi := (hm.integrable_comp hF.aestronglyMeasurable).mpr hFi
  change (∫ x, ∫ t, (F ∘ (fun p : (I → ℝ) × ℝ => Function.update p.1 i p.2)) (x, t) ∂standardNormal ∂standardGaussian I) = _
  rw [← integral_prod _ hi]
  simp only [Function.comp_apply]
  rw [← integral_map hm.measurable.aemeasurable hF.aestronglyMeasurable, hm.map_eq]

end GeneralizedBulk.Entropy.Hermite
