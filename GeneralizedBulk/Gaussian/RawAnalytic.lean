import GeneralizedBulk.Exterior.GaussianOrdinaryLaw

/-! The full raw Gaussian matrix has the stated spectral derivative. -/
noncomputable section
open MeasureTheory BourgadeHuang

namespace GeneralizedBulk.Exterior
variable {I S : Type*} [Countable I] [MeasurableSpace S]
variable (P : Measure S) [IsProbabilityMeasure P]
variable (X : S → Gaussian.PresentedState I) (hX : Measurable X)
variable (hm : Integrable (fun x => ‖(X x).scalar.val.2‖) P)

theorem hasDerivAt_constructedMatrix_ae (parameters : Parameters) :
    ∀ᵐ z ∂P.prod (Gaussian.iidLaw (Gaussian.markLaw parameters.p) I),
      ∀ i j : Fin 4, ∀ w : ℂ, ∀ hw : w.im ≠ 0,
      HasDerivAt (fun u =>
        (Marked.mean parameters (fun x => (X x).scalar) u z.1 +
          Gaussian.constructedField P X hX hm parameters (u, false) z) i j)
        (constructedDerivative P X hX hm parameters z ⟨w, hw⟩ i j) w := by
  filter_upwards [Gaussian.constructedField_hasDerivAt_ae P X hX hm parameters] with z hz
  intro i j w hw
  have hs := hasDerivAt_anchoredNevanlinna (X z.1).scalar hw
  have hmean := ((((hs.const_mul (parameters.scale : ℂ)).const_add
    (parameters.center : ℂ)).mul_const (covarianceMatrix (parameters.p : ℂ) i j)).add_const
    ((parameters.r : ℂ) * GeneralizedSwitching.edgeMatrix i j))
  have h := hmean.add (hz i j w hw)
  simpa only [mean_eq_covariance, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    constructedDerivative] using h

end GeneralizedBulk.Exterior
