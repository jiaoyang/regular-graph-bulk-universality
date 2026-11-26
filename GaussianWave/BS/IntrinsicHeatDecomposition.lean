import GaussianWave.BS.ScoreRotation
import GaussianWave.BS.LinearEntropy
import GaussianWave.BS.Reused.Analysis.ProductDensityEntropy

/-! Gaussian noise decomposes into actual independent intrinsic and normal
coordinates when the original law is supported on a linear subspace. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

section Split
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Actual Gaussian smoothing of a law supported on zero normal coordinates
factors pointwise into its intrinsic heat density and a normal Gaussian. -/
theorem heatDensity_zero_normal_factor
    (μ : Measure ((I ⊕ J) → ℝ)) [IsProbabilityMeasure μ]
    (hsupport : ∀ᵐ z ∂μ, rightCoordinates z = 0) {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (y : J → ℝ) :
    heatDensity μ t (Sum.elim x y) =
      heatDensity (Measure.map leftCoordinates μ) t x * heatKernel t y := by
  have he : heatDensity (Measure.map leftCoordinates μ) t x =
      ∫ z, heatKernel t (x - leftCoordinates z) ∂μ := by
    unfold heatDensity
    exact integral_map measurable_leftCoordinates.aemeasurable
      (((measurable_heatKernel t).comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  rw [he, ← integral_mul_const]
  unfold heatDensity
  apply integral_congr_ae
  filter_upwards [hsupport] with z hz
  rw [heatKernel_split_sub, hz, sub_zero]

private theorem squareRadius_left_le (z : (I ⊕ J) → ℝ) :
    squareRadius (leftCoordinates z) ≤ squareRadius z := by
  have he : squareRadius z = squareRadius (leftCoordinates z) + squareRadius (rightCoordinates z) := by
    simp only [squareRadius, Fintype.sum_sum_type, leftCoordinates, rightCoordinates]
  rw [he]
  exact le_add_of_nonneg_right (squareRadius_nonneg _)

private theorem integrable_squareRadius_left_image
    (μ : Measure ((I ⊕ J) → ℝ)) (hμ : Integrable (squareRadius (I := I ⊕ J)) μ) :
    Integrable (squareRadius (I := I)) (Measure.map leftCoordinates μ) := by
  apply (integrable_map_measure continuous_squareRadius.measurable.aestronglyMeasurable
    measurable_leftCoordinates.aemeasurable).mpr
  apply hμ.mono'
    ((continuous_squareRadius.measurable.comp measurable_leftCoordinates).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖squareRadius (leftCoordinates z)‖ ≤ squareRadius z
  rw [Real.norm_eq_abs, abs_of_nonneg (squareRadius_nonneg _)]
  exact squareRadius_left_le z

/-- Exact ambient entropy equals intrinsic heated entropy plus the Gaussian
normal entropy. All densities and product independence are derived. -/
theorem heatDensity_entropy_zero_normal
    (μ : Measure ((I ⊕ J) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I ⊕ J)) μ)
    (hsupport : ∀ᵐ z ∂μ, rightCoordinates z = 0) {t : ℝ} (ht : 0 < t) :
    densityEntropy volume (heatDensity μ t) =
      densityEntropy volume (heatDensity (Measure.map leftCoordinates μ) t) +
        gaussianEntropyValue J (heatVariance t) := by
  let ν := Measure.map leftCoordinates μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map measurable_leftCoordinates.aemeasurable
  have hν : Integrable (squareRadius (I := I)) ν := integrable_squareRadius_left_image μ hμ
  have hprod := Reused.Analysis.product_density_entropy
    (volume : Measure (I → ℝ)) (volume : Measure (J → ℝ))
    (heatDensity ν t) (heatKernel t) (integrable_heatDensity ν ht) (integrable_heatKernel t)
    (heatDensity_pos ν ht) (heatKernel_pos ht)
    (integrable_heatDensity_log ν hν ht) (integrable_heatKernel_log ht)
    (integral_heatDensity ν ht) (integral_heatKernel ht)
  have hpres := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : I ⊕ J => ℝ)
  have he := hpres.integral_comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)).symm.measurableEmbedding
    (fun z => heatDensity μ t z * Real.log (heatDensity μ t z))
  change (∫ p : (I → ℝ) × (J → ℝ),
      heatDensity μ t (Sum.elim p.1 p.2) * Real.log (heatDensity μ t (Sum.elim p.1 p.2))) =
        ∫ z, heatDensity μ t z * Real.log (heatDensity μ t z) at he
  unfold densityEntropy
  rw [← he]
  simp_rw [heatDensity_zero_normal_factor μ hsupport ht]
  have hp : -(∫ p : (I → ℝ) × (J → ℝ),
      heatDensity ν t p.1 * heatKernel t p.2 * Real.log (heatDensity ν t p.1 * heatKernel t p.2)) =
      densityEntropy (volume : Measure (I → ℝ)) (heatDensity ν t) +
        densityEntropy (volume : Measure (J → ℝ)) (heatKernel (I := J) t) := by
    simpa only [densityEntropy, sub_eq_add_neg] using hprod.2
  rw [densityEntropy_heatKernel ht] at hp
  exact hp
end Split

/-- The actual density entropy is its expected negative log density under the
actual convolution law. -/
theorem heatDensity_entropy_eq_negative_integral_log
    {I : Type*} [Fintype I] (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 < t) :
    densityEntropy volume (heatDensity μ t) = -(∫ x, Real.log (heatDensity μ t x) ∂heatedLaw μ t) := by
  rw [heatedLaw_eq_withDensity μ ht,
    integral_withDensity_eq_integral_toReal_smul (measurable_heatDensity μ t).ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [densityEntropy, ENNReal.toReal_ofReal (heatDensity_nonneg _ _ _), smul_eq_mul]

/-- Heat entropy is invariant under a full orthogonal change, including a
change of the finite coordinate index type. -/
theorem heatDensity_entropy_orthogonal_change
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (R : Matrix K I ℝ) (hRR : R * R.transpose = 1) (hRT : R.transpose * R = 1)
    {t : ℝ} (ht : 0 < t) :
    densityEntropy volume (heatDensity (Measure.map R.mulVec μ) t) =
      densityEntropy volume (heatDensity μ t) := by
  let ν := Measure.map R.mulVec μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map (measurable_finiteMatrixAction R).aemeasurable
  rw [heatDensity_entropy_eq_negative_integral_log ν ht,
    heatDensity_entropy_eq_negative_integral_log μ ht]
  have hmap := heatedLaw_map_orthonormal_rows μ R hRR t
  change Measure.map R.mulVec (heatedLaw μ t) = heatedLaw ν t at hmap
  rw [← hmap, integral_map (measurable_finiteMatrixAction R).aemeasurable
    (measurable_heatDensity ν t).log.aestronglyMeasurable]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [heatDensity_orthogonal_change μ R hRR hRT ht]

/-- Generic intrinsic/normal decomposition for a law with a proved orthogonal
support projection. The support premise is the ordinary actual a.e. linear
constraint, not a density or entropy conclusion. -/
theorem heatDensity_entropy_orthonormal_support
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ)
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1)
    (hsupport : ∀ᵐ x ∂μ, O.transpose.mulVec (O.mulVec x) = x)
    {t : ℝ} (ht : 0 < t) :
    densityEntropy volume (heatDensity μ t) =
      densityEntropy volume (heatDensity (Measure.map O.mulVec μ) t) +
        gaussianEntropyValue (Fin (Fintype.card I - Fintype.card J)) (heatVariance t) := by
  classical
  obtain ⟨R, hfirst, hRR, hRT⟩ := exists_orthogonal_row_completion O hO
  let ν := Measure.map R.mulVec μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map (measurable_finiteMatrixAction R).aemeasurable
  have hleft (x : I → ℝ) : leftCoordinates (R.mulVec x) = O.mulVec x := by
    ext j
    change R (Sum.inl j) ⬝ᵥ x = O j ⬝ᵥ x
    rw [hfirst]
  have hright (x : I → ℝ) (hx : O.transpose.mulVec (O.mulVec x) = x) :
      rightCoordinates (R.mulVec x) = 0 := by
    ext l
    change R.mulVec x (Sum.inr l) = 0
    rw [← hx, Matrix.mulVec_mulVec]
    have hz (j : J) : (R * O.transpose) (Sum.inr l) j = 0 := by
      have h := congrArg (fun M => M (Sum.inr l) (Sum.inl j)) hRR
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, hfirst, Matrix.one_apply,
        Sum.inr_ne_inl, if_false] using h
    simp only [Matrix.mulVec, dotProduct, hz, zero_mul, Finset.sum_const_zero]
  have hs : ∀ᵐ z ∂ν, rightCoordinates z = 0 := by
    rw [ae_map_iff (measurable_finiteMatrixAction R).aemeasurable
      (measurableSet_eq_fun (measurable_rightCoordinates (I := J)) measurable_const)]
    exact hsupport.mono (fun x hx => hright x hx)
  have hν := integrable_squareRadius_matrixImage μ hμ R
  have hm : Measure.map leftCoordinates ν = Measure.map O.mulVec μ := by
    rw [Measure.map_map measurable_leftCoordinates (measurable_finiteMatrixAction R)]
    congr 1
    funext x
    exact hleft x
  rw [← heatDensity_entropy_orthogonal_change μ R hRR hRT ht]
  rw [heatDensity_entropy_zero_normal ν hν hs ht, hm]
end GaussianWave.BS
