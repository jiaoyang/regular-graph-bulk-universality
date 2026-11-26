import GaussianWave.BS.LogDensityFactorization

/-! Actual white covariance and integration by parts identify every coefficient
of a linear heat score, including all cross-channel coefficients. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace GaussianWave.BS
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem clm_eq_finiteLinearForm (A : (I → ℝ) →L[ℝ] ℝ) (x : I → ℝ) :
    A x = finiteLinearForm (fun i => A (Pi.single i 1)) x := by
  have hsum : x = ∑ i, x i • (Pi.single i 1 : I → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hsum]
  simp only [map_sum, map_smul, smul_eq_mul, finiteLinearForm]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem heatDirectionalScore_of_bilinear_quadratic_logshape
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (P : (I → ℝ) →ₗ[ℝ] (I → ℝ))
    (B : (I → ℝ) →L[ℝ] (I → ℝ) →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u)
    (hshape : ∀ x, Real.log (heatDensity μ t x) =
      Real.log (heatDensity μ t (P x)) + B (x - P x) (x - P x) / 2)
    (w : I → ℝ) (hw : P w = 0) (x : I → ℝ) :
    heatDirectionalScore μ t w x = B w (x - P x) := by
  let u := x - P x
  have hc : HasDerivAt (fun s : ℝ => u + s • w) w 0 := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const (0 : ℝ) u).add ((hasDerivAt_id (0 : ℝ)).smul_const w)
  have hb := ((B.hasFDerivAt.comp_hasDerivAt 0 hc).clm_apply hc).div_const 2
  have hq : HasDerivAt (fun s : ℝ => Real.log (heatDensity μ t (P x)) + B (u + s • w) (u + s • w) / 2)
      (B w u) 0 := by
    convert hb.const_add (Real.log (heatDensity μ t (P x))) using 1
    simp only [zero_smul, add_zero, Function.comp_apply]
    rw [hB u w]
    ring
  have heq : (fun s : ℝ => Real.log (heatDensity μ t (x + s • w))) =
      (fun s : ℝ => Real.log (heatDensity μ t (P x)) + B (u + s • w) (u + s • w) / 2) := by
    funext s
    rw [hshape, map_add, map_smul, hw, smul_zero, add_zero]
    dsimp [u]
    congr 2 <;> abel
  rw [← heq] at hq
  rw [heatDirectionalScore_eq_log_fderiv μ ht]
  exact (((contDiff_three_log_heatDensity μ ht).differentiable (by simp) x).hasFDerivAt.hasLineDerivAt w).unique hq

private theorem integrable_form_density
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) (v : I → ℝ) :
    Integrable (fun x => finiteLinearForm v x * heatDensity μ t x) := by
  have h2 := integrable_heatDensity_mul_linearForm_sq μ hμ ht v
  apply ((integrable_heatDensity μ ht).add h2).mono'
    (((continuous_finiteLinearForm v).measurable.mul (measurable_heatDensity μ t)).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatDensity_nonneg _ _ _)]
  change |finiteLinearForm v x| * heatDensity μ t x ≤
    heatDensity μ t x + heatDensity μ t x * finiteLinearForm v x ^ 2
  have habs : |finiteLinearForm v x| ≤ 1 + finiteLinearForm v x ^ 2 := by
    nlinarith [sq_nonneg (|finiteLinearForm v x| - 1), sq_abs (finiteLinearForm v x)]
  nlinarith [mul_le_mul_of_nonneg_right habs (heatDensity_nonneg μ t x)]

theorem linear_heatScore_bilinear_identity
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t)
    (w a : I → ℝ) (hscore : ∀ x, heatDirectionalScore μ t w x = finiteLinearForm a x)
    (v : I → ℝ) :
    (∫ x, finiteLinearForm v x * (finiteLinearForm a x * heatDensity μ t x)) = -finiteLinearForm v w := by
  have h2 := (integrable_heatDensity_mul_linearForm_sq μ hμ ht v).add
    (integrable_heatDensity_mul_linearForm_sq μ hμ ht a)
  have hprod : Integrable (fun x => finiteLinearForm v x * (finiteLinearForm a x * heatDensity μ t x)) := by
    apply h2.mono'
      (((continuous_finiteLinearForm v).measurable.mul
        ((continuous_finiteLinearForm a).measurable.mul (measurable_heatDensity μ t))).aestronglyMeasurable)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (heatDensity_nonneg _ _ _)]
    change |finiteLinearForm v x| * (|finiteLinearForm a x| * heatDensity μ t x) ≤
      heatDensity μ t x * finiteLinearForm v x ^ 2 + heatDensity μ t x * finiteLinearForm a x ^ 2
    have hab : |finiteLinearForm v x| * |finiteLinearForm a x| ≤
        finiteLinearForm v x ^ 2 + finiteLinearForm a x ^ 2 := by
      nlinarith [sq_nonneg (|finiteLinearForm v x| - |finiteLinearForm a x|),
        sq_abs (finiteLinearForm v x), sq_abs (finiteLinearForm a x)]
    nlinarith [mul_le_mul_of_nonneg_right hab (heatDensity_nonneg μ t x)]
  have hf (x : I → ℝ) : HasLineDerivAt ℝ (finiteLinearForm v) (finiteLinearForm v w) x w := by
    change HasDerivAt (fun s : ℝ => finiteLinearForm v (x + s • w)) _ 0
    have h : HasDerivAt (fun s : ℝ => ∑ i, v i * (x i + s * w i)) (∑ i, v i * w i) 0 := by
      apply HasDerivAt.sum
      intro i _
      simpa using ((hasDerivAt_const 0 (x i)).add ((hasDerivAt_id 0).mul_const (w i))).const_mul (v i)
    exact h
  have hg (x : I → ℝ) : HasLineDerivAt ℝ (heatDensity μ t)
      (finiteLinearForm a x * heatDensity μ t x) x w := by
    have hs := hscore x
    unfold heatDirectionalScore at hs
    have hn := (div_eq_iff (heatDensity_pos μ ht x).ne').mp hs
    have hd := hasDerivAt_heatDensity_line μ ht x w 0
    simp only [zero_smul, add_zero] at hd
    exact hn ▸ hd
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ)
    ((integrable_heatDensity μ ht).const_mul (finiteLinearForm v w)) hprod
    (integrable_form_density μ hμ ht v) hf hg
  simp only [ContinuousLinearMap.mul_apply'] at h
  rw [integral_const_mul, integral_heatDensity μ ht, mul_one] at h
  exact h

/-- Full identity covariance determines all coefficients of the actual
linear score. This includes cross-channel and mixed spatial coefficients. -/
theorem linear_heatScore_of_identitySecondMoments
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (hmom : HasIdentitySecondMoments μ)
    {t : ℝ} (ht : 0 < t) (w a : I → ℝ)
    (hscore : ∀ x, heatDirectionalScore μ t w x = finiteLinearForm a x) :
    ∀ x, heatDirectionalScore μ t w x = -(1 / (1 + 2 * t)) * finiteLinearForm w x := by
  have ha (i : I) : a i = -(1 / (1 + 2 * t)) * w i := by
    let v : I → ℝ := Pi.single i 1
    have h := linear_heatScore_bilinear_identity μ hμ ht w a hscore v
    have hm := integral_heatDensity_mul_linearForm_mul μ hμ hmom ht v a
    have heq : (fun x => finiteLinearForm v x * (finiteLinearForm a x * heatDensity μ t x)) =
        (fun x => heatDensity μ t x * (finiteLinearForm v x * finiteLinearForm a x)) := by funext x; ring
    rw [heq, hm] at h
    simp [v, Pi.single_apply, finiteLinearForm] at h
    apply (mul_left_cancel₀ (by positivity : (1 + 2 * t : ℝ) ≠ 0))
    calc
      (1 + 2 * t) * a i = -(w i) := h
      _ = _ := by field_simp; ring
  intro x
  rw [hscore]
  unfold finiteLinearForm
  simp_rw [ha]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem heatDirectionalScore_gaussian_of_bilinear_quadratic_logshape
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (hmom : HasIdentitySecondMoments μ)
    {t : ℝ} (ht : 0 < t) (P : (I → ℝ) →ₗ[ℝ] (I → ℝ))
    (B : (I → ℝ) →L[ℝ] (I → ℝ) →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u)
    (hshape : ∀ x, Real.log (heatDensity μ t x) =
      Real.log (heatDensity μ t (P x)) + B (x - P x) (x - P x) / 2)
    (w : I → ℝ) (hw : P w = 0) :
    ∀ x, heatDirectionalScore μ t w x = -(1 / (1 + 2 * t)) * finiteLinearForm w x := by
  let A : (I → ℝ) →L[ℝ] ℝ := (B w).comp
    (ContinuousLinearMap.id ℝ (I → ℝ) - P.toContinuousLinearMap)
  apply linear_heatScore_of_identitySecondMoments μ hμ hmom ht w
    (fun i => A (Pi.single i 1))
  intro x
  rw [heatDirectionalScore_of_bilinear_quadratic_logshape μ ht P B hB hshape w hw x]
  exact clm_eq_finiteLinearForm A x

end GaussianWave.BS
