import GaussianWave.BS.ScoreRigidity
import GaussianWave.BS.EntropyEndpoint
import GaussianWave.BS.HeatCovariance

/-!
# Actual Gaussian product factorization from a quadratic log density

The independence conclusion below is an equality of actual probability
measures. It is proved from a separable logarithm using the explicit Gaussian
density, fiber normalization, and the product with-density formula.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal ContDiff

namespace GaussianWave.BS

/-- A quadratic discarded-coordinate logarithm implies literal independence
of the retained coordinates and a Gaussian discarded vector. The retained
law is the actual marginal of the actual heat convolution. -/
theorem splitHeatedLaw_eq_product_of_logshape
    {I J : Type*} [Fintype I] [Fintype J]
    (μ : Measure ((I ⊕ J) → ℝ)) [IsProbabilityMeasure μ]
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (hshape : ∀ (r : I → ℝ) (z : J → ℝ),
      Real.log (heatDensity μ t (Sum.elim r z)) =
        Real.log (heatDensity μ t (Sum.elim r 0)) - squareMass z / (4 * s)) :
    splitHeatedLaw μ t = (heatedLaw (Measure.map leftCoordinates μ) t).prod (heatGaussian J s) := by
  let a : (I → ℝ) → ℝ := fun r => heatDensity μ t (Sum.elim r 0) / heatKernelBound J s
  have hB : heatKernelBound J s ≠ 0 := (heatKernelBound_pos hs).ne'
  have hfactor (r : I → ℝ) (z : J → ℝ) :
      heatDensity μ t (Sum.elim r z) = a r * heatKernel s z := by
    rw [heatKernel_factor hs]
    have hh : heatDensity μ t (Sum.elim r z) =
        heatDensity μ t (Sum.elim r 0) * Real.exp (-squareMass z / (4 * s)) := by
      rw [← Real.exp_log (heatDensity_pos μ ht (Sum.elim r z)), hshape,
        sub_eq_add_neg, Real.exp_add, Real.exp_log (heatDensity_pos μ ht (Sum.elim r 0))]
      congr 2
      ring
    rw [hh]
    dsimp [a]
    field_simp
    ring
  have ha (r : I → ℝ) : a r = heatDensity (Measure.map leftCoordinates μ) t r := by
    rw [← fiber_heatDensity μ ht r]
    simp_rw [hfactor]
    rw [integral_const_mul, integral_heatKernel hs, mul_one]
  have hactual (r : I → ℝ) (z : J → ℝ) :
      heatDensity μ t (Sum.elim r z) =
        heatDensity (Measure.map leftCoordinates μ) t r * heatKernel s z := by
    rw [hfactor, ha]
  rw [heatedLaw_eq_withDensity (Measure.map leftCoordinates μ) ht, heatGaussian_eq_withDensity hs,
    prod_withDensity (measurable_heatDensity _ t).ennreal_ofReal
      (measurable_heatKernel s).ennreal_ofReal]
  unfold splitHeatedLaw splitHeatedDensity
  congr 1
  funext p
  rw [hactual, ENNReal.ofReal_mul (heatDensity_nonneg _ _ _)]

private theorem linearForm_orthogonal_complement
    {I : Type*} [Fintype I] (w x y : I → ℝ) :
    finiteLinearForm w (x - y) = finiteLinearForm w x - finiteLinearForm w y := by
  simp only [finiteLinearForm, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The actual smooth score in a transverse direction is computed from the
derived quadratic log shape. The projection conditions are ordinary finite
linear geometry, and Gaussian independence is not an assumption. -/
theorem heatDirectionalScore_of_quadratic_logshape
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (P : (I → ℝ) →ₗ[ℝ] (I → ℝ)) (κ : ℝ)
    (hshape : ∀ x, Real.log (heatDensity μ t x) =
      Real.log (heatDensity μ t (P x)) + (κ / 2) * squareMass (x - P x))
    (w : I → ℝ) (hw : P w = 0) (hperp : ∀ x, finiteLinearForm w (P x) = 0)
    (x : I → ℝ) : heatDirectionalScore μ t w x = κ * finiteLinearForm w x := by
  have heq : (fun s : ℝ => Real.log (heatDensity μ t (x + s • w))) =
      (fun s : ℝ => Real.log (heatDensity μ t (P x)) +
        (κ / 2) * squareMass ((x - P x) + s • w)) := by
    funext s
    rw [hshape, map_add, map_smul, hw, smul_zero, add_zero]
    congr 2
    congr 1
    abel
  have hs := (hasDerivAt_squareMass_line (x - P x) w 0).const_mul (κ / 2)
  have hsum : (∑ i, 2 * (x - P x) i * w i) = 2 * finiteLinearForm w x := by
    calc
      _ = 2 * finiteLinearForm w (x - P x) := by
        unfold finiteLinearForm
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := by rw [linearForm_orthogonal_complement, hperp, sub_zero]
  have hq : HasDerivAt (fun s : ℝ => Real.log (heatDensity μ t (P x)) +
      (κ / 2) * squareMass ((x - P x) + s • w)) (κ * finiteLinearForm w x) 0 := by
    convert hs.const_add (Real.log (heatDensity μ t (P x))) using 1
    simp only [zero_mul, add_zero]
    rw [hsum]
    ring
  rw [← heq] at hq
  have hl := ((contDiff_three_log_heatDensity μ ht).differentiable (by simp) x).hasFDerivAt.hasLineDerivAt w
  rw [heatDirectionalScore_eq_log_fderiv μ ht]
  exact hl.unique hq

private theorem integrable_linearForm_sq_density
    {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) (w : I → ℝ) :
    Integrable (fun x => finiteLinearForm w x ^ 2 * heatDensity μ t x) := by
  have hm : Measurable (finiteLinearForm w) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))
  apply ((integrable_heatDensity_mul_squareRadius μ hμ ht).const_mul (squareRadius w)).mono'
    ((hm.pow_const 2).mul (measurable_heatDensity μ t)).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (heatDensity_nonneg _ _ _))]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w x
  change finiteLinearForm w x ^ 2 ≤ squareRadius w * squareRadius x at hcs
  nlinarith [mul_le_mul_of_nonneg_right hcs (heatDensity_nonneg μ t x)]

/-- Integration by parts identifies the quadratic transverse coefficient from
the actual second moment. This avoids assuming a sign condition on that
coefficient or assuming a Gaussian product factorization. -/
theorem quadratic_logshape_coefficient_mul_secondMoment
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t)
    (P : (I → ℝ) →ₗ[ℝ] (I → ℝ)) (κ : ℝ)
    (hshape : ∀ x, Real.log (heatDensity μ t x) =
      Real.log (heatDensity μ t (P x)) + (κ / 2) * squareMass (x - P x))
    (w : I → ℝ) (hw : P w = 0) (hperp : ∀ x, finiteLinearForm w (P x) = 0)
    (hunit : squareRadius w = 1) :
    κ * (∫ x, finiteLinearForm w x ^ 2 * heatDensity μ t x) = -1 := by
  have h2 := integrable_linearForm_sq_density μ hμ ht w
  have hm : Measurable (finiteLinearForm w) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))
  have h1 : Integrable (fun x => finiteLinearForm w x * heatDensity μ t x) := by
    apply ((integrable_heatDensity μ ht).add h2).mono'
      (hm.mul (measurable_heatDensity μ t)).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatDensity_nonneg _ _ _)]
    have habs : |finiteLinearForm w x| ≤ 1 + finiteLinearForm w x ^ 2 := by
      nlinarith [sq_nonneg (|finiteLinearForm w x| - 1), sq_abs (finiteLinearForm w x)]
    change |finiteLinearForm w x| * heatDensity μ t x ≤
      heatDensity μ t x + finiteLinearForm w x ^ 2 * heatDensity μ t x
    nlinarith [mul_le_mul_of_nonneg_right habs (heatDensity_nonneg μ t x)]
  have hf (x : I → ℝ) : HasLineDerivAt ℝ (finiteLinearForm w) 1 x w := by
    change HasDerivAt (fun s : ℝ => finiteLinearForm w (x + s • w)) 1 0
    have hs : HasDerivAt (fun s : ℝ => ∑ i, w i * (x i + s * w i))
        (∑ i, w i * w i) 0 := by
      apply HasDerivAt.sum
      intro i _
      simpa using ((hasDerivAt_const 0 (x i)).add ((hasDerivAt_id 0).mul_const (w i))).const_mul (w i)
    convert hs using 1
    simpa only [squareRadius, pow_two] using hunit.symm
  have hg (x : I → ℝ) : HasLineDerivAt ℝ (heatDensity μ t)
      (κ * finiteLinearForm w x * heatDensity μ t x) x w := by
    have hs := heatDirectionalScore_of_quadratic_logshape μ ht P κ hshape w hw hperp x
    unfold heatDirectionalScore at hs
    have hn := (div_eq_iff (heatDensity_pos μ ht x).ne').mp hs
    have hd := hasDerivAt_heatDensity_line μ ht x w 0
    simp only [zero_smul, add_zero] at hd
    exact hn ▸ hd
  have hleft : Integrable (fun x => finiteLinearForm w x *
      (κ * finiteLinearForm w x * heatDensity μ t x)) := by
    convert h2.const_mul κ using 1
    funext x
    ring
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (by simpa only [one_mul, ContinuousLinearMap.mul_apply'] using integrable_heatDensity μ ht)
    hleft h1 hf hg
  have heq : (fun x => finiteLinearForm w x * (κ * finiteLinearForm w x * heatDensity μ t x)) =
      (fun x => κ * (finiteLinearForm w x ^ 2 * heatDensity μ t x)) := by funext x; ring
  simp only [ContinuousLinearMap.mul_apply', one_mul] at h
  rw [heq, integral_const_mul, integral_heatDensity μ ht] at h
  exact h

theorem quadratic_logshape_coefficient_of_identitySecondMoments
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (hmom : HasIdentitySecondMoments μ)
    {t : ℝ} (ht : 0 < t)
    (P : (I → ℝ) →ₗ[ℝ] (I → ℝ)) (κ : ℝ)
    (hshape : ∀ x, Real.log (heatDensity μ t x) =
      Real.log (heatDensity μ t (P x)) + (κ / 2) * squareMass (x - P x))
    (w : I → ℝ) (hw : P w = 0) (hperp : ∀ x, finiteLinearForm w (P x) = 0)
    (hunit : squareRadius w = 1) : κ = -(1 / (1 + 2 * t)) := by
  have h := quadratic_logshape_coefficient_mul_secondMoment μ hμ ht P κ hshape w hw hperp hunit
  have hm := integral_heatDensity_mul_unitLinearForm_sq μ hμ hmom ht w hunit
  simp_rw [mul_comm (heatDensity μ t _)] at hm
  rw [hm] at h
  rw [← neg_div]
  exact (eq_div_iff (by positivity : (1 + 2 * t : ℝ) ≠ 0)).mpr h

end GaussianWave.BS
