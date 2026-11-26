import GeneralizedBulk.Entropy.GaussianAffineEntropy
import GeneralizedBulk.Analysis.RealDensityIntegration

/-! The actual differential-entropy Jacobian for every positive probability density. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace GeneralizedBulk.Analysis
open GeneralizedBulk.Entropy
variable {I : Type*} [Fintype I] [DecidableEq I]

def linearDensity (M : Matrix I I ℝ) (f : (I → ℝ) → ℝ) (x : I → ℝ) : ℝ :=
  |M.det|⁻¹ * f (M⁻¹.mulVec x)

theorem measurable_linearDensity (M : Matrix I I ℝ) (f : (I → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (linearDensity M f) :=
  (hf.comp (GeneralizedBulk.Gaussian.measurable_finiteMatrixAction M⁻¹)).const_mul _

theorem linearDensity_pullback (M : Matrix I I ℝ) (hM : M.det ≠ 0) (f : (I → ℝ) → ℝ) (x : I → ℝ) :
    linearDensity M f (M.mulVec x) = |M.det|⁻¹ * f x := by
  unfold linearDensity
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]

theorem linearDensity_pushforward (M : Matrix I I ℝ) (hM : M.det ≠ 0) (f : (I → ℝ) → ℝ) (hf : Measurable f) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).map (matrixMeasurableEquiv M hM) =
      volume.withDensity (fun x => ENNReal.ofReal (linearDensity M f x)) := by
  apply map_realDensity_scaled_reference volume (matrixMeasurableEquiv M hM) |M.det|⁻¹ (by positivity) _ f hf
  change (volume : Measure (I → ℝ)).map (Matrix.toLin' M) = _
  simpa only [abs_inv] using Real.map_matrix_volume_pi_eq_smul_volume_pi hM

theorem linearDensity_entropy_change (M : Matrix I I ℝ) (hM : M.det ≠ 0)
    (f : (I → ℝ) → ℝ) (hf : Measurable f) (hp : ∀ x, 0 < f x)
    (hflog : Integrable (fun x => f x * Real.log (f x)))
    (hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))) :
    -(∫ x, linearDensity M f x * Real.log (linearDensity M f x)) =
      -(∫ x, f x * Real.log (f x)) + Real.log (|M.det|) := by
  let μ : Measure (I → ℝ) := volume.withDensity (fun x => ENNReal.ofReal (f x))
  let ν : Measure (I → ℝ) := volume.withDensity (fun x => ENNReal.ofReal (linearDensity M f x))
  letI : IsProbabilityMeasure μ := hprob
  have hmap : μ.map (matrixMeasurableEquiv M hM) = ν := linearDensity_pushforward M hM f hf
  have hlog : Integrable (fun x => Real.log (f x)) μ :=
    (integrable_realDensity_iff volume f _ hf (fun x => (hp x).le)).mpr hflog
  have hlogpull (x : I → ℝ) : Real.log (linearDensity M f (M.mulVec x)) =
      -Real.log (|M.det|) + Real.log (f x) := by
    rw [linearDensity_pullback M hM, Real.log_mul (inv_ne_zero (abs_ne_zero.mpr hM)) (hp x).ne', Real.log_inv]
  have hlogν : Integrable (fun x => Real.log (linearDensity M f x)) ν := by
    rw [← hmap]
    apply (integrable_map_equiv (matrixMeasurableEquiv M hM) _).mpr
    change Integrable (fun x => Real.log (linearDensity M f (M.mulVec x))) μ
    simp_rw [hlogpull]
    exact (integrable_const _).add hlog
  have hinner : (∫ x, Real.log (linearDensity M f x) ∂ν) =
      -Real.log (|M.det|) + ∫ x, Real.log (f x) ∂μ := by
    rw [← hmap, integral_map (matrixMeasurableEquiv M hM).measurable.aemeasurable]
    · change (∫ x, Real.log (linearDensity M f (M.mulVec x)) ∂μ) = _
      simp_rw [hlogpull]
      rw [integral_add (integrable_const _) hlog, integral_const]
      simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul]
    · rw [hmap]
      exact hlogν.aestronglyMeasurable
  have heν := integral_realDensity volume (linearDensity M f) (fun x => Real.log (linearDensity M f x))
    (measurable_linearDensity M f hf) (fun x => mul_nonneg (by positivity) (hp _).le)
  have heμ := integral_realDensity volume f (fun x => Real.log (f x)) hf (fun x => (hp x).le)
  change (∫ x, Real.log (linearDensity M f x) ∂ν) = _ at heν
  change (∫ x, Real.log (f x) ∂μ) = _ at heμ
  rw [heν, heμ] at hinner
  linarith

end GeneralizedBulk.Analysis
