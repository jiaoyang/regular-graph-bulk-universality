import GaussianWave.BS.HeatDerivatives

/-!
# Genuine Fréchet differentiability of the arbitrary-measure heat density

Uniform bounds for Gaussian derivatives justify differentiating the finite
mixing integral in the finite-dimensional function space. This upgrades the
line-derivative formulas to the actual derivative used by marginal scores.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators ContDiff
namespace GaussianWave.BS
variable {I : Type*} [Fintype I]

theorem contDiff_heatKernel (t : ℝ) : ContDiff ℝ ∞ (heatKernel (I := I) t) := by
  unfold heatKernel gaussianPDFReal
  apply contDiff_prod
  intro i _
  simp only [div_eq_mul_inv]
  fun_prop

theorem fderiv_heatKernel_apply {t : ℝ} (ht : 0 < t) (x v : I → ℝ) :
    fderiv ℝ (heatKernel t) x v = ∑ i, heatKernelGradient t x i * v i := by
  have hf := (contDiff_heatKernel (I := I) t).differentiable (by simp)
  have h1 := (hf x).hasFDerivAt.hasLineDerivAt v
  have h2 := hasDerivAt_heatKernel_line_gradient ht x v 0
  simp only [zero_smul, add_zero] at h2
  exact h1.unique h2

theorem norm_fderiv_heatKernel_le {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    ‖fderiv ℝ (heatKernel t) x‖ ≤ (Fintype.card I : ℝ) * heatGradientBound I t := by
  have hb : 0 ≤ heatGradientBound I t := by
    unfold heatGradientBound
    exact div_nonneg (mul_nonneg (by positivity) (heatKernelBound_nonneg I t)) (by positivity)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hb)
  intro v
  rw [fderiv_heatKernel_apply ht]
  calc
    _ ≤ ∑ i, ‖heatKernelGradient t x i * v i‖ := norm_sum_le _ _
    _ = ∑ i, ‖heatKernelGradient t x i‖ * ‖v i‖ := by simp_rw [norm_mul]
    _ ≤ ∑ _i : I, heatGradientBound I t * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (norm_heatKernelGradient_le ht x i) (norm_le_pi_norm v i)
        (norm_nonneg _) hb
    _ = _ := by simp; ring

/-- The actual derivative operator, as an ordinary absolutely convergent
Bochner integral of the actual Gaussian derivative operators. -/
def heatDensityFDeriv (μ : Measure (I → ℝ)) (t : ℝ) (x : I → ℝ) :
    (I → ℝ) →L[ℝ] ℝ := ∫ y, fderiv ℝ (heatKernel t) (x - y) ∂μ

theorem continuous_heatDensityFDeriv
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) :
    Continuous (heatDensityFDeriv μ t) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated
    (bound := fun _ => (Fintype.card I : ℝ) * heatGradientBound I t)
  · exact Eventually.of_forall (fun z =>
      (((contDiff_heatKernel t).continuous_fderiv (by simp)).comp
        (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)
  · exact Eventually.of_forall (fun z =>
      ae_of_all _ (fun y => norm_fderiv_heatKernel_le ht (z - y)))
  · exact integrable_const _
  · exact ae_of_all _ (fun y =>
      (((contDiff_heatKernel t).continuous_fderiv (by simp)).comp
        (continuous_id.sub continuous_const)).continuousAt)

theorem hasFDerivAt_heatDensity
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    HasFDerivAt (heatDensity μ t) (heatDensityFDeriv μ t x) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y : I → ℝ => heatKernel t (z - y))
    (F' := fun z y : I → ℝ => fderiv ℝ (heatKernel t) (z - y))
    (bound := fun _ => (Fintype.card I : ℝ) * heatGradientBound I t)
    (ε := 1) zero_lt_one
  · exact Eventually.of_forall (fun z =>
      ((continuous_heatKernel t).comp (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)
  · exact integrable_heatKernel_shift μ t x
  · exact (((contDiff_heatKernel t).continuous_fderiv (by simp)).comp
      (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable
  · exact ae_of_all _ (fun y z _ => norm_fderiv_heatKernel_le ht (z - y))
  · exact integrable_const _
  · apply ae_of_all
    intro y z _
    have hk := ((contDiff_heatKernel (I := I) t).differentiable (by simp) (z - y)).hasFDerivAt
    simpa only [ContinuousLinearMap.comp_id] using hk.comp z (hasFDerivAt_sub_const y)

theorem contDiff_one_heatDensity
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 1 (heatDensity μ t) :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨heatDensityFDeriv μ t, continuous_heatDensityFDeriv μ ht, hasFDerivAt_heatDensity μ ht⟩

theorem continuous_heatDensity
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) :
    Continuous (heatDensity μ t) := (contDiff_one_heatDensity μ ht).continuous

theorem fderiv_heatDensity_apply
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (x v : I → ℝ) :
    fderiv ℝ (heatDensity μ t) x v = ∑ i, heatDensityGradient μ t x i * v i := by
  have h1 := (hasFDerivAt_heatDensity μ ht x).hasLineDerivAt v
  have h2 := hasDerivAt_heatDensity_line μ ht x v 0
  simp only [zero_smul, add_zero] at h2
  rw [(hasFDerivAt_heatDensity μ ht x).fderiv]
  exact h1.unique h2

end GaussianWave.BS
