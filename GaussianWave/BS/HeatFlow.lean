import GaussianWave.GaussianLaws

/-!
# Actual Gaussian heat convolution for arbitrary mixing measures

The input measure is arbitrary, rather than a finite empirical mixture.
Positive heat times use variance `2*t` in every Euclidean coordinate.
The first layer constructs the actual convolution measure and proves its
Lebesgue density, positivity, and normalization. Entropy differentiation and
the de Bruijn identity are separate obligations, not assumptions here.

The finite-product density argument is adapted from the user's earlier
`GeneralizedBulk/Analysis/PiDensity.lean`; no old project is imported.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators ENNReal NNReal MeasureTheory

namespace GaussianWave.BS

section FiniteProductDensity
variable {I : Type*} [Fintype I]

private theorem integral_pi_product (μ : I → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : I → ℝ → ℝ) :
    (∫ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫ t, f i t ∂μ i := by
  let ms : I → MeasureSpace ℝ := fun i => ⟨μ i⟩
  have sf : ∀ i, @SigmaFinite ℝ _ (@volume ℝ (ms i)) := fun i => inferInstance
  simpa only [volume_pi] using
    @integral_fintype_prod_eq_prod ℝ _ I _ (fun _ => ℝ) f ms sf

private theorem integrable_pi_product (μ : I → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : I → ℝ → ℝ) (hf : ∀ i, Integrable (f i) (μ i)) :
    Integrable (fun x => ∏ i, f i (x i)) (Measure.pi μ) := by
  let ms : I → MeasureSpace ℝ := fun i => ⟨μ i⟩
  have sf : ∀ i, @SigmaFinite ℝ _ (@volume ℝ (ms i)) := fun i => inferInstance
  simpa only [volume_pi] using
    @Integrable.fintype_prod_dep ℝ _ I _ (fun _ => ℝ) f ms sf hf

private theorem pi_withDensity_ofReal (μ : I → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : I → ℝ → ℝ) (hf : ∀ i, Integrable (f i) (μ i))
    (hpos : ∀ i t, 0 ≤ f i t) :
    Measure.pi (fun i => (μ i).withDensity (fun t => ENNReal.ofReal (f i t))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  letI : ∀ i, IsFiniteMeasure ((μ i).withDensity (fun t => ENNReal.ofReal (f i t))) :=
    fun i => isFiniteMeasure_withDensity_ofReal (hf i).hasFiniteIntegral
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hprod := integrable_pi_product μ f hf
  rw [← ofReal_integral_eq_lintegral_ofReal hprod.restrict
    (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => hpos i (x i))))]
  rw [Measure.restrict_pi_pi, integral_pi_product]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hpos i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict (ae_of_all _ (hpos i))

end FiniteProductDensity

def heatVariance (t : ℝ) : ℝ≥0 := ⟨max (2 * t) 0, le_max_right _ _⟩

theorem heatVariance_pos {t : ℝ} (ht : 0 < t) : 0 < heatVariance t := by
  change 0 < max (2 * t) 0
  positivity

def heatKernel {I : Type*} [Fintype I] (t : ℝ) (x : I → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 (heatVariance t) (x i)

def heatKernelBound (I : Type*) [Fintype I] (t : ℝ) : ℝ :=
  ∏ _i : I, (Real.sqrt (2 * Real.pi * (heatVariance t : ℝ)))⁻¹

theorem heatKernel_nonneg {I : Type*} [Fintype I] (t : ℝ) (x : I → ℝ) :
    0 ≤ heatKernel t x :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 (heatVariance t) (x i)

theorem heatKernel_pos {I : Type*} [Fintype I] {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    0 < heatKernel t x :=
  Finset.prod_pos fun i _ => gaussianPDFReal_pos 0 (heatVariance t) (x i) (heatVariance_pos ht).ne'

theorem heatKernel_le_bound {I : Type*} [Fintype I] (t : ℝ) (x : I → ℝ) :
    heatKernel t x ≤ heatKernelBound I t := by
  apply Finset.prod_le_prod (fun i _ => gaussianPDFReal_nonneg 0 _ _)
  intro i _
  have he : Real.exp (-(x i) ^ 2 / (2 * (heatVariance t : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  simpa only [gaussianPDFReal, sub_zero, mul_one] using
    mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem continuous_heatKernel {I : Type*} [Fintype I] (t : ℝ) :
    Continuous (heatKernel (I := I) t) := by
  apply continuous_finset_prod
  intro i _
  unfold gaussianPDFReal
  fun_prop

theorem measurable_heatKernel {I : Type*} [Fintype I] (t : ℝ) :
    Measurable (heatKernel (I := I) t) := (continuous_heatKernel t).measurable

theorem integrable_heatKernel {I : Type*} [Fintype I] (t : ℝ) :
    Integrable (heatKernel (I := I) t) := by
  simpa only [heatKernel, ← volume_pi] using integrable_pi_product
    (fun _ : I => (volume : Measure ℝ)) (fun _ => gaussianPDFReal 0 (heatVariance t))
    (fun _ => integrable_gaussianPDFReal 0 _)

theorem integral_heatKernel {I : Type*} [Fintype I] {t : ℝ} (ht : 0 < t) :
    (∫ x : I → ℝ, heatKernel t x) = 1 := by
  change (∫ x : I → ℝ, ∏ i, gaussianPDFReal 0 (heatVariance t) (x i)) = 1
  rw [volume_pi, integral_pi_product]
  simp only [integral_gaussianPDFReal_eq_one 0 (heatVariance_pos ht).ne', Finset.prod_const_one]

/-- Actual independent Gaussian noise of coordinate variance `2*t`. -/
def heatGaussian (I : Type*) [Fintype I] (t : ℝ) : Measure (I → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 (heatVariance t))

instance {I : Type*} [Fintype I] (t : ℝ) : IsProbabilityMeasure (heatGaussian I t) := by
  unfold heatGaussian
  infer_instance

theorem heatGaussian_eq_withDensity {I : Type*} [Fintype I] {t : ℝ} (ht : 0 < t) :
    heatGaussian I t = volume.withDensity (fun x => ENNReal.ofReal (heatKernel t x)) := by
  unfold heatGaussian
  simp_rw [gaussianReal_of_var_ne_zero 0 (heatVariance_pos ht).ne']
  simp only [gaussianPDF_def]
  rw [pi_withDensity_ofReal (fun _ : I => (volume : Measure ℝ))
    (fun _ => gaussianPDFReal 0 (heatVariance t))
    (fun _ => integrable_gaussianPDFReal 0 _) (fun _ => gaussianPDFReal_nonneg 0 _)]
  rfl

/-- The actual law of the sum of independent input and Gaussian noise. -/
def heatedLaw {I : Type*} [Fintype I] (μ : Measure (I → ℝ)) (t : ℝ) : Measure (I → ℝ) :=
  Measure.conv μ (heatGaussian I t)

instance {I : Type*} [Fintype I] (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (t : ℝ) : IsProbabilityMeasure (heatedLaw μ t) := by
  unfold heatedLaw
  infer_instance

/-- The ordinary integral formula for the arbitrary-measure heat density. -/
def heatDensity {I : Type*} [Fintype I] (μ : Measure (I → ℝ)) (t : ℝ) (x : I → ℝ) : ℝ :=
  ∫ y, heatKernel t (x - y) ∂μ

theorem integrable_heatKernel_shift {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] (t : ℝ) (x : I → ℝ) :
    Integrable (fun y => heatKernel t (x - y)) μ := by
  apply (integrable_const (heatKernelBound I t)).mono'
    ((continuous_heatKernel t).comp (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable
  filter_upwards [] with y
  change |heatKernel t (x - y)| ≤ heatKernelBound I t
  rw [abs_of_nonneg (heatKernel_nonneg _ _)]
  exact heatKernel_le_bound _ _

theorem heatDensity_nonneg {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) (t : ℝ) (x : I → ℝ) : 0 ≤ heatDensity μ t x :=
  integral_nonneg fun y => heatKernel_nonneg t (x - y)

theorem measurable_heatDensity {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [SFinite μ] (t : ℝ) : Measurable (heatDensity μ t) := by
  have hm : StronglyMeasurable
      (fun z : (I → ℝ) × (I → ℝ) => heatKernel t (z.1 - z.2)) :=
    ((continuous_heatKernel t).comp (continuous_fst.sub continuous_snd)).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

theorem heatDensity_pos {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    0 < heatDensity μ t x := by
  apply (integral_pos_iff_support_of_nonneg (fun y => (heatKernel_pos ht _).le)
    (integrable_heatKernel_shift μ t x)).mpr
  have heq : Function.support (fun y => heatKernel t (x - y)) = Set.univ := by
    ext y
    simp [Function.mem_support, (heatKernel_pos ht (x - y)).ne']
  rw [heq, measure_univ]
  exact zero_lt_one

theorem heatDensity_le_bound {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] (t : ℝ) (x : I → ℝ) :
    heatDensity μ t x ≤ heatKernelBound I t := by
  calc
    _ ≤ ∫ _y, heatKernelBound I t ∂μ :=
      integral_mono (integrable_heatKernel_shift μ t x) (integrable_const _)
        (fun y => heatKernel_le_bound t (x - y))
    _ = _ := by simp

theorem ofReal_heatDensity {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] (t : ℝ) (x : I → ℝ) :
    ENNReal.ofReal (heatDensity μ t x) =
      ∫⁻ y, ENNReal.ofReal (heatKernel t (x - y)) ∂μ :=
  ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel_shift μ t x)
    (ae_of_all _ (fun y => heatKernel_nonneg t (x - y)))

/-- The integral formula is the Lebesgue density of the actual independent
Gaussian convolution, for an arbitrary finite input measure. -/
theorem heatedLaw_eq_withDensity {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) :
    heatedLaw μ t = volume.withDensity (fun x => ENNReal.ofReal (heatDensity μ t x)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  calc
    (∫⁻ x, g x ∂heatedLaw μ t) =
        ∫⁻ y, ∫⁻ z, ENNReal.ofReal (heatKernel t z) * g (y + z) ∂volume ∂μ := by
      rw [heatedLaw, Measure.lintegral_conv hg]
      apply lintegral_congr
      intro y
      rw [heatGaussian_eq_withDensity ht]
      exact lintegral_withDensity_eq_lintegral_mul volume
        (measurable_heatKernel t).ennreal_ofReal (hg.comp (measurable_const.add measurable_id))
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (heatKernel t (x - y)) * g x ∂volume ∂μ := by
      apply lintegral_congr
      intro y
      have hm : Measurable (fun x : I → ℝ =>
          ENNReal.ofReal (heatKernel t (x - y)) * g x) :=
        ((measurable_heatKernel t).comp (measurable_id.sub measurable_const)).ennreal_ofReal.mul hg
      have h := (measurePreserving_add_left (volume : Measure (I → ℝ)) y).lintegral_comp hm
      simpa only [add_sub_cancel_left] using h
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (heatKernel t (x - y)) * g x ∂μ ∂volume := by
      apply lintegral_lintegral_swap
      exact (((measurable_heatKernel t).comp (measurable_snd.sub measurable_fst)).ennreal_ofReal.mul
        (hg.comp measurable_snd)).aemeasurable
    _ = ∫⁻ x, ENNReal.ofReal (heatDensity μ t x) * g x ∂volume := by
      apply lintegral_congr
      intro x
      rw [lintegral_mul_const (μ := μ) (f := fun y : I → ℝ => ENNReal.ofReal (heatKernel t (x - y))) (g x)
        (((measurable_heatKernel t).comp (measurable_const.sub measurable_id)).ennreal_ofReal),
        ← ofReal_heatDensity μ t x]
    _ = ∫⁻ x, g x ∂volume.withDensity (fun x => ENNReal.ofReal (heatDensity μ t x)) :=
      (lintegral_withDensity_eq_lintegral_mul volume
        (measurable_heatDensity μ t).ennreal_ofReal hg).symm

theorem lintegral_heatDensity {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) :
    (∫⁻ x, ENNReal.ofReal (heatDensity μ t x)) = 1 := by
  have h := congrArg (fun ν : Measure (I → ℝ) => ν Set.univ) (heatedLaw_eq_withDensity μ ht)
  simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using h.symm

theorem integrable_heatDensity {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) :
    Integrable (heatDensity μ t) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_heatDensity μ t).aestronglyMeasurable
    (ae_of_all _ (fun x => heatDensity_nonneg μ t x))).mp
  rw [lintegral_heatDensity μ ht]
  exact ENNReal.one_ne_top

theorem integral_heatDensity {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) :
    (∫ x, heatDensity μ t x) = 1 := by
  have h := ofReal_integral_eq_lintegral_ofReal (integrable_heatDensity μ ht)
    (ae_of_all _ (fun x => heatDensity_nonneg μ t x))
  rw [lintegral_heatDensity μ ht] at h
  exact ENNReal.ofReal_eq_one.mp h

end GaussianWave.BS
