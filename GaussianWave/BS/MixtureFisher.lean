import GaussianWave.BS.GaussianReference
import GaussianWave.BS.HeatDerivatives

/-!
# Fisher information of an arbitrary Gaussian mixture

The central inequality here is proved by integrating a literal square against
the mixing measure. In particular it is not an assumed Fisher-information
inequality. The actual heat-kernel specialization is developed below it.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

/-- The weighted Cauchy--Schwarz estimate, proved by completing a square under
an arbitrary measure. All integrability requirements are explicit. -/
theorem weighted_integral_variance_nonneg
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (k s : Y → ℝ)
    (hk0 : ∀ y, 0 ≤ k y) (hki : Integrable k μ)
    (hksi : Integrable (fun y => k y * s y) μ)
    (hksqi : Integrable (fun y => k y * (s y) ^ 2) μ)
    (hmass : 0 < ∫ y, k y ∂μ) :
    (∫ y, k y * s y ∂μ) ^ 2 / (∫ y, k y ∂μ) ≤
      ∫ y, k y * (s y) ^ 2 ∂μ := by
  let a := ∫ y, k y ∂μ
  let b := ∫ y, k y * s y ∂μ
  let c := ∫ y, k y * (s y) ^ 2 ∂μ
  have heq : (fun y => k y * (s y - b / a) ^ 2) =
      (fun y => k y * (s y) ^ 2 - (2 * (b / a)) * (k y * s y) +
        (b / a) ^ 2 * k y) := by
    funext y
    ring
  have hn : 0 ≤ ∫ y, k y * (s y - b / a) ^ 2 ∂μ :=
    integral_nonneg (fun y => mul_nonneg (hk0 y) (sq_nonneg _))
  rw [heq,
    integral_add (f := fun y => k y * (s y) ^ 2 - (2 * (b / a)) * (k y * s y))
      (hksqi.sub (hksi.const_mul _)) (hki.const_mul _),
    integral_sub (f := fun y => k y * (s y) ^ 2) hksqi (hksi.const_mul _),
    integral_const_mul, integral_const_mul] at hn
  change 0 ≤ c - 2 * (b / a) * b + (b / a) ^ 2 * a at hn
  have ha : a ≠ 0 := hmass.ne'
  have hid : c - 2 * (b / a) * b + (b / a) ^ 2 * a = c - b ^ 2 / a := by
    field_simp
    ring
  rw [hid] at hn
  exact sub_nonneg.mp hn

/-- Equality in the weighted score estimate means that the score is constant
under the weighted mixing measure, as an actual almost-everywhere statement. -/
theorem weighted_integral_variance_eq_zero_iff
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (k s : Y → ℝ)
    (hk0 : ∀ y, 0 < k y) (hki : Integrable k μ)
    (hksi : Integrable (fun y => k y * s y) μ)
    (hksqi : Integrable (fun y => k y * (s y) ^ 2) μ)
    (hmass : 0 < ∫ y, k y ∂μ) :
    (∫ y, k y * (s y) ^ 2 ∂μ) -
      (∫ y, k y * s y ∂μ) ^ 2 / (∫ y, k y ∂μ) = 0 ↔
      ∀ᵐ y ∂μ, s y = (∫ z, k z * s z ∂μ) / (∫ z, k z ∂μ) := by
  let a := ∫ y, k y ∂μ
  let b := ∫ y, k y * s y ∂μ
  have heq : (fun y => k y * (s y - b / a) ^ 2) =
      (fun y => k y * (s y) ^ 2 - (2 * (b / a)) * (k y * s y) +
        (b / a) ^ 2 * k y) := by
    funext y
    ring
  have hi : Integrable (fun y => k y * (s y - b / a) ^ 2) μ := by
    rw [heq]
    exact (hksqi.sub (hksi.const_mul _)).add (hki.const_mul _)
  have hint : (∫ y, k y * (s y - b / a) ^ 2 ∂μ) =
      (∫ y, k y * (s y) ^ 2 ∂μ) - b ^ 2 / a := by
    rw [heq,
      integral_add (f := fun y => k y * (s y) ^ 2 - (2 * (b / a)) * (k y * s y))
        (hksqi.sub (hksi.const_mul _)) (hki.const_mul _),
      integral_sub (f := fun y => k y * (s y) ^ 2) hksqi (hksi.const_mul _),
      integral_const_mul, integral_const_mul]
    change (∫ y, k y * (s y) ^ 2 ∂μ) - 2 * (b / a) * b + (b / a) ^ 2 * a = _
    have ha : a ≠ 0 := hmass.ne'
    field_simp
    ring
  rw [← hint, integral_eq_zero_iff_of_nonneg (fun y => mul_nonneg (hk0 y).le (sq_nonneg _)) hi]
  constructor
  · intro h
    filter_upwards [h] with y hy
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hy).resolve_left (hk0 y).ne'))
  · intro h
    filter_upwards [h] with y hy
    simp [hy, a, b]

section ActualHeatFisher
variable {I : Type*} [Fintype I]

/-- The coordinate Fisher square of the actual heat density. -/
def heatFisherCoordinate (μ : Measure (I → ℝ)) (t : ℝ) (i : I) (x : I → ℝ) : ℝ :=
  (heatDensityGradient μ t x i) ^ 2 / heatDensity μ t x

def heatFisherInformation (μ : Measure (I → ℝ)) (t : ℝ) : ℝ :=
  ∫ x, ∑ i, heatFisherCoordinate μ t i x

/-- The component-noise Fisher square before taking the conditional mean. -/
def heatNoiseFisherKernel (t : ℝ) (i : I) (x : I → ℝ) : ℝ :=
  heatKernel t x * (x i) ^ 2 / (4 * t ^ 2)

theorem heatNoiseFisherKernel_nonneg (t : ℝ) (i : I) (x : I → ℝ) :
    0 ≤ heatNoiseFisherKernel t i x := by
  unfold heatNoiseFisherKernel
  exact div_nonneg (mul_nonneg (heatKernel_nonneg t x) (sq_nonneg _)) (by positivity)

theorem integrable_heatNoiseFisherKernel {t : ℝ} (ht : 0 < t) (i : I) :
    Integrable (heatNoiseFisherKernel t i) :=
  (integrable_heatKernel_mul_coordinate_sq ht i).div_const _

theorem integral_heatNoiseFisherKernel {t : ℝ} (ht : 0 < t) (i : I) :
    (∫ x, heatNoiseFisherKernel t i x) = 1 / (2 * t) := by
  unfold heatNoiseFisherKernel
  rw [integral_div, integral_heatKernel_mul_coordinate_sq ht i, coe_heatVariance ht.le]
  field_simp
  ring

theorem continuous_heatNoiseFisherKernel (t : ℝ) (i : I) :
    Continuous (heatNoiseFisherKernel t i) := by
  unfold heatNoiseFisherKernel
  exact ((continuous_heatKernel t).mul ((continuous_apply i).pow 2)).div_const _

theorem heatNoiseFisherKernel_le {t : ℝ} (ht : 0 < t) (i : I) (x : I → ℝ) :
    heatNoiseFisherKernel t i x ≤ (4 * t * heatKernelBound I t) / (4 * t ^ 2) := by
  unfold heatNoiseFisherKernel
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ squareMass x * heatKernel t x := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right
        (sq_coordinate_le_squareMass x i) (heatKernel_nonneg t x)
    _ ≤ _ := squareMass_mul_heatKernel_le ht x

theorem integrable_heatNoiseFisherKernel_shift
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t)
    (i : I) (x : I → ℝ) : Integrable (fun y => heatNoiseFisherKernel t i (x - y)) μ := by
  refine (integrable_const ((4 * t * heatKernelBound I t) / (4 * t ^ 2))).mono'
    (((continuous_heatNoiseFisherKernel t i).comp
      (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable) ?_
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (heatNoiseFisherKernel_nonneg _ _ _)]
  exact heatNoiseFisherKernel_le ht i _

/-- Pointwise mixture-score contraction, for the actual heat gradient. -/
theorem heatFisherCoordinate_le_noise
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (i : I) (x : I → ℝ) :
    heatFisherCoordinate μ t i x ≤ ∫ y, heatNoiseFisherKernel t i (x - y) ∂μ := by
  have hfirst : Integrable
      (fun y => heatKernel t (x - y) * (-(x - y) i / (2 * t))) μ := by
    simpa only [heatKernelGradient, mul_comm] using integrable_heatKernelGradient_shift μ ht x i
  have hsecond : Integrable
      (fun y => heatKernel t (x - y) * (-(x - y) i / (2 * t)) ^ 2) μ := by
    convert integrable_heatNoiseFisherKernel_shift μ ht i x using 1
    funext y
    unfold heatNoiseFisherKernel
    ring
  have h := weighted_integral_variance_nonneg μ
    (fun y => heatKernel t (x - y)) (fun y => -(x - y) i / (2 * t))
    (fun y => heatKernel_nonneg _ _) (integrable_heatKernel_shift μ t x) hfirst hsecond
    (heatDensity_pos μ ht x)
  convert h using 1
  · unfold heatFisherCoordinate heatDensityGradient heatKernelGradient heatDensity
    congr 2
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  · apply integral_congr_ae
    filter_upwards [] with y
    unfold heatNoiseFisherKernel
    ring

theorem integrable_heatNoiseFisherKernel_prod
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    Integrable (fun z : (I → ℝ) × (I → ℝ) => heatNoiseFisherKernel t i (z.2 - z.1))
      (μ.prod volume) := by
  have hm : AEStronglyMeasurable
      (fun z : (I → ℝ) × (I → ℝ) => heatNoiseFisherKernel t i (z.2 - z.1)) (μ.prod volume) :=
    ((continuous_heatNoiseFisherKernel t i).comp
    (continuous_snd.sub continuous_fst)).measurable.aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact ae_of_all _ (fun y => (integrable_heatNoiseFisherKernel ht i).comp_sub_right y)
  · have heq (y : I → ℝ) :
        (∫ x, ‖heatNoiseFisherKernel t i (x - y)‖) = 1 / (2 * t) := by
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (heatNoiseFisherKernel_nonneg _ _ _)]
      rw [integral_sub_right_eq_self, integral_heatNoiseFisherKernel ht i]
    simp_rw [heq]
    exact integrable_const _

theorem integrable_heatNoiseFisherMixture
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    Integrable (fun x => ∫ y, heatNoiseFisherKernel t i (x - y) ∂μ) :=
  (integrable_heatNoiseFisherKernel_prod μ ht i).integral_prod_right

theorem integral_heatNoiseFisherMixture
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    (∫ x, ∫ y, heatNoiseFisherKernel t i (x - y) ∂μ) = 1 / (2 * t) := by
  rw [← integral_prod_symm _ (integrable_heatNoiseFisherKernel_prod μ ht i),
    integral_prod _ (integrable_heatNoiseFisherKernel_prod μ ht i)]
  simp_rw [integral_sub_right_eq_self, integral_heatNoiseFisherKernel ht i]
  simp

theorem measurable_heatDensityGradient
    (μ : Measure (I → ℝ)) [SFinite μ] (t : ℝ) (i : I) :
    Measurable (fun x => heatDensityGradient μ t x i) := by
  have hm := ((continuous_heatKernelGradient t i).comp
    (continuous_fst.sub continuous_snd)).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

theorem measurable_heatFisherCoordinate
    (μ : Measure (I → ℝ)) [SFinite μ] (t : ℝ) (i : I) :
    Measurable (heatFisherCoordinate μ t i) :=
  ((measurable_heatDensityGradient μ t i).pow_const 2).div (measurable_heatDensity μ t)

theorem heatFisherCoordinate_nonneg
    (μ : Measure (I → ℝ)) (t : ℝ) (i : I) (x : I → ℝ) :
    0 ≤ heatFisherCoordinate μ t i x :=
  div_nonneg (sq_nonneg _) (heatDensity_nonneg _ _ _)

theorem integrable_heatFisherCoordinate
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    Integrable (heatFisherCoordinate μ t i) := by
  refine (integrable_heatNoiseFisherMixture μ ht i).mono'
    (measurable_heatFisherCoordinate μ t i).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (heatFisherCoordinate_nonneg _ _ _ _)]
  exact heatFisherCoordinate_le_noise μ ht i x

theorem integral_heatFisherCoordinate_le
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    (∫ x, heatFisherCoordinate μ t i x) ≤ 1 / (2 * t) := by
  have h := integral_mono (integrable_heatFisherCoordinate μ ht i)
    (integrable_heatNoiseFisherMixture μ ht i) (heatFisherCoordinate_le_noise μ ht i)
  rwa [integral_heatNoiseFisherMixture μ ht i] at h

/-- Gaussian smoothing gives finite Fisher information for every probability
input, even when the input itself has no density or second moment. -/
theorem heatFisherInformation_le
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) :
    heatFisherInformation μ t ≤ (Fintype.card I : ℝ) / (2 * t) := by
  unfold heatFisherInformation
  rw [integral_finset_sum _ (fun i _ => integrable_heatFisherCoordinate μ ht i)]
  calc
    _ ≤ ∑ _i : I, 1 / (2 * t) := Finset.sum_le_sum fun i _ => integral_heatFisherCoordinate_le μ ht i
    _ = _ := by simp; ring

end ActualHeatFisher

end GaussianWave.BS
