import GaussianWave.BS.DensityEntropy
import GaussianWave.BS.GaussianReference
import GaussianWave.GaussianProduct

/-!
# Arbitrary-mixture entropy lower bounds for the heat-flow endpoint

The mixing measure is an actual arbitrary probability measure. The entropy
comparison is proved using Gibbs' inequality and Fubini, rather than supplied
as an entropy-concavity or Gaussian-maximum premise. Finite second moments
supply finite entropy, logarithmic envelopes, and exact convolution moments.
The derived Gaussian entropy squeeze proves the normalized large-time limit.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace GaussianWave.BS

/-- Concavity of differential entropy for an actual arbitrary density mixture.
The product integrability hypotheses ensure that all Fubini operations and
entropy subtractions refer to genuine finite integrals. -/
theorem densityEntropy_mixture_ge_mean
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (m : Measure X) [SFinite m] (μ : Measure Y) [IsProbabilityMeasure μ]
    (p : Y → X → ℝ) (f : X → ℝ)
    (hp0 : ∀ y x, 0 ≤ p y x) (hfpos : ∀ x, 0 < f x)
    (hpi : ∀ y, Integrable (p y) m) (hfi : Integrable f m)
    (hpone : ∀ y, (∫ x, p y x ∂m) = 1) (hfone : (∫ x, f x ∂m) = 1)
    (hmix : ∀ x, f x = ∫ y, p y x ∂μ)
    (hplog : Integrable (fun z : Y × X => p z.1 z.2 * Real.log (p z.1 z.2)) (μ.prod m))
    (hcross : Integrable (fun z : Y × X => p z.1 z.2 * Real.log (f z.2)) (μ.prod m)) :
    (∫ y, densityEntropy m (p y) ∂μ) ≤ densityEntropy m f := by
  have hineq : ∀ᵐ y ∂μ,
      densityEntropy m (p y) ≤ -(∫ x, p y x * Real.log (f x) ∂m) := by
    filter_upwards [hplog.prod_right_ae, hcross.prod_right_ae] with y hylog hycross
    exact densityEntropy_le_crossEntropy m (p y) f (hp0 y) hfpos
      (hpi y) hfi (hpone y) hfone hylog hycross
  have hleft : Integrable (fun y => densityEntropy m (p y)) μ := hplog.integral_prod_left.neg
  have hright : Integrable (fun y => -(∫ x, p y x * Real.log (f x) ∂m)) μ :=
    hcross.integral_prod_left.neg
  calc
    _ ≤ ∫ y, -(∫ x, p y x * Real.log (f x) ∂m) ∂μ := integral_mono_ae hleft hright hineq
    _ = densityEntropy m f := by
      rw [integral_neg, integral_integral_swap hcross]
      unfold densityEntropy
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      rw [integral_mul_const, ← hmix x]

/-- The cross product integrability needed above follows from integrability of
the mixture's entropy integrand. It is proved on the full product measure. -/
theorem integrable_mixture_cross
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (m : Measure X) [SFinite m] (μ : Measure Y) [IsProbabilityMeasure μ]
    (p : Y → X → ℝ) (f : X → ℝ)
    (hp : Measurable (fun z : Y × X => p z.1 z.2)) (hf : Measurable f)
    (hp0 : ∀ y x, 0 ≤ p y x)
    (hpint : ∀ x, Integrable (fun y => p y x) μ)
    (hmix : ∀ x, f x = ∫ y, p y x ∂μ)
    (hflog : Integrable (fun x => f x * Real.log (f x)) m) :
    Integrable (fun z : Y × X => p z.1 z.2 * Real.log (f z.2)) (μ.prod m) := by
  have hmeas : AEStronglyMeasurable
      (fun z : Y × X => p z.1 z.2 * Real.log (f z.2)) (μ.prod m) :=
    (hp.mul ((Real.measurable_log.comp hf).comp measurable_snd)).aestronglyMeasurable
  apply (integrable_prod_iff' hmeas).mpr
  constructor
  · exact Eventually.of_forall (fun x => (hpint x).mul_const (Real.log (f x)))
  · have heq (x : X) :
        (∫ y, ‖p y x * Real.log (f x)‖ ∂μ) = ‖f x * Real.log (f x)‖ := by
      have hf0 : 0 ≤ f x := by rw [hmix]; exact integral_nonneg (fun y => hp0 y x)
      simp_rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 _ x)]
      rw [integral_mul_const, ← hmix x, abs_of_nonneg hf0]
    simp_rw [heq]
    exact hflog.norm

/-- Jensen's logarithm inequality, proved by the tangent-line bound for `log`.
All integrability requirements are genuine and explicit. -/
theorem integral_log_le_log_integral
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (z : Y → ℝ) (hz : ∀ y, 0 < z y) (hzi : Integrable z μ)
    (hzlog : Integrable (fun y => Real.log (z y)) μ)
    (hmean : 0 < ∫ y, z y ∂μ) :
    (∫ y, Real.log (z y) ∂μ) ≤ Real.log (∫ y, z y ∂μ) := by
  let a := ∫ y, z y ∂μ
  have hp (y : Y) : Real.log (z y) ≤ z y / a - 1 + Real.log a := by
    have hh := Real.log_le_sub_one_of_pos (div_pos (hz y) hmean)
    rw [Real.log_div (hz y).ne' hmean.ne'] at hh
    linarith
  have hi : Integrable (fun y => z y / a - 1 + Real.log a) μ :=
    ((hzi.div_const a).sub (integrable_const 1)).add (integrable_const _)
  have hh := integral_mono hzlog hi hp
  rw [integral_add (f := fun y => z y / a - 1)
    ((hzi.div_const a).sub (integrable_const 1)) (integrable_const _),
    integral_sub (f := fun y => z y / a) (hzi.div_const a) (integrable_const 1), integral_div] at hh
  simpa [a, hmean.ne'] using hh

lemma squareRadius_nonneg {I : Type*} [Fintype I] (x : I → ℝ) :
    0 ≤ squareRadius x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma continuous_squareRadius {I : Type*} [Fintype I] :
    Continuous (squareRadius : (I → ℝ) → ℝ) :=
  continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2)

lemma squareRadius_add_le {I : Type*} [Fintype I] (x y : I → ℝ) :
    squareRadius (x + y) ≤ 2 * squareRadius x + 2 * squareRadius y := by
  calc
    _ ≤ ∑ i, (2 * x i ^ 2 + 2 * y i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      change (x i + y i) ^ 2 ≤ _
      nlinarith [sq_nonneg (x i - y i)]
    _ = _ := by simp only [squareRadius, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma squareRadius_sub_le {I : Type*} [Fintype I] (x y : I → ℝ) :
    squareRadius (x - y) ≤ 2 * squareRadius x + 2 * squareRadius y := by
  simpa only [sub_eq_add_neg, squareRadius, Pi.neg_apply, neg_sq] using squareRadius_add_le x (-y)

lemma integrable_squareRadius_sub {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (x : I → ℝ) :
    Integrable (fun y => squareRadius (x - y)) μ := by
  apply ((integrable_const (2 * squareRadius x)).add (hμ.const_mul 2)).mono'
    (continuous_squareRadius.comp (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable
  filter_upwards [] with y
  change |squareRadius (x - y)| ≤ 2 * squareRadius x + 2 * squareRadius y
  rw [abs_of_nonneg (squareRadius_nonneg _)]
  exact squareRadius_sub_le x y

/-- Finite input second moment gives a genuine finite second moment after
actual independent Gaussian convolution. -/
theorem integrable_heatedLaw_squareRadius {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (t : ℝ) :
    Integrable (squareRadius (I := I)) (heatedLaw μ t) := by
  have hG := integrable_heatGaussian_squareRadius (I := I) t
  have hl : Integrable (fun z : (I → ℝ) × (I → ℝ) => squareRadius z.1)
      (μ.prod (heatGaussian I t)) := by
    simpa only [mul_one] using hμ.mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : I → ℝ => (1 : ℝ)) (heatGaussian I t))
  have hr : Integrable (fun z : (I → ℝ) × (I → ℝ) => squareRadius z.2)
      (μ.prod (heatGaussian I t)) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : I → ℝ => (1 : ℝ)) μ).mul_prod hG
  have hadd : Integrable (fun z : (I → ℝ) × (I → ℝ) => squareRadius (z.1 + z.2))
      (μ.prod (heatGaussian I t)) := by
    apply ((hl.const_mul 2).add (hr.const_mul 2)).mono'
      (continuous_squareRadius.comp (continuous_fst.add continuous_snd)).measurable.aestronglyMeasurable
    filter_upwards [] with z
    change |squareRadius (z.1 + z.2)| ≤ 2 * squareRadius z.1 + 2 * squareRadius z.2
    rw [abs_of_nonneg (squareRadius_nonneg _)]
    exact squareRadius_add_le _ _
  change Integrable squareRadius (Measure.map (fun z : (I → ℝ) × (I → ℝ) => z.1 + z.2)
    (μ.prod (heatGaussian I t)))
  exact (integrable_map_measure continuous_squareRadius.measurable.aestronglyMeasurable
    (measurable_fst.add measurable_snd).aemeasurable).mpr hadd

/-- The actual heated Lebesgue density has an integrable radial second moment. -/
theorem integrable_heatDensity_mul_squareRadius {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => heatDensity μ t x * squareRadius x) := by
  have hi := integrable_heatedLaw_squareRadius μ hμ t
  rw [heatedLaw_eq_withDensity μ ht] at hi
  have hh := (integrable_withDensity_iff_integrable_smul'
    (measurable_heatDensity μ t).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hi
  simpa only [ENNReal.toReal_ofReal (heatDensity_nonneg _ _ _), smul_eq_mul] using hh

/-- A finite input second moment makes the logarithm of each shifted Gaussian
component integrable against the mixing law. -/
theorem integrable_log_heatKernel_shift {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    Integrable (fun y => Real.log (heatKernel t (x - y))) μ := by
  have heq : (fun y => Real.log (heatKernel t (x - y))) =
      (fun y => -((Fintype.card I : ℝ) / 2) * Real.log (2 * Real.pi * (heatVariance t : ℝ)) -
        squareRadius (x - y) / (2 * (heatVariance t : ℝ))) := by
    funext y
    exact log_heatKernel ht _
  rw [heq]
  exact (integrable_const _).sub ((integrable_squareRadius_sub μ hμ x).div_const _)

/-- Jensen provides a quantitative quadratic lower bound for the logarithm
of the actual arbitrary-mixture heat density. -/
theorem log_heatDensity_lower {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    -((Fintype.card I : ℝ) / 2) * Real.log (2 * Real.pi * (heatVariance t : ℝ)) -
      (2 * squareRadius x + 2 * ∫ y, squareRadius y ∂μ) / (2 * (heatVariance t : ℝ)) ≤
        Real.log (heatDensity μ t x) := by
  have hj := integral_log_le_log_integral μ (fun y => heatKernel t (x - y))
    (fun y => heatKernel_pos ht _) (integrable_heatKernel_shift μ t x)
    (integrable_log_heatKernel_shift μ hμ ht x) (heatDensity_pos μ ht x)
  change (∫ y, Real.log (heatKernel t (x - y)) ∂μ) ≤ Real.log (heatDensity μ t x) at hj
  have heq : (∫ y, Real.log (heatKernel t (x - y)) ∂μ) =
      -((Fintype.card I : ℝ) / 2) * Real.log (2 * Real.pi * (heatVariance t : ℝ)) -
        (∫ y, squareRadius (x - y) ∂μ) / (2 * (heatVariance t : ℝ)) := by
    simp_rw [log_heatKernel ht]
    rw [integral_sub (integrable_const _)
      ((integrable_squareRadius_sub μ hμ x).div_const _), integral_div]
    simp
  have hb : (∫ y, squareRadius (x - y) ∂μ) ≤
      2 * squareRadius x + 2 * ∫ y, squareRadius y ∂μ := by
    have h := integral_mono (integrable_squareRadius_sub μ hμ x)
      ((integrable_const (2 * squareRadius x)).add (hμ.const_mul 2))
      (squareRadius_sub_le x)
    change (∫ y, squareRadius (x - y) ∂μ) ≤
      ∫ y, 2 * squareRadius x + 2 * squareRadius y ∂μ at h
    rw [integral_add (f := fun _ => 2 * squareRadius x) (integrable_const _)
      (hμ.const_mul 2), integral_const, measureReal_univ_eq_one, one_smul,
      integral_const_mul] at h
    exact h
  rw [heq] at hj
  have hd : 0 ≤ 2 * (heatVariance t : ℝ) := by positivity
  have hh := div_le_div_of_nonneg_right hb hd
  linarith

/-- A bounded positive density with a quadratic lower log bound has a finite
entropy integrand as soon as its density-weighted second moment is finite. -/
theorem integrable_density_log_of_quadratic_lower {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) (hf : Measurable f) (hfpos : ∀ x, 0 < f x)
    (hfi : Integrable f) (hfq : Integrable (fun x => f x * squareRadius x))
    (K A B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hbound : ∀ x, f x ≤ K)
    (hlower : ∀ x, A - B * squareRadius x ≤ Real.log (f x)) :
    Integrable (fun x => f x * Real.log (f x)) := by
  apply ((hfi.const_mul (K + 1 + |A|)).add (hfq.const_mul B)).mono'
    (hf.mul (Real.measurable_log.comp hf)).aestronglyMeasurable
  filter_upwards [] with x
  have hR := squareRadius_nonneg x
  have hBR : 0 ≤ B * squareRadius x := mul_nonneg hB hR
  have hupper : Real.log (f x) ≤ K - 1 :=
    (Real.log_le_sub_one_of_pos (hfpos x)).trans (by linarith [hbound x])
  have habs : |Real.log (f x)| ≤ K + 1 + |A| + B * squareRadius x := by
    apply abs_le.mpr
    constructor
    · linarith [hlower x, (abs_le.mp (le_refl |A|)).1]
    · linarith [abs_nonneg A]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hfpos x).le]
  have hh := mul_le_mul_of_nonneg_left habs (hfpos x).le
  change f x * |Real.log (f x)| ≤ (K + 1 + |A|) * f x + B * (f x * squareRadius x)
  nlinarith

/-- Every actual positive-time Gaussian convolution of a finite-second-moment
probability law has finite differential entropy; no entropy premise is used. -/
theorem integrable_heatDensity_log {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => heatDensity μ t x * Real.log (heatDensity μ t x)) := by
  let v : ℝ := heatVariance t
  let M := ∫ y, squareRadius y ∂μ
  let A := -((Fintype.card I : ℝ) / 2) * Real.log (2 * Real.pi * v) - M / v
  have hv : 0 < v := by dsimp [v]; exact_mod_cast heatVariance_pos ht
  apply integrable_density_log_of_quadratic_lower (heatDensity μ t)
    (measurable_heatDensity μ t) (heatDensity_pos μ ht)
    (integrable_heatDensity μ ht) (integrable_heatDensity_mul_squareRadius μ hμ ht)
    (heatKernelBound I t) A (1 / v)
  · unfold heatKernelBound
    exact Finset.prod_nonneg (fun _ _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
  · positivity
  · exact heatDensity_le_bound μ t
  · intro x
    have h := log_heatDensity_lower μ hμ ht x
    have heq : A - (1 / v) * squareRadius x =
        -((Fintype.card I : ℝ) / 2) * Real.log (2 * Real.pi * (heatVariance t : ℝ)) -
          (2 * squareRadius x + 2 * ∫ y, squareRadius y ∂μ) /
            (2 * (heatVariance t : ℝ)) := by
      dsimp [A, M, v]
      field_simp
      ring
    rw [heq]
    exact h

/-- Translation preserves the actual Lebesgue integral on finite real coordinates. -/
lemma integral_sub_right_eq {I : Type*} [Fintype I]
    (g : (I → ℝ) → ℝ) (y : I → ℝ) :
    (∫ x, g (x - y)) = ∫ x, g x := by
  have hh := (measurePreserving_add_right (volume : Measure (I → ℝ)) (-y)).integral_comp
    (MeasurableEquiv.addRight (-y)).measurableEmbedding g
  simpa only [sub_eq_add_neg] using hh

lemma integrable_sub_right {I : Type*} [Fintype I]
    (g : (I → ℝ) → ℝ) (hg : Integrable g) (y : I → ℝ) :
    Integrable (fun x => g (x - y)) := by
  have hh := ((measurePreserving_add_right (volume : Measure (I → ℝ)) (-y)).integrable_comp
    hg.aestronglyMeasurable).mpr hg
  simpa only [Function.comp_def, sub_eq_add_neg] using hh

/-- Translated Gaussian component entropy integrands are integrable on the
entire arbitrary-mixture product probability/Lebesgue space. -/
theorem integrable_heatComponent_log {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : (I → ℝ) × (I → ℝ) =>
      heatKernel t (z.2 - z.1) * Real.log (heatKernel t (z.2 - z.1))) (μ.prod volume) := by
  have hk := integrable_heatKernel_log (I := I) ht
  have hmeas : Measurable (fun z : (I → ℝ) × (I → ℝ) =>
      heatKernel t (z.2 - z.1) * Real.log (heatKernel t (z.2 - z.1))) :=
    ((measurable_heatKernel t).comp (measurable_snd.sub measurable_fst)).mul
    (Real.measurable_log.comp ((measurable_heatKernel t).comp (measurable_snd.sub measurable_fst)))
  apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall (fun y => integrable_sub_right _ hk y)
  · have heq (y : I → ℝ) :
        (∫ x, ‖heatKernel t (x - y) * Real.log (heatKernel t (x - y))‖) =
          ∫ x : I → ℝ, ‖heatKernel t x * Real.log (heatKernel t x)‖ :=
      integral_sub_right_eq (fun x => ‖heatKernel t x * Real.log (heatKernel t x)‖) y
    simp_rw [heq]
    exact integrable_const _

/-- Actual Gaussian-convolution entropy is at least the Gaussian noise entropy,
for every finite-second-moment mixing law. All integrability hypotheses of
Gibbs and Fubini are discharged from that moment assumption. -/
theorem densityEntropy_heatDensity_ge_heatKernel {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) :
    densityEntropy volume (heatKernel (I := I) t) ≤ densityEntropy volume (heatDensity μ t) := by
  have hflog := integrable_heatDensity_log μ hμ ht
  have hcross := integrable_mixture_cross volume μ
    (fun y x => heatKernel t (x - y)) (heatDensity μ t)
    ((measurable_heatKernel t).comp (measurable_snd.sub measurable_fst))
    (measurable_heatDensity μ t) (fun y x => heatKernel_nonneg t _)
    (integrable_heatKernel_shift μ t) (fun _ => rfl) hflog
  have hh := densityEntropy_mixture_ge_mean volume μ
    (fun y x => heatKernel t (x - y)) (heatDensity μ t)
    (fun y x => heatKernel_nonneg t _) (heatDensity_pos μ ht)
    (fun y => integrable_sub_right _ (integrable_heatKernel t) y)
    (integrable_heatDensity μ ht)
    (fun y => by rw [integral_sub_right_eq, integral_heatKernel ht])
    (integral_heatDensity μ ht) (fun _ => rfl) (integrable_heatComponent_log μ ht) hcross
  have heq (y : I → ℝ) : densityEntropy volume (fun x => heatKernel t (x - y)) =
      densityEntropy volume (heatKernel (I := I) t) := by
    unfold densityEntropy
    rw [integral_sub_right_eq (fun x => heatKernel t x * Real.log (heatKernel t x)) y]
  simp_rw [heq] at hh
  simpa using hh

theorem gaussianEntropyValue_le_densityEntropy_heatDensity {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) :
    gaussianEntropyValue I (heatVariance t) ≤ densityEntropy volume (heatDensity μ t) := by
  rw [← densityEntropy_heatKernel ht]
  exact densityEntropy_heatDensity_ge_heatKernel μ hμ ht

/-- An explicit quadratic envelope coefficient, continuous at positive heat times. -/
def heatLogEnvelopeConstant {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) (t : ℝ) : ℝ :=
  heatKernelBound I t + 1 +
    |-((Fintype.card I : ℝ) / 2) * Real.log (2 * Real.pi * (heatVariance t : ℝ)) -
      (∫ y, squareRadius y ∂μ) / (heatVariance t : ℝ)| + 1 / (heatVariance t : ℝ)

theorem abs_log_heatDensity_le {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    |Real.log (heatDensity μ t x)| ≤ heatLogEnvelopeConstant μ t * (1 + squareRadius x) := by
  let v : ℝ := heatVariance t
  let A := -((Fintype.card I : ℝ) / 2) * Real.log (2 * Real.pi * v) -
    (∫ y, squareRadius y ∂μ) / v
  let K := heatKernelBound I t
  have hv : 0 < v := by dsimp [v]; exact_mod_cast heatVariance_pos ht
  have hK : 0 ≤ K := by
    dsimp [K, heatKernelBound]
    exact Finset.prod_nonneg (fun _ _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hR := squareRadius_nonneg x
  have hlower : A - (1 / v) * squareRadius x ≤ Real.log (heatDensity μ t x) := by
    have h := log_heatDensity_lower μ hμ ht x
    convert h using 1
    dsimp [A, v]
    field_simp
    ring
  have hupper : Real.log (heatDensity μ t x) ≤ K - 1 :=
    (Real.log_le_sub_one_of_pos (heatDensity_pos μ ht x)).trans
      (by linarith [heatDensity_le_bound μ t x])
  have hB : 0 ≤ 1 / v := by positivity
  have habs : |Real.log (heatDensity μ t x)| ≤ K + 1 + |A| + (1 / v) * squareRadius x := by
    apply abs_le.mpr
    constructor
    · have hA : -|A| ≤ A := neg_abs_le A
      have hh := sub_le_sub_right hA ((1 / v) * squareRadius x)
      have hn : -(K + 1 + |A| + (1 / v) * squareRadius x) ≤
          -|A| - (1 / v) * squareRadius x := by linarith
      exact hn.trans (hh.trans hlower)
    · linarith [abs_nonneg A, mul_nonneg hB hR]
  change |Real.log (heatDensity μ t x)| ≤ (K + 1 + |A| + 1 / v) * (1 + squareRadius x)
  nlinarith [mul_nonneg (show 0 ≤ K + 1 + |A| by positivity) hR]

lemma continuousAt_heatLogEnvelopeConstant {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (heatLogEnvelopeConstant μ) t := by
  have hv : Continuous (fun u : ℝ => (heatVariance u : ℝ)) := by
    change Continuous (fun u : ℝ => max (2 * u) 0)
    fun_prop
  have hvpos : 0 < (heatVariance t : ℝ) := by exact_mod_cast heatVariance_pos ht
  have hp : 0 < 2 * Real.pi * (heatVariance t : ℝ) := by positivity
  have hs : ContinuousAt (fun u : ℝ => Real.sqrt (2 * Real.pi * (heatVariance u : ℝ))) t :=
    Real.continuous_sqrt.continuousAt.comp (continuousAt_const.mul hv.continuousAt)
  have hK : ContinuousAt (heatKernelBound I) t := by
    have heq : heatKernelBound I = (fun u : ℝ =>
        ((Real.sqrt (2 * Real.pi * (heatVariance u : ℝ)))⁻¹) ^ Fintype.card I) := by
      funext u
      simp [heatKernelBound]
    rw [heq]
    exact (hs.inv₀ (Real.sqrt_pos.mpr hp).ne').pow _
  have hlog : ContinuousAt (fun u : ℝ =>
      Real.log (2 * Real.pi * (heatVariance u : ℝ))) t :=
    (continuousAt_const.mul hv.continuousAt).log hp.ne'
  have hA : ContinuousAt (fun u : ℝ =>
      -((Fintype.card I : ℝ) / 2) * Real.log (2 * Real.pi * (heatVariance u : ℝ)) -
        (∫ y, squareRadius y ∂μ) / (heatVariance u : ℝ)) t :=
    (continuousAt_const.mul hlog).sub (continuousAt_const.div hv.continuousAt hvpos.ne')
  exact ((hK.add continuousAt_const).add hA.abs).add
    (continuousAt_const.div hv.continuousAt hvpos.ne')

/-- A locally uniform logarithmic envelope, suitable for differentiating
entropy on compact positive-time intervals. The only mixing-law input is a
finite radial second moment. -/
theorem exists_uniform_log_heatDensity_bound {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc a b, ∀ x : I → ℝ,
      |Real.log (heatDensity μ u x)| ≤ C * (1 + squareRadius x) := by
  have hcont : ContinuousOn (heatLogEnvelopeConstant μ) (Set.Icc a b) := by
    intro u hu
    exact (continuousAt_heatLogEnvelopeConstant μ (lt_of_lt_of_le ha hu.1)).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro u hu x
  have hCu : heatLogEnvelopeConstant μ u ≤ max C 0 :=
    (hC (Set.mem_image_of_mem _ hu)).trans (le_max_left _ _)
  exact (abs_log_heatDensity_le μ hμ (lt_of_lt_of_le ha hu.1) x).trans
    (mul_le_mul_of_nonneg_right hCu (by linarith [squareRadius_nonneg x] : 0 ≤ 1 + squareRadius x))

lemma integrable_coordinate_of_squareRadius {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (i : I) :
    Integrable (fun x : I → ℝ => x i) μ := by
  apply ((integrable_const (1 : ℝ)).add hμ).mono' (measurable_pi_apply i).aestronglyMeasurable
  filter_upwards [] with x
  change |x i| ≤ 1 + squareRadius x
  have hi : x i ^ 2 ≤ squareRadius x :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  nlinarith [sq_nonneg (|x i| - 1), sq_abs (x i)]

lemma centeredGaussian_first_moment (v : ℝ≥0) :
    (∫ x : ℝ, x ∂gaussianReal 0 v) = 0 := by
  rw [← centeredGaussian_eq_scaled_standard v]
  change (∫ x : ℝ, id x ∂Measure.map
    (fun x : ℝ => Real.sqrt (v : ℝ) * x) standardNormal) = 0
  rw [integral_map (by fun_prop : AEMeasurable (fun x : ℝ => Real.sqrt (v : ℝ) * x) standardNormal)
      (measurable_id.aestronglyMeasurable : AEStronglyMeasurable (fun x : ℝ => x)
        (Measure.map (fun x : ℝ => Real.sqrt (v : ℝ) * x) standardNormal))]
  change (∫ x : ℝ, Real.sqrt (v : ℝ) * x ∂standardNormal) = 0
  rw [integral_const_mul, standardNormal_moment_one, mul_zero]

lemma integral_heatGaussian_coordinate {I : Type*} [Fintype I] (t : ℝ) (i : I) :
    (∫ x : I → ℝ, x i ∂heatGaussian I t) = 0 := by
  classical
  let ms : I → MeasureSpace ℝ := fun _ => ⟨gaussianReal 0 (heatVariance t)⟩
  have sf : ∀ j, @SigmaFinite ℝ _ (@volume ℝ (ms j)) := fun _ =>
    (inferInstance : SigmaFinite (gaussianReal 0 (heatVariance t)))
  let f : I → ℝ → ℝ := fun j y => if j = i then y else 1
  have hp := @integral_fintype_prod_eq_prod ℝ _ I _ (fun _ => ℝ) f ms sf
  have hf (j : I) : (∫ y, f j y ∂gaussianReal 0 (heatVariance t)) =
      if j = i then 0 else 1 := by
    by_cases hj : j = i <;> simp [f, hj, centeredGaussian_first_moment]
  calc
    _ = ∫ x : I → ℝ, ∏ j, f j (x j) ∂heatGaussian I t := by simp [f]
    _ = ∏ j, ∫ y, f j y ∂gaussianReal 0 (heatVariance t) := by
      simpa only [heatGaussian, ← volume_pi] using hp
    _ = _ := by simp_rw [hf]; simp

/-- Actual independent Gaussian convolution adds exactly the Gaussian radial
second moment. No centering assumption on the input is needed. -/
theorem integral_heatedLaw_squareRadius {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (t : ℝ) :
    (∫ x, squareRadius x ∂heatedLaw μ t) =
      (∫ x, squareRadius x ∂μ) + (Fintype.card I : ℝ) * (heatVariance t : ℝ) := by
  have hG := integrable_heatGaussian_squareRadius (I := I) t
  have hl : Integrable (fun z : (I → ℝ) × (I → ℝ) => squareRadius z.1)
      (μ.prod (heatGaussian I t)) := by
    simpa only [mul_one] using hμ.mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : I → ℝ => (1 : ℝ)) (heatGaussian I t))
  have hr : Integrable (fun z : (I → ℝ) × (I → ℝ) => squareRadius z.2)
      (μ.prod (heatGaussian I t)) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : I → ℝ => (1 : ℝ)) μ).mul_prod hG
  have hc (i : I) : Integrable (fun z : (I → ℝ) × (I → ℝ) => z.1 i * z.2 i)
      (μ.prod (heatGaussian I t)) :=
    (integrable_coordinate_of_squareRadius μ hμ i).mul_prod
      (integrable_coordinate_of_squareRadius _ hG i)
  have hcSum := integrable_finset_sum Finset.univ (fun i _ => hc i)
  have hcZero : (∫ z : (I → ℝ) × (I → ℝ), ∑ i, z.1 i * z.2 i
      ∂μ.prod (heatGaussian I t)) = 0 := by
    rw [integral_finset_sum Finset.univ (fun i _ => hc i)]
    apply Finset.sum_eq_zero
    intro i _
    rw [integral_prod_mul (fun x : I → ℝ => x i) (fun x : I → ℝ => x i),
      integral_heatGaussian_coordinate, mul_zero]
  have hleft : (∫ z : (I → ℝ) × (I → ℝ), squareRadius z.1
      ∂μ.prod (heatGaussian I t)) = ∫ x, squareRadius x ∂μ := by
    simpa only [mul_one, integral_const, measureReal_univ_eq_one, one_smul] using
      (integral_prod_mul (μ := μ) (ν := heatGaussian I t) squareRadius (fun _ => (1 : ℝ)))
  have hright : (∫ z : (I → ℝ) × (I → ℝ), squareRadius z.2
      ∂μ.prod (heatGaussian I t)) = ∫ x, squareRadius x ∂heatGaussian I t := by
    simpa only [one_mul, integral_const, measureReal_univ_eq_one, one_smul] using
      (integral_prod_mul (μ := μ) (ν := heatGaussian I t) (fun _ => (1 : ℝ)) squareRadius)
  have heq (z : (I → ℝ) × (I → ℝ)) : squareRadius (z.1 + z.2) =
      squareRadius z.1 + 2 * (∑ i, z.1 i * z.2 i) + squareRadius z.2 := by
    calc
      _ = ∑ i, (z.1 i ^ 2 + 2 * (z.1 i * z.2 i) + z.2 i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        change (z.1 i + z.2 i) ^ 2 = _
        ring
      _ = _ := by simp only [squareRadius, Finset.sum_add_distrib, ← Finset.mul_sum]
  change (∫ x, squareRadius x ∂Measure.map
    (fun z : (I → ℝ) × (I → ℝ) => z.1 + z.2) (μ.prod (heatGaussian I t))) = _
  rw [integral_map (measurable_fst.add measurable_snd).aemeasurable
    continuous_squareRadius.measurable.aestronglyMeasurable]
  simp_rw [heq]
  rw [integral_add (f := fun z : (I → ℝ) × (I → ℝ) =>
      squareRadius z.1 + 2 * ∑ i, z.1 i * z.2 i) (hl.add (hcSum.const_mul 2)) hr,
    integral_add (f := fun z : (I → ℝ) × (I → ℝ) => squareRadius z.1) hl (hcSum.const_mul 2),
    integral_const_mul, hcZero, hleft, hright, integral_heatGaussian_squareRadius]
  ring

/-- The actual Lebesgue density has the same exact computed second moment. -/
theorem integral_heatDensity_mul_squareRadius {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) :
    (∫ x, heatDensity μ t x * squareRadius x) =
      (∫ x, squareRadius x ∂μ) + (Fintype.card I : ℝ) * (heatVariance t : ℝ) := by
  have heq := integral_withDensity_eq_integral_toReal_smul
    (μ := (volume : Measure (I → ℝ))) (measurable_heatDensity μ t).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) squareRadius
  simp only [ENNReal.toReal_ofReal (heatDensity_nonneg _ _ _), smul_eq_mul] at heq
  rw [← heq, ← heatedLaw_eq_withDensity μ ht, integral_heatedLaw_squareRadius μ hμ]


lemma heatVariance_coe_of_pos {t : ℝ} (ht : 0 < t) :
    (heatVariance t : ℝ) = 2 * t := by
  exact max_eq_left (by linarith)

lemma gaussianEntropyValue_eq_unit_add_log {I : Type*} [Fintype I]
    {v : ℝ≥0} (hv : 0 < v) :
    gaussianEntropyValue I v = gaussianEntropyValue I 1 +
      (Fintype.card I : ℝ) / 2 * Real.log (v : ℝ) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  simp only [gaussianEntropyValue, NNReal.coe_one, mul_one]
  rw [Real.log_mul (by positivity : 2 * Real.pi ≠ 0) hv']
  ring

/-- The finite-time Gaussian entropy squeeze for whitened input. Both bounds
refer to the actual arbitrary heat mixture and have been derived from Gibbs'
inequality and computed moments. -/
theorem heatDensity_entropy_squeeze {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ)
    (htrace : (∫ x, squareRadius x ∂μ) = (Fintype.card I : ℝ))
    {t : ℝ} (ht : 0 < t) :
    gaussianEntropyValue I (heatVariance t) ≤ densityEntropy volume (heatDensity μ t) ∧
      densityEntropy volume (heatDensity μ t) ≤
        gaussianEntropyValue I (heatVariance (t + 1 / 2)) := by
  refine ⟨gaussianEntropyValue_le_densityEntropy_heatDensity μ hμ ht, ?_⟩
  apply densityEntropy_le_gaussianEntropyValue (heatDensity μ t) (by linarith)
    (heatDensity_nonneg μ t) (integrable_heatDensity μ ht) (integral_heatDensity μ ht)
    (integrable_heatDensity_log μ hμ ht) (integrable_heatDensity_mul_squareRadius μ hμ ht)
  rw [integral_heatDensity_mul_squareRadius μ hμ ht, htrace,
    heatVariance_coe_of_pos ht, heatVariance_coe_of_pos (by linarith : 0 < t + 1 / 2)]
  ring

/-- Large-time endpoint after covariance normalization. This is the entropy
of the actual heated density minus the deterministic entropy scaling term;
it converges to the standard Gaussian entropy. -/
theorem tendsto_normalized_heatDensity_entropy_atTop {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ)
    (htrace : (∫ x, squareRadius x ∂μ) = (Fintype.card I : ℝ)) :
    Tendsto (fun t : ℝ => densityEntropy volume (heatDensity μ t) -
      (Fintype.card I : ℝ) / 2 * Real.log (1 + 2 * t)) atTop
      (𝓝 (gaussianEntropyValue I 1)) := by
  let L : ℝ → ℝ := fun t => gaussianEntropyValue I 1 +
    (Fintype.card I : ℝ) / 2 * Real.log (2 * t / (1 + 2 * t))
  have hlarge : Tendsto (fun t : ℝ => 1 + 2 * t) atTop atTop := by
    apply tendsto_atTop_mono (fun t : ℝ => by linarith : ∀ t : ℝ, 2 * t ≤ 1 + 2 * t)
    exact tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hinv : Tendsto (fun t : ℝ => (1 + 2 * t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlarge
  have hratio : Tendsto (fun t : ℝ => 2 * t / (1 + 2 * t)) atTop (𝓝 1) := by
    have hh : Tendsto (fun t : ℝ => 1 - (1 + 2 * t)⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hinv
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hd : 1 + 2 * t ≠ 0 := by linarith
    field_simp
  have hL : Tendsto L atTop (𝓝 (gaussianEntropyValue I 1)) := by
    have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    have hh : Tendsto L atTop (𝓝 (gaussianEntropyValue I 1 +
        (Fintype.card I : ℝ) / 2 * Real.log 1)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul hlog)
    simpa using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    obtain ⟨hl, _⟩ := heatDensity_entropy_squeeze μ hμ htrace ht
    have hn : 0 < 1 + 2 * t := by linarith
    have hv : 0 < heatVariance t := heatVariance_pos ht
    rw [gaussianEntropyValue_eq_unit_add_log hv, heatVariance_coe_of_pos ht] at hl
    dsimp [L]
    rw [Real.log_div (by positivity : 2 * t ≠ 0) hn.ne']
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    obtain ⟨_, hu⟩ := heatDensity_entropy_squeeze μ hμ htrace ht
    rw [gaussianEntropyValue_eq_unit_add_log (heatVariance_pos (by linarith : 0 < t + 1 / 2)),
      heatVariance_coe_of_pos (by linarith : 0 < t + 1 / 2)] at hu
    have heq : 2 * (t + 1 / 2) = 1 + 2 * t := by ring
    rw [heq] at hu
    linarith

end GaussianWave.BS
