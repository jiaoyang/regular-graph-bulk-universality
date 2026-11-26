import GaussianWave.BS.EntropyEndpoint
import GaussianWave.BS.EntropySemicontinuity
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# Recovery of initial entropy at zero heat time

The first step is the actual strong continuity of spatial translations in
Lebesgue L1. It applies to arbitrary integrable measurable densities, without
a continuity or finite-support assumption on the initial density.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators NNReal

namespace GaussianWave.BS
variable {I : Type*} [Fintype I]

private def translateL1 (f : (I → ℝ) →₁[volume] ℝ) (z : I → ℝ) :
    (I → ℝ) →₁[volume] ℝ :=
  Lp.compMeasurePreserving (fun x : I → ℝ => x - z)
    (by simpa only [sub_eq_add_neg] using
      measurePreserving_add_right (volume : Measure (I → ℝ)) (-z)) f

private theorem continuous_translateL1 (f : (I → ℝ) →₁[volume] ℝ) :
    Continuous (translateL1 f) := by
  let g : (I → ℝ) → C(I → ℝ, I → ℝ) := fun z => ⟨fun x => x - z,
    continuous_id.sub continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.sub continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun z => by simpa only [g, sub_eq_add_neg] using
      measurePreserving_add_right (volume : Measure (I → ℝ)) (-z)) (by simp)

private theorem norm_translateL1_sub_eq
    (f : (I → ℝ) → ℝ) (hf : Integrable f (volume : Measure (I → ℝ))) (z : I → ℝ) :
    ‖translateL1 (hf.toL1 f) z - hf.toL1 f‖ =
      ∫ x, ‖f (x - z) - f x‖ := by
  have hp : MeasurePreserving (fun x : I → ℝ => x - z) volume volume := by
    simpa only [sub_eq_add_neg] using
      measurePreserving_add_right (volume : Measure (I → ℝ)) (-z)
  rw [L1.norm_sub_eq_lintegral,
    integral_norm_eq_lintegral_enorm (f := fun x => f (x - z) - f x)
      ((integrable_sub_right f hf z).sub hf).aestronglyMeasurable]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving (hf.toL1 f) hp,
    hp.quasiMeasurePreserving.ae hf.coeFn_toL1, hf.coeFn_toL1] with x hx hxz hxf
  simp only [translateL1] at hx ⊢
  rw [hx, Function.comp_apply, hxz, hxf]

/-- Strong L1 continuity of translation, as an ordinary norm integral. -/
theorem continuous_integral_norm_translation_sub
    (f : (I → ℝ) → ℝ) (hf : Integrable f) :
    Continuous (fun z : I → ℝ => ∫ x, ‖f (x - z) - f x‖) := by
  have h := ((continuous_translateL1 (hf.toL1 f)).sub
    (continuous_const : Continuous (fun _ : I → ℝ => hf.toL1 f))).norm
  simpa only [norm_translateL1_sub_eq f hf] using h

theorem tendsto_integral_norm_translation_sub_zero
    (f : (I → ℝ) → ℝ) (hf : Integrable f) :
    Tendsto (fun z : I → ℝ => ∫ x, ‖f (x - z) - f x‖) (𝓝 0) (𝓝 0) := by
  convert (continuous_integral_norm_translation_sub f hf).tendsto (0 : I → ℝ) using 1
  simp

theorem integral_norm_translation_sub_le
    (f : (I → ℝ) → ℝ) (hf : Integrable f) (z : I → ℝ) :
    (∫ x, ‖f (x - z) - f x‖) ≤ 2 * ∫ x, ‖f x‖ := by
  calc
    _ ≤ ∫ x, ‖f (x - z)‖ + ‖f x‖ := integral_mono
      ((integrable_sub_right f hf z).sub hf).norm
      ((integrable_sub_right f hf z).norm.add hf.norm) (fun x => norm_sub_le _ _)
    _ = (∫ x, ‖f (x - z)‖) + ∫ x, ‖f x‖ := integral_add
      (integrable_sub_right f hf z).norm hf.norm
    _ = _ := by rw [integral_sub_right_eq (fun x => ‖f x‖) z]; ring

/-- Actual coordinatewise scaling representation of the heat-noise law,
including the zero-variance endpoint. -/
theorem heatGaussian_eq_map_standardVector (I : Type*) [Fintype I] (t : ℝ) :
    heatGaussian I t = (standardVector I).map
      (fun x : I → ℝ => Real.sqrt (heatVariance t : ℝ) • x) := by
  let c : ℝ := Real.sqrt (heatVariance t : ℝ)
  have hc : (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0) = heatVariance t := by
    apply Subtype.ext
    exact Real.sq_sqrt (heatVariance t).property
  unfold heatGaussian
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have heq : (fun x : I → ℝ => c • x) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => (fun a : ℝ => c * a) ⁻¹' s i) := by
    ext x
    simp [Set.mem_pi]
  change standardVector I ((fun x : I → ℝ => c • x) ⁻¹' Set.pi Set.univ s) = _
  rw [heq]
  unfold standardVector
  rw [Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  have hmap := ProbabilityTheory.gaussianReal_map_const_mul (μ := 0) (v := 1) c
  rw [mul_zero, mul_one, hc] at hmap
  have hset := congrArg (fun ν : Measure ℝ => ν (s i)) hmap
  dsimp only at hset
  rw [Measure.map_apply (by fun_prop) (hs i)] at hset
  exact hset

/-- Heat noise converges against every bounded continuous test to evaluation
at zero, proved on one fixed actual standard-Gaussian probability space. -/
theorem tendsto_integral_heatGaussian_zero
    (h : (I → ℝ) → ℝ) (hh : Continuous h) (B : ℝ) (hB : ∀ x, ‖h x‖ ≤ B) :
    Tendsto (fun t : ℝ => ∫ x, h x ∂heatGaussian I t) (𝓝 0) (𝓝 (h 0)) := by
  have hscale : Tendsto (fun t : ℝ => Real.sqrt (heatVariance t : ℝ)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => Real.sqrt (max (2 * t) 0)) := by fun_prop
    simpa only [heatVariance, mul_zero, max_self, Real.sqrt_zero] using hc.tendsto 0
  have hd := tendsto_integral_filter_of_dominated_convergence
    (μ := standardVector I)
    (F := fun t x => h (Real.sqrt (heatVariance t : ℝ) • x))
    (f := fun _ => h 0) (fun _ => B)
    (Filter.Eventually.of_forall (fun t =>
      (hh.comp (continuous_const.smul continuous_id)).measurable.aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun t => ae_of_all _ (fun x => hB _)))
    (integrable_const _) (ae_of_all _ (fun x => by
      simpa only [zero_smul] using hh.continuousAt.tendsto.comp
        (hscale.smul_const x)))
  have heq (t : ℝ) : (∫ x, h x ∂heatGaussian I t) =
      ∫ x, h (Real.sqrt (heatVariance t : ℝ) • x) ∂standardVector I := by
    rw [heatGaussian_eq_map_standardVector]
    exact integral_map (by fun_prop) hh.measurable.aestronglyMeasurable
  simpa only [heq, integral_const, measureReal_univ_eq_one, one_smul] using hd

theorem tendsto_integral_heatGaussian_translation_error
    (f : (I → ℝ) → ℝ) (hf : Integrable f) :
    Tendsto (fun t : ℝ => ∫ z, (∫ x, ‖f (x - z) - f x‖) ∂heatGaussian I t)
      (𝓝 0) (𝓝 0) := by
  convert tendsto_integral_heatGaussian_zero
    (fun z => ∫ x, ‖f (x - z) - f x‖) (continuous_integral_norm_translation_sub f hf)
    (2 * ∫ x, ‖f x‖) (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact integral_norm_translation_sub_le f hf z) using 1
  simp

lemma integral_sub_left_eq (g : (I → ℝ) → ℝ) (x : I → ℝ) :
    (∫ z, g (x - z)) = ∫ z, g z := by
  have hn := integral_neg_eq_self (fun z => g (x + z)) (volume : Measure (I → ℝ))
  have ha := integral_add_left_eq_self (μ := (volume : Measure (I → ℝ))) g x
  simpa only [sub_eq_add_neg] using hn.trans ha

lemma integrable_sub_left (g : (I → ℝ) → ℝ) (hg : Integrable g) (x : I → ℝ) :
    Integrable (fun z => g (x - z)) := by
  simpa only [neg_sub] using integrable_sub_right (fun z => g (-z)) hg.comp_neg x

/-- The actual heat density, when the initial law has density `f`, is the
actual average of translations of `f` against the Gaussian noise law. -/
theorem heatDensity_eq_noise_average_of_density
    (μ : Measure (I → ℝ)) (f : (I → ℝ) → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    heatDensity μ t x = ∫ z, f (x - z) ∂heatGaussian I t := by
  rw [heatDensity, hμ, integral_withDensity_eq_integral_toReal_smul
    hf.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]
  rw [heatGaussian_eq_withDensity ht, integral_withDensity_eq_integral_toReal_smul
    (measurable_heatKernel t).ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (heatKernel_nonneg _ _), smul_eq_mul]
  have heq := integral_sub_left_eq (fun y => f y * heatKernel t (x - y)) x
  simpa only [sub_sub_cancel, mul_comm] using heq.symm

theorem integrable_noise_density_shift
    (f : (I → ℝ) → ℝ) (hf : Measurable f) (hfi : Integrable f)
    {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    Integrable (fun z => f (x - z)) (heatGaussian I t) := by
  rw [heatGaussian_eq_withDensity ht]
  apply (integrable_withDensity_iff_integrable_smul'
    (measurable_heatKernel t).ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
  simp only [ENNReal.toReal_ofReal (heatKernel_nonneg _ _), smul_eq_mul]
  apply (((integrable_sub_left f hfi x).norm).const_mul (heatKernelBound I t)).mono'
    (((measurable_heatKernel t).mul (hf.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
  filter_upwards [] with z
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg _ _)]
  exact mul_le_mul_of_nonneg_right (heatKernel_le_bound t z) (norm_nonneg _)

theorem integrable_translated_density_prod
    (ν : Measure (I → ℝ)) [IsProbabilityMeasure ν]
    (f : (I → ℝ) → ℝ) (hf : Measurable f) (hfi : Integrable f) :
    Integrable (fun z : (I → ℝ) × (I → ℝ) => f (z.2 - z.1)) (ν.prod volume) := by
  apply (integrable_prod_iff
    ((hf.comp (measurable_snd.sub measurable_fst)).aestronglyMeasurable)).mpr
  constructor
  · exact ae_of_all _ (fun z => integrable_sub_right f hfi z)
  · change Integrable (fun z => ∫ x, ‖f (x - z)‖) ν
    simp_rw [integral_sub_right_eq (fun x => ‖f x‖)]
    exact integrable_const _

/-- The norm difference between the actual heat density and the initial
density is bounded by the average L1 translation error. -/
theorem integral_norm_heatDensity_sub_le
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (f : (I → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {t : ℝ} (ht : 0 < t) :
    (∫ x, ‖heatDensity μ t x - f x‖) ≤
      ∫ z, (∫ x, ‖f (x - z) - f x‖) ∂heatGaussian I t := by
  have hprod : Integrable (fun z : (I → ℝ) × (I → ℝ) => f (z.2 - z.1) - f z.2)
      ((heatGaussian I t).prod volume) := by
    apply (integrable_translated_density_prod (heatGaussian I t) f hf hfi).sub
    simpa only [one_mul] using (integrable_const (1 : ℝ) :
      Integrable (fun _ : I → ℝ => (1 : ℝ)) (heatGaussian I t)).mul_prod hfi
  have hbound (x : I → ℝ) : ‖heatDensity μ t x - f x‖ ≤
      ∫ z, ‖f (x - z) - f x‖ ∂heatGaussian I t := by
    have heq : heatDensity μ t x - f x = ∫ z, f (x - z) - f x ∂heatGaussian I t := by
      rw [integral_sub (integrable_noise_density_shift f hf hfi ht x) (integrable_const _),
        ← heatDensity_eq_noise_average_of_density μ f hf hf0 hμ ht]
      simp
    rw [heq]
    exact norm_integral_le_integral_norm _
  calc
    _ ≤ ∫ x, ∫ z, ‖f (x - z) - f x‖ ∂heatGaussian I t :=
      integral_mono ((integrable_heatDensity μ ht).sub hfi).norm
        hprod.norm.integral_prod_right hbound
    _ = _ := (integral_integral_swap hprod.norm).symm

/-- The actual heat density converges to every initial Lebesgue density in
L1 as the positive heat time decreases to zero. -/
theorem tendsto_integral_norm_heatDensity_sub_zero
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (f : (I → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    Tendsto (fun t : ℝ => ∫ x, ‖heatDensity μ t x - f x‖) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => norm_nonneg _)))
    ?_ ((tendsto_integral_heatGaussian_translation_error f hfi).mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact integral_norm_heatDensity_sub_le μ f hf hf0 hfi hμ ht

/-- Adding independent Gaussian noise increases the entropy of an actual
initial density. This is derived by averaging its translates and applying
the proved Gibbs mixture inequality, rather than assumed as entropy
monotonicity. -/
theorem densityEntropy_le_heatDensity_entropy
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (f : (I → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f)
    (hf1 : (∫ x, f x) = 1)
    (hflog : Integrable (fun x => f x * Real.log (f x)))
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hμ2 : Integrable (squareRadius (I := I)) μ)
    {t : ℝ} (ht : 0 < t) :
    densityEntropy volume f ≤ densityEntropy volume (heatDensity μ t) := by
  let p : (I → ℝ) → (I → ℝ) → ℝ := fun z x => f (x - z)
  have hpmeas : Measurable (fun z : (I → ℝ) × (I → ℝ) => p z.1 z.2) :=
    hf.comp (measurable_snd.sub measurable_fst)
  have hpint (z : I → ℝ) : Integrable (p z) := integrable_sub_right f hfi z
  have hpone (z : I → ℝ) : (∫ x, p z x) = 1 := by
    dsimp [p]
    rw [integral_sub_right_eq, hf1]
  have hmix (x : I → ℝ) : heatDensity μ t x = ∫ z, p z x ∂heatGaussian I t :=
    heatDensity_eq_noise_average_of_density μ f hf hf0 hμ ht x
  have hplog : Integrable (fun z : (I → ℝ) × (I → ℝ) =>
      p z.1 z.2 * Real.log (p z.1 z.2)) ((heatGaussian I t).prod volume) :=
    integrable_translated_density_prod (heatGaussian I t) (fun x => f x * Real.log (f x))
      (hf.mul (Real.measurable_log.comp hf)) hflog
  have hcross := integrable_mixture_cross volume (heatGaussian I t) p (heatDensity μ t)
    hpmeas (measurable_heatDensity μ t) (fun z x => hf0 _)
    (fun x => integrable_noise_density_shift f hf hfi ht x) hmix
    (integrable_heatDensity_log μ hμ2 ht)
  have h := densityEntropy_mixture_ge_mean volume (heatGaussian I t) p (heatDensity μ t)
    (fun z x => hf0 _) (heatDensity_pos μ ht) hpint (integrable_heatDensity μ ht)
    hpone (integral_heatDensity μ ht) hmix hplog hcross
  have hpentropy (z : I → ℝ) : densityEntropy volume (p z) = densityEntropy volume f := by
    unfold densityEntropy
    dsimp only [p]
    rw [integral_sub_right_eq (fun x => f x * Real.log (f x)) z]
  simpa only [hpentropy, integral_const, measureReal_univ_eq_one, one_smul] using h

theorem integrable_initial_density_mul_squareRadius
    (μ : Measure (I → ℝ))
    (f : (I → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hμ2 : Integrable (squareRadius (I := I)) μ) :
    Integrable (fun x => f x * squareRadius x) := by
  rw [hμ] at hμ2
  have hh := (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hμ2
  simpa only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul] using hh

theorem integral_initial_density_mul_squareRadius
    (μ : Measure (I → ℝ))
    (f : (I → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    (∫ x, f x * squareRadius x) = ∫ x, squareRadius x ∂μ := by
  rw [hμ, integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]

/-- Sequential recovery of the entropy of the original arbitrary density.
No entropy convergence premise is used: L1 approximation, moment convergence,
Gibbs mixture monotonicity, and Gaussian-reference Fatou semicontinuity have
all been proved for the actual convolutions. -/
theorem tendsto_heatDensity_entropy_zero_seq
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (f : (I → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f)
    (hf1 : (∫ x, f x) = 1)
    (hflog : Integrable (fun x => f x * Real.log (f x)))
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hμ2 : Integrable (squareRadius (I := I)) μ)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => densityEntropy volume (heatDensity μ (t n))) atTop
      (𝓝 (densityEntropy volume f)) := by
  have hwithin : Tendsto t atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht0, Filter.Eventually.of_forall ht⟩
  have hL1 := (tendsto_integral_norm_heatDensity_sub_zero μ f hf hf0 hfi hμ).comp hwithin
  have hmoment : Tendsto (fun n => ∫ x, heatDensity μ (t n) x * squareRadius x) atTop
      (𝓝 (∫ x, f x * squareRadius x)) := by
    simp_rw [integral_heatDensity_mul_squareRadius μ hμ2 (ht _)]
    rw [integral_initial_density_mul_squareRadius μ f hf hf0 hμ]
    have hv : Tendsto (fun n => (heatVariance (t n) : ℝ)) atTop (𝓝 0) := by
      have hc : Continuous (fun u : ℝ => max (2 * u) 0) := by fun_prop
      simpa only [heatVariance, mul_zero, max_self] using (hc.tendsto 0).comp ht0
    simpa using tendsto_const_nhds.add (hv.const_mul (Fintype.card I : ℝ))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n => ha.trans_le
      (densityEntropy_le_heatDensity_entropy μ f hf hf0 hfi hf1 hflog hμ hμ2 (ht n)))
  · intro b hb
    apply eventually_densityEntropy_lt_of_L1_and_secondMoment (fun n => heatDensity μ (t n)) f
      (fun n => heatDensity_nonneg μ (t n)) hf0
      (fun n => integrable_heatDensity μ (ht n)) hfi
      (fun n => integral_heatDensity μ (ht n)) hf1
      (fun n => integrable_heatDensity_log μ hμ2 (ht n)) hflog
      (fun n => integrable_heatDensity_mul_squareRadius μ hμ2 (ht n))
      (integrable_initial_density_mul_squareRadius μ f hf hf0 hμ hμ2)
      _ hmoment hb
    simpa only [Real.norm_eq_abs] using hL1

/-- Full positive-time entropy recovery, for every arbitrary finite-second-
moment initial Lebesgue density with finite entropy. -/
theorem tendsto_heatDensity_entropy_zero
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (f : (I → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f)
    (hf1 : (∫ x, f x) = 1)
    (hflog : Integrable (fun x => f x * Real.log (f x)))
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hμ2 : Integrable (squareRadius (I := I)) μ) :
    Tendsto (fun t : ℝ => densityEntropy volume (heatDensity μ t)) (𝓝[>] 0)
      (𝓝 (densityEntropy volume f)) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro t ht
  have hp : ∀ᶠ n in atTop, 0 < t n := ht self_mem_nhdsWithin
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hp
  apply (tendsto_add_atTop_iff_nat N).mp
  exact tendsto_heatDensity_entropy_zero_seq μ f hf hf0 hfi hf1 hflog hμ hμ2
    (fun n => t (n + N)) (fun n => hN (n + N) (by omega))
    ((ht.mono_right nhdsWithin_le_nhds).comp (tendsto_add_atTop_nat N))

end GaussianWave.BS
