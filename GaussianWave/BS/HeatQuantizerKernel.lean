import GaussianWave.BS.EntropyRecovery
import GaussianWave.BS.Reused.Entropy.FiniteLawIntegral
import GaussianWave.BS.Reused.Entropy.ClippedQuantizer
import GaussianWave.BS.Reused.Entropy.IntegerClippingEntropy
import GaussianWave.BS.Reused.Entropy.GridCells

/-! A genuine continuous finite-output recoloring kernel obtained by adding
Gaussian noise and then applying any measurable finite quantizer. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GaussianWave.BS
open Reused.Entropy
variable {I : Type*} [Fintype I]

private theorem norm_setIntegral_translate_sub_le
    (f : (I → ℝ) → ℝ) (hf : Integrable f) (S : Set (I → ℝ)) (x y : I → ℝ) :
    ‖(∫ z in S, f (z - x)) - ∫ z in S, f (z - y)‖ ≤
      ∫ z, ‖f (z - (x - y)) - f z‖ := by
  have hx := integrable_sub_right f hf x
  have hy := integrable_sub_right f hf y
  rw [← integral_sub hx.restrict hy.restrict]
  calc
    _ ≤ ∫ z in S, ‖f (z - x) - f (z - y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ‖f (z - x) - f (z - y)‖ :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun _ => norm_nonneg _)) (hx.sub hy).norm
    _ = ∫ z, ‖f ((z - y) - (x - y)) - f (z - y)‖ := by
      congr 1
      funext z
      rw [show (z - y) - (x - y) = z - x by abel]
    _ = _ := integral_sub_right_eq (fun z => ‖f (z - (x - y)) - f z‖) y

/-- Integrating an L1 translate over a fixed measurable event is continuous.
This is strong-Feller continuity from the actual L1 translation theorem. -/
theorem continuous_setIntegral_translate
    (f : (I → ℝ) → ℝ) (hf : Integrable f) (S : Set (I → ℝ)) :
    Continuous (fun x => ∫ z in S, f (z - x)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hsub : Tendsto (fun x : I → ℝ => x - y) (𝓝 y) (𝓝 0) := by
    simpa only [id_eq, sub_self] using
      (continuous_id.sub (continuous_const : Continuous (fun _ : I → ℝ => y))).tendsto y
  have hb := (tendsto_integral_norm_translation_sub_zero f hf).comp hsub
  have h := squeeze_zero_norm (fun x => norm_setIntegral_translate_sub_le f hf S x y) hb
  exact tendsto_sub_nhds_zero_iff.mp h

/-- Literal finite mass of the quantizer after independent Gaussian noise. -/
def heatQuantizerMass {B : Type*} [MeasurableSpace B]
    (Q : (I → ℝ) → B) (t : ℝ) (x : I → ℝ) (b : B) : ℝ :=
  (heatGaussian I t).real {z | Q (x + z) = b}

/-- The probability mass has an ordinary translated-density formula. -/
theorem heatQuantizerMass_eq_setIntegral {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (Q : (I → ℝ) → B) (hQ : Measurable Q) {t : ℝ} (ht : 0 < t) (x : I → ℝ) (b : B) :
    heatQuantizerMass Q t x b = ∫ z in Q ⁻¹' {b}, heatKernel t (z - x) := by
  let S := Q ⁻¹' {b}
  have hS : MeasurableSet S := hQ (measurableSet_singleton b)
  have htranslate : MeasurableSet {z : I → ℝ | Q (x + z) = b} :=
    (hQ.comp (measurable_const.add measurable_id)) (measurableSet_singleton b)
  unfold heatQuantizerMass Measure.real
  rw [heatGaussian_eq_withDensity ht, withDensity_apply _ htranslate]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel t).restrict
    (ae_of_all _ (fun z => heatKernel_nonneg t z)),
    ENNReal.toReal_ofReal (integral_nonneg (fun z => heatKernel_nonneg t z))]
  rw [← integral_indicator htranslate, ← integral_indicator hS]
  have h' := (measurePreserving_add_right (volume : Measure (I → ℝ)) x).integral_comp
    (MeasurableEquiv.addRight x).measurableEmbedding
    (S.indicator (fun z => heatKernel t (z - x)))
  simpa only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, S,
    Set.mem_setOf_eq, add_sub_cancel_right, add_sub_cancel_left, add_comm] using h'

theorem continuous_heatQuantizerMass {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (Q : (I → ℝ) → B) (hQ : Measurable Q) {t : ℝ} (ht : 0 < t) (b : B) :
    Continuous (fun x => heatQuantizerMass Q t x b) := by
  simp_rw [heatQuantizerMass_eq_setIntegral Q hQ ht]
  exact continuous_setIntegral_translate (heatKernel t) (integrable_heatKernel t) _

theorem heatQuantizerMass_nonneg {B : Type*} [MeasurableSpace B]
    (Q : (I → ℝ) → B) (t : ℝ) (x : I → ℝ) (b : B) :
    0 ≤ heatQuantizerMass Q t x b := measureReal_nonneg

theorem heatQuantizerMass_sum {B : Type*} [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (Q : (I → ℝ) → B) (hQ : Measurable Q) (t : ℝ) (x : I → ℝ) :
    (∑ b, heatQuantizerMass Q t x b) = 1 := by
  have h := lawMass_hasSum (heatGaussian I t) (fun z => Q (x + z))
    (hQ.comp (measurable_const.add measurable_id))
  simpa only [tsum_fintype, lawMass, heatQuantizerMass] using h.tsum_eq

theorem lawMass_heatedLaw_eq_integral_heatQuantizerMass
    {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (Q : (I → ℝ) → B) (hQ : Measurable Q) {t : ℝ} (ht : 0 < t) (b : B) :
    lawMass (heatedLaw μ t) Q b = ∫ x, heatQuantizerMass Q t x b ∂μ := by
  let S := Q ⁻¹' {b}
  have hS : MeasurableSet S := hQ (measurableSet_singleton b)
  have hprod : Integrable
      (fun z : (I → ℝ) × (I → ℝ) => heatKernel t (z.1 - z.2))
      ((volume.restrict S).prod μ) := by
    apply (integrable_prod_iff (((continuous_heatKernel t).comp
      (continuous_fst.sub continuous_snd)).measurable.aestronglyMeasurable)).mpr
    constructor
    · exact ae_of_all _ (fun x => integrable_heatKernel_shift μ t x)
    · have he (x : I → ℝ) :
          (∫ y, ‖heatKernel t (x - y)‖ ∂μ) = heatDensity μ t x := by
        simp only [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg _ _), heatDensity]
      change Integrable (fun x => ∫ y, ‖heatKernel t (x - y)‖ ∂μ) (volume.restrict S)
      simp_rw [he]
      exact (integrable_heatDensity μ ht).restrict
  have hmass : lawMass (heatedLaw μ t) Q b = ∫ z in S, heatDensity μ t z := by
    rw [lawMass, measureReal_def, heatedLaw_eq_withDensity μ ht, withDensity_apply _ hS]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatDensity μ ht).restrict
      (ae_of_all _ (heatDensity_nonneg μ t)),
      ENNReal.toReal_ofReal (integral_nonneg (heatDensity_nonneg μ t))]
  rw [hmass]
  change (∫ z in S, ∫ x, heatKernel t (z - x) ∂μ) = _
  rw [integral_integral_swap hprod]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (heatQuantizerMass_eq_setIntegral Q hQ ht x b).symm

theorem heatQuantizerMass_eq_dirac_heat_law
    {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (Q : (I → ℝ) → B) (hQ : Measurable Q) {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    heatQuantizerMass Q t x = lawMass (heatedLaw (Measure.dirac x) t) Q := by
  funext b
  rw [lawMass_heatedLaw_eq_integral_heatQuantizerMass (Measure.dirac x) Q hQ ht]
  exact (integral_dirac' _ x (continuous_heatQuantizerMass Q hQ ht b).stronglyMeasurable).symm

end GaussianWave.BS
