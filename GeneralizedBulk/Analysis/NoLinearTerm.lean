import GeneralizedBulk.Gaussian.SeriesPresentedBounds
import BourgadeHuang.CountingEvaluation
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! Uniform height moments exclude an escaped affine Nevanlinna term. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology

namespace GeneralizedBulk.Analysis

theorem measurable_anchoredLinearCoefficient : Measurable anchoredLinearCoefficient := by
  have hm : Measurable (fun s : AnchoredCountingState => s.val.1.measure) :=
    LocalCountingMeasure.measurable_measure.comp (measurable_fst.comp measurable_subtype_coe)
  have hw : Measurable (fun s : AnchoredCountingState =>
      ∫ a, nevanlinnaWeight a ∂s.val.1.measure) := by
    have hl := (Measure.measurable_lintegral continuous_nevanlinnaWeight.measurable.ennreal_ofReal).comp hm
    convert hl.ennreal_toReal using 1
    funext s
    exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall nevanlinnaWeight_nonneg)
      s.integrable_weight.aestronglyMeasurable
  exact (Complex.measurable_im.comp (measurable_snd.comp measurable_subtype_coe)).sub hw

theorem integrable_anchoredLinearCoefficient
    {S : Type*} [MeasurableSpace S] (P : Measure S)
    (X : S → AnchoredCountingState) (hX : Measurable X)
    (hm : Integrable (fun x => ‖(X x).val.2‖) P) :
    Integrable (fun x => anchoredLinearCoefficient (X x)) P := by
  apply hm.mono' (measurable_anchoredLinearCoefficient.comp hX).aestronglyMeasurable
  filter_upwards [] with x
  change ‖anchoredLinearCoefficient (X x)‖ ≤ ‖(X x).val.2‖
  rw [Real.norm_eq_abs, abs_of_nonneg (anchoredLinearCoefficient_nonneg _)]
  have h := mul_anchoredLinearCoefficient_le_im (X x) (z := Complex.I) (by simp)
  simpa only [Complex.I_im, one_mul, anchoredNevanlinna_I] using
    h.trans (Complex.im_le_norm _)

theorem integrable_scalar_norm_of_anchor
    {S : Type*} [MeasurableSpace S] (P : Measure S)
    (X : S → AnchoredCountingState) (hX : Measurable X)
    (hm : Integrable (fun x => ‖(X x).val.2‖) P) {w : ℂ} (hw : w.im ≠ 0) :
    Integrable (fun x => ‖anchoredNevanlinna (X x) w‖) P := by
  apply (hm.const_mul (Gaussian.scalarValueEnvelope w)).mono'
    (((continuous_anchoredNevanlinna hw).measurable.comp hX).norm).aestronglyMeasurable
  filter_upwards [] with x
  rw [norm_norm]
  exact norm_anchoredNevanlinna_le_anchor (X x) hw

/-- Uniform first moments along integer imaginary heights force zero linear
mass almost surely. This is stronger than assuming its vanishing in a limit. -/
theorem anchoredLinearCoefficient_eq_zero_ae_of_uniform_height
    {S : Type*} [MeasurableSpace S] (P : Measure S)
    (X : S → AnchoredCountingState) (hX : Measurable X)
    (hm : Integrable (fun x => ‖(X x).val.2‖) P)
    (C : ℝ)
    (hheight : ∀ n : ℕ, (∫ x, ‖anchoredNevanlinna (X x)
      (((n : ℝ) + 1 : ℝ) * Complex.I)‖ ∂P) ≤ C) :
    ∀ᵐ x ∂P, anchoredLinearCoefficient (X x) = 0 := by
  have hi := integrable_anchoredLinearCoefficient P X hX hm
  have hb (n : ℕ) : (∫ x, anchoredLinearCoefficient (X x) ∂P) ≤ C / ((n : ℝ) + 1) := by
    have hy : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hw : ((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I).im ≠ 0 := by
      simpa using ne_of_gt hy
    have hnorm := integrable_scalar_norm_of_anchor P X hX hm hw
    have hp : ∀ x, ((n : ℝ) + 1) * anchoredLinearCoefficient (X x) ≤
        ‖anchoredNevanlinna (X x) (((n : ℝ) + 1 : ℝ) * Complex.I)‖ := by
      intro x
      have h := mul_anchoredLinearCoefficient_le_im (X x)
        (z := (((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I) (by simpa using hy)
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero] using
          h.trans (Complex.im_le_norm _)
    have hh := (integral_mono (hi.const_mul _) hnorm hp).trans (hheight n)
    rw [integral_const_mul] at hh
    exact (le_div_iff₀ hy).2 (by simpa only [mul_comm] using hh)
  have ht : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat (a := C)
  have hz : (∫ x, anchoredLinearCoefficient (X x) ∂P) = 0 :=
    le_antisymm (ge_of_tendsto ht (Eventually.of_forall hb))
      (integral_nonneg (fun x => anchoredLinearCoefficient_nonneg _))
  exact (integral_eq_zero_iff_of_nonneg (fun x => anchoredLinearCoefficient_nonneg _) hi).1 hz

end GeneralizedBulk.Analysis
