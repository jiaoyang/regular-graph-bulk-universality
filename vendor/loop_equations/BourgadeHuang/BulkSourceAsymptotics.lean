import BourgadeHuang.BulkCompactSources
import BourgadeHuang.ExponentialExpectationBounds

/-! Quantitative normalization of exponential observables, directly from the
limiting hierarchy and its proved large-height local law. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- A small centered compact source has an exponential expectation close to one. -/
theorem compactCenteredSource_exponential_close
    {T : Type*} [TopologicalSpace T] [TopologicalSpace.MetrizableSpace T]
    [SecondCountableTopology T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T]
    (κ : Measure T) [IsProbabilityMeasure κ]
    (γ ρ : T → ℂ) (hγ : Continuous γ) (hρ : Continuous ρ) (hup : ∀ t, 0<(γ t).im)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {δ : ℝ} (hδ : 0<δ) (hρδ : ∀ t, ‖ρ t‖ ≤ δ*(γ t).im) :
    Integrable (fun s => Complex.exp (compactCenteredSource κ γ ρ s)) ν ∧
      ‖(∫ s, Complex.exp (compactCenteredSource κ γ ρ s) ∂ν)-1‖ ≤
        δ*(64+Real.exp (δ^2/bulkExponentialScale)) := by
  obtain ⟨h2i,h2b⟩ := compactCenteredSource_second_moment κ γ ρ hγ hρ hup ν hh ha he hδ.le hρδ
  obtain ⟨hei,heb⟩ := compactCenteredSource_exp_bound κ γ ρ hγ hρ hup ν hh ha he hδ.le
    (show (0:ℝ)≤2 by norm_num) hρδ
  obtain ⟨hi,hb⟩ := exponential_expectation_close_of_second_moment ν
    (compactCenteredSource κ γ ρ) (measurable_compactCenteredSource κ γ ρ hγ hρ hup) h2i hei hδ
  refine ⟨hi,hb.trans ?_⟩
  calc
    _ ≤ (128*δ^2)/(2*δ)+(δ/2)*(2*Real.exp ((2*δ)^2/(4*bulkExponentialScale))) :=
      add_le_add (div_le_div_of_nonneg_right h2b (by positivity))
        (mul_le_mul_of_nonneg_left heb (by positivity))
    _ = _ := by
      have heq : (2*δ)^2/(4*bulkExponentialScale)=δ^2/bulkExponentialScale := by ring
      rw [heq]
      field_simp
      ring

theorem ratioPath_im_lower {u v : ℂ} {η : ℝ} (hu : η≤u.im) (hv : η≤v.im)
    (t : RatioInterval) : η≤(ratioPath u v t).im := by
  simp only [ratioPath,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,zero_add,Complex.sub_im]
  nlinarith [t.property.1,t.property.2]

/-- Exact separation of the deterministic exponential from the centered
straight-path source. -/
theorem anchoredCharacteristicRatio_centered (s : AnchoredCountingState) {u v : ℂ}
    (hu : 0<u.im) (hv : 0<v.im) :
    anchoredCharacteristicRatio s u v = Complex.exp (-(u-v)*Complex.I) *
      Complex.exp (compactCenteredSource ratioIntervalMeasure (fun t : RatioInterval => ratioPath u v t) (fun _ => -(u-v)) s) := by
  have huv : SameOpenHalfPlane u v := Or.inl ⟨hu,hv⟩
  have hc := continuous_nevanlinna_ratioPath s huv
  have hi : Integrable (fun t : RatioInterval => -(u-v)*anchoredNevanlinna s (ratioPath u v t)) ratioIntervalMeasure :=
    (continuous_const.mul hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq : compactCenteredSource ratioIntervalMeasure (fun t : RatioInterval => ratioPath u v t) (fun _ => -(u-v)) s =
      (∫ t : RatioInterval, -(u-v)*anchoredNevanlinna s (ratioPath u v t) ∂ratioIntervalMeasure)- (-(u-v)*Complex.I) := by
    simp only [compactCenteredSource,mul_sub]
    rw [integral_sub hi (integrable_const _)]
    simp
  unfold anchoredCharacteristicRatio
  rw [heq,← Complex.exp_add]
  congr 1
  ring

/-- Actual ratio expectations approach their deterministic normalization when
endpoint displacement is small relative to their common height. -/
theorem expectedCharacteristicRatio_normalized_bound
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {u v : ℂ} {η δ : ℝ} (hη : 0<η) (hu : η≤u.im) (hv : η≤v.im)
    (hδ : 0<δ) (hd : ‖u-v‖≤δ*η) :
    Integrable (fun s => anchoredCharacteristicRatio s u v) ν ∧
      ‖Complex.exp ((u-v)*Complex.I)*(∫ s, anchoredCharacteristicRatio s u v ∂ν)-1‖ ≤
        δ*(64+Real.exp (δ^2/bulkExponentialScale)) := by
  have hup : ∀ t : RatioInterval, 0<(ratioPath u v t).im :=
    fun t => hη.trans_le (ratioPath_im_lower hu hv t)
  have hr : ∀ t : RatioInterval, ‖-(u-v)‖≤δ*(ratioPath u v t).im := by
    intro t
    rw [norm_neg]
    exact hd.trans (mul_le_mul_of_nonneg_left (ratioPath_im_lower hu hv t) hδ.le)
  obtain ⟨hi,hb⟩ := compactCenteredSource_exponential_close ratioIntervalMeasure
    (fun t : RatioInterval => ratioPath u v t) (fun _ => -(u-v)) ((continuous_ratioPath u v).comp continuous_subtype_val) continuous_const hup ν hh ha he hδ hr
  have heq (s : AnchoredCountingState) := anchoredCharacteristicRatio_centered s (hη.trans_le hu) (hη.trans_le hv)
  have hRi : Integrable (fun s => anchoredCharacteristicRatio s u v) ν := by
    simpa only [heq] using hi.const_mul (Complex.exp (-(u-v)*Complex.I))
  refine ⟨hRi, ?_⟩
  have hmean : (∫ s, anchoredCharacteristicRatio s u v ∂ν) =
      Complex.exp (-(u-v)*Complex.I) *
        ∫ s, Complex.exp (compactCenteredSource ratioIntervalMeasure (fun t : RatioInterval => ratioPath u v t) (fun _ => -(u-v)) s) ∂ν := by
    simp only [heq,integral_const_mul]
  rw [hmean,← mul_assoc,← Complex.exp_add]
  convert hb using 1
  have hz : (u-v)*Complex.I + -(u-v)*Complex.I=0 := by ring
  rw [hz,Complex.exp_zero,one_mul]

end BourgadeHuang
