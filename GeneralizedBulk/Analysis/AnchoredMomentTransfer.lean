import GeneralizedBulk.Analysis.CappedMomentTransfer
import GeneralizedBulk.Analysis.PolynomialMoments
import GeneralizedBulk.Analysis.NoLinearTerm

/-! Actual uncapped anchor moments and removal of escaped affine mass in weak limits. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.Analysis

theorem nonnegative_min_pow (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (q : ℕ) :
    min a b ^ q = min (a ^ q) (b ^ q) := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab, min_eq_left (pow_le_pow_left₀ ha hab q)]
  · have hba := le_of_not_ge hab
    rw [min_eq_right hba, min_eq_right (pow_le_pow_left₀ hb hba q)]

/-- A capped norm moment on the finite good event gives the actual norm
moment of the weak limiting anchored counting state. -/
theorem weak_limit_anchor_moment_of_good_capped_norm
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (X : ℕ → Ω → AnchoredCountingState) (hX : ∀ n, Measurable (X n))
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges (fun n => Measure.map (X n) (P n)) ν)
    (good : ℕ → Set Ω) (hgood : ∀ n, MeasurableSet (good n))
    (hbad : Tendsto (fun n => (P n).real (good n)ᶜ) atTop (𝓝 0))
    (cap : ℕ → ℝ) (hcapnonneg : ∀ n, 0 ≤ cap n) (hcap : Tendsto cap atTop atTop)
    (q : ℕ) (hq : q ≠ 0) (C : ℝ) (hC : 0 ≤ C)
    (bounds : ℕ → ℝ) (hbounds : Tendsto bounds atTop (𝓝 C))
    (hmoment : ∀ᶠ n in atTop, (∫ x, (good n).indicator
      (fun x => min ‖(X n x).val.2‖ (cap n) ^ q) x ∂P n) ≤ bounds n) :
    Integrable (fun s : AnchoredCountingState => ‖s.val.2‖ ^ q) ν ∧
      (∫ s : AnchoredCountingState, ‖s.val.2‖ ^ q ∂ν) ≤ C := by
  apply weak_limit_moment_of_good_capped_moments P X hX ν hweak
    (fun s : AnchoredCountingState => ‖s.val.2‖ ^ q)
    (((continuous_snd.comp continuous_subtype_val).norm).pow q)
    (fun s => pow_nonneg (norm_nonneg _) q) good hgood hbad
    (fun n => cap n ^ q) ((tendsto_pow_atTop hq).comp hcap) C hC bounds hbounds
  filter_upwards [hmoment] with n hn
  simpa only [nonnegative_min_pow _ _ (norm_nonneg _) (hcapnonneg n) q] using hn

/-- All asserted limiting anchor moments are derived from finite caps;
no limiting integrability assumption is used. -/
theorem weak_limit_anchor_allMoments_of_good_capped_norms
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (X : ℕ → Ω → AnchoredCountingState) (hX : ∀ n, Measurable (X n))
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges (fun n => Measure.map (X n) (P n)) ν)
    (good : ℕ → Set Ω) (hgood : ∀ n, MeasurableSet (good n))
    (hbad : Tendsto (fun n => (P n).real (good n)ᶜ) atTop (𝓝 0))
    (cap : ℕ → ℝ) (hcapnonneg : ∀ n, 0 ≤ cap n) (hcap : Tendsto cap atTop atTop)
    (hmoment : ∀ q : ℕ, q ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧ ∃ bounds : ℕ → ℝ,
      Tendsto bounds atTop (𝓝 C) ∧ ∀ᶠ n in atTop, (∫ x, (good n).indicator
        (fun x => min ‖(X n x).val.2‖ (cap n) ^ q) x ∂P n) ≤ bounds n) :
    AllMoments ν (fun s : AnchoredCountingState => s.val.2) := by
  refine ⟨(measurable_snd.comp measurable_subtype_coe).aestronglyMeasurable,?_⟩
  intro q
  by_cases hq : q = 0
  · subst q
    simpa only [pow_zero] using integrable_const (μ := ν) (1 : ℝ)
  · obtain ⟨C,hC,bounds,hbounds,hm⟩ := hmoment q hq
    exact (weak_limit_anchor_moment_of_good_capped_norm P X hX ν hweak good hgood hbad cap
      hcapnonneg hcap q hq C hC bounds hbounds hm).1

/-- Uniform limiting height bounds are enough to remove escaped affine
mass; their derivation below uses only capped finite good-event estimates. -/
theorem weak_limit_zero_linear_of_good_capped_heights
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (X : ℕ → Ω → AnchoredCountingState) (hX : ∀ n, Measurable (X n))
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges (fun n => Measure.map (X n) (P n)) ν)
    (hanchor : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (C : ℝ) (hC : 0 ≤ C)
    (good : ℕ → ℕ → Set Ω) (hgood : ∀ Y n, MeasurableSet (good Y n))
    (hbad : ∀ Y, Tendsto (fun n => (P n).real (good Y n)ᶜ) atTop (𝓝 0))
    (cap : ℕ → ℕ → ℝ) (hcap : ∀ Y, Tendsto (cap Y) atTop atTop)
    (bounds : ℕ → ℕ → ℝ) (hbounds : ∀ Y, Tendsto (bounds Y) atTop (𝓝 C))
    (hmoment : ∀ Y : ℕ, ∀ᶠ n in atTop, (∫ x, (good Y n).indicator
      (fun x => min ‖anchoredNevanlinna (X n x) ((((Y : ℝ) + 1 : ℝ) : ℂ) * Complex.I)‖
        (cap Y n)) x ∂P n) ≤ bounds Y n) :
    ∀ᵐ s ∂ν, anchoredLinearCoefficient s = 0 := by
  apply anchoredLinearCoefficient_eq_zero_ae_of_uniform_height ν id measurable_id hanchor C
  intro Y
  have hY : (0 : ℝ) < (Y : ℝ) + 1 := by positivity
  have hw : (((((Y : ℝ) + 1 : ℝ) : ℂ) * Complex.I)).im ≠ 0 := by
    simpa using ne_of_gt hY
  exact (weak_limit_moment_of_good_capped_moments P X hX ν hweak
    (fun s => ‖anchoredNevanlinna s ((((Y : ℝ) + 1 : ℝ) : ℂ) * Complex.I)‖)
    (continuous_anchoredNevanlinna hw).norm (fun s => norm_nonneg _)
    (good Y) (hgood Y) (hbad Y) (cap Y) (hcap Y) C hC (bounds Y) (hbounds Y) (hmoment Y)).2

end GeneralizedBulk.Analysis
