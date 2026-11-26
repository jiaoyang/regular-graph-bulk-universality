import GeneralizedBulk.Graph.MicroscopicMomentBounds
import GeneralizedBulk.Analysis.AnchoredMomentTransfer

/-! Every actual scalar/counting subsequential limit inherits genuine
uncapped moments and zero affine coefficient from the proved finite caps. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem microscopic_limit_moments_of_caps {P : Measure Ω} [IsProbabilityMeasure P]
    (E sigma center : ℝ) (good : ℕ → Set Ω) (hgood : ∀ n,MeasurableSet (good n))
    (hbad : Tendsto (fun n => P.real (good n)ᶜ) atTop (nhds 0))
    (cap : ℕ → ℝ) (hcap0 : ∀ n,0 ≤ cap n) (hcap : Tendsto cap atTop atTop)
    (constants : ℕ → ℝ) (hconstants : ∀ q,0 ≤ constants q)
    (bounds : ℕ → ℕ → ℝ) (hbounds : ∀ q,Tendsto (bounds q) atTop (nhds (constants q)))
    (hmoment : ∀ Y q : ℕ,∀ᶠ n in atTop,
      (∫ ω,(good n).indicator (fun ω => min (D.microscopicVerticalNorm n ω E sigma center Y) (cap n)^q) ω ∂P) ≤ bounds q n)
    (r : ℕ → ℕ) (hr : StrictMono r) (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hweak : WeakLawConverges (fun n => Measure.map (fun ω => D.microscopicCountingState (r n) ω E sigma center) P) ν) :
    AllMoments ν (fun s : AnchoredCountingState => s.val.2) ∧
      (∀ᵐ s ∂ν,anchoredLinearCoefficient s=0) ∧
      ∀ Y q : ℕ,q ≠ 0 →
      Integrable (fun s : AnchoredCountingState => ‖anchoredNevanlinna s ((((Y : ℝ)+1 : ℝ) : ℂ)*Complex.I)‖^q) ν ∧
        (∫ s : AnchoredCountingState,‖anchoredNevanlinna s ((((Y : ℝ)+1 : ℝ) : ℂ)*Complex.I)‖^q ∂ν) ≤ constants q := by
  have hrat : Tendsto r atTop atTop := hr.tendsto_atTop
  have hM (Y q : ℕ) (hq : q ≠ 0) :
      Integrable (fun s : AnchoredCountingState => ‖anchoredNevanlinna s ((((Y : ℝ)+1 : ℝ) : ℂ)*Complex.I)‖^q) ν ∧
        (∫ s : AnchoredCountingState,‖anchoredNevanlinna s ((((Y : ℝ)+1 : ℝ) : ℂ)*Complex.I)‖^q ∂ν) ≤ constants q := by
    have hw : (((((Y : ℝ)+1 : ℝ) : ℂ)*Complex.I)).im ≠ 0 := by simp; positivity
    apply weak_limit_moment_of_good_capped_moments (fun _ : ℕ => P)
      (fun n ω => D.microscopicCountingState (r n) ω E sigma center)
      (fun n => D.measurable_microscopicCountingState (r n) E sigma center) ν hweak
      (fun s : AnchoredCountingState => ‖anchoredNevanlinna s ((((Y : ℝ)+1 : ℝ) : ℂ)*Complex.I)‖^q)
      ((continuous_anchoredNevanlinna hw).norm.pow q) (fun s => pow_nonneg (norm_nonneg _) q)
      (fun n => good (r n)) (fun n => hgood (r n)) (hbad.comp hrat)
      (fun n => cap (r n)^q) ((tendsto_pow_atTop hq).comp (hcap.comp hrat))
      (constants q) (hconstants q) (fun n => bounds q (r n)) ((hbounds q).comp hrat)
    filter_upwards [hrat.eventually (hmoment Y q)] with n hn
    simpa only [microscopicVerticalNorm,nonnegative_min_pow _ _ (norm_nonneg _) (hcap0 (r n)) q] using hn
  have hAll : AllMoments ν (fun s : AnchoredCountingState => s.val.2) := by
    refine ⟨(measurable_snd.comp measurable_subtype_coe).aestronglyMeasurable,fun q => ?_⟩
    by_cases hq : q=0
    · subst q
      simpa only [pow_zero] using integrable_const (μ := ν) (1 : ℝ)
    · simpa only [Nat.cast_zero,zero_add,Complex.ofReal_one,one_mul,anchoredNevanlinna_I] using (hM 0 q hq).1
  have hanchor : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν := by
    simpa only [pow_one] using hAll.norm_pow 1
  have hzero := anchoredLinearCoefficient_eq_zero_ae_of_uniform_height ν id measurable_id hanchor (constants 1)
    (fun Y => by simpa only [pow_one,id_eq] using (hM Y 1 (by norm_num)).2)
  exact ⟨hAll,hzero,hM⟩

end GeneralizedBulk.External.RegularSpectralData
