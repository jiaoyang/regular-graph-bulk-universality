import BourgadeHuang.CharacteristicRatioMeasurability
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! State measurability of actual Cauchy-series coefficients. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter Complex
namespace BourgadeHuang

/-- Jointly measurable circle evaluations give strongly measurable actual
Cauchy multilinear coefficients. No formal coefficient is supplied as data. -/
theorem stronglyMeasurable_cauchyPowerSeries_of_circle
    (F : AnchoredCountingState → ℂ → ℂ) (u : ℂ) (R : ℝ)
    (hF : Measurable (fun p : ℝ × AnchoredCountingState => F p.2 (circleMap u R p.1))) (n : ℕ) :
    StronglyMeasurable (fun s => cauchyPowerSeries (F s) u R n) := by
  have hcircle : Measurable (fun p : ℝ × AnchoredCountingState => circleMap u R p.1) :=
    (measurable_circleMap u R).comp measurable_fst
  have hderiv : Measurable (fun p : ℝ × AnchoredCountingState => deriv (circleMap u R) p.1) := by
    simp only [deriv_circleMap]
    exact ((measurable_circleMap 0 R).comp measurable_fst).mul measurable_const
  have hk : Measurable (fun p : ℝ × AnchoredCountingState =>
      deriv (circleMap u R) p.1 •
        ((circleMap u R p.1-u)⁻¹^n • (circleMap u R p.1-u)⁻¹ • F p.2 (circleMap u R p.1))) :=
    hderiv.smul (((hcircle.sub measurable_const).inv.pow_const n).smul
      ((hcircle.sub measurable_const).inv.smul hF))
  have hi : StronglyMeasurable (fun s =>
      ∫ θ in Set.Icc (0:ℝ) (2*Real.pi), deriv (circleMap u R) θ •
        ((circleMap u R θ-u)⁻¹^n • (circleMap u R θ-u)⁻¹ • F s (circleMap u R θ))) :=
    hk.stronglyMeasurable.integral_prod_left
  have hc := hi.const_smul ((2*Real.pi*Complex.I:ℂ)⁻¹)
  have hm := (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin n) ℂ).continuous.comp_stronglyMeasurable hc
  simpa only [cauchyPowerSeries, circleIntegral_def_Icc,
    ContinuousMultilinearMap.piFieldEquiv] using hm

theorem stronglyMeasurable_ratio_cauchyPowerSeries (u b : ℂ) (R : ℝ)
    (hcircle : ∀ θ : ℝ, SameOpenHalfPlane (circleMap u R θ) b) (n : ℕ) :
    StronglyMeasurable (fun s : AnchoredCountingState =>
      cauchyPowerSeries (fun z => anchoredCharacteristicRatio s z b) u R n) := by
  apply stronglyMeasurable_cauchyPowerSeries_of_circle
  apply measurable_uncurry_of_continuous_of_measurable (u := fun θ : ℝ =>
    fun s : AnchoredCountingState => anchoredCharacteristicRatio s (circleMap u R θ) b)
  · intro s
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (hasDerivAt_anchoredCharacteristicRatio s (hcircle θ)).continuousAt.comp
      (continuous_circleMap u R).continuousAt
  · intro θ
    exact measurable_anchoredCharacteristicRatio (hcircle θ)

theorem stronglyMeasurable_reverseRatio_cauchyPowerSeries (u b : ℂ) (R : ℝ)
    (hcircle : ∀ θ : ℝ, SameOpenHalfPlane b (circleMap u R θ)) (n : ℕ) :
    StronglyMeasurable (fun s : AnchoredCountingState =>
      cauchyPowerSeries (fun z => anchoredCharacteristicRatio s b z) u R n) := by
  apply stronglyMeasurable_cauchyPowerSeries_of_circle
  apply measurable_uncurry_of_continuous_of_measurable (u := fun θ : ℝ =>
    fun s : AnchoredCountingState => anchoredCharacteristicRatio s b (circleMap u R θ))
  · intro s
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (hasDerivAt_anchoredCharacteristicRatio_denominator s (hcircle θ)).continuousAt.comp
      (continuous_circleMap u R).continuousAt
  · intro θ
    exact measurable_anchoredCharacteristicRatio (hcircle θ)

end BourgadeHuang
