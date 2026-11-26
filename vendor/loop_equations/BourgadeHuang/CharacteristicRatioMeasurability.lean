import BourgadeHuang.CharacteristicRatioDerivatives

/-! Measurability of the path observable is intrinsic to the state space and
requires neither a loop hierarchy nor a particular law. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem measurable_integrated_nevanlinna_ratioPath {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Measurable (fun s : AnchoredCountingState => ∫ t : RatioInterval,
      -(u-v)*anchoredNevanlinna s (ratioPath u v t) ∂ratioIntervalMeasure) := by
  have hm : Measurable (Function.uncurry (fun t : RatioInterval => fun s : AnchoredCountingState =>
      -(u-v)*anchoredNevanlinna s (ratioPath u v t))) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun s => continuous_const.mul (continuous_nevanlinna_ratioPath s huv))
      (fun t => (continuous_const.mul (continuous_anchoredNevanlinna (ratioPath_offReal huv t.property))).measurable)
  exact hm.stronglyMeasurable.integral_prod_left.measurable

theorem measurable_anchoredCharacteristicRatio {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Measurable (fun s : AnchoredCountingState => anchoredCharacteristicRatio s u v) :=
  Complex.continuous_exp.measurable.comp (measurable_integrated_nevanlinna_ratioPath huv)

end BourgadeHuang
