import GaussianWave.BS.FiniteConditionalGluing
import GaussianWave.BS.RelativeConditionalEntropy

/-! Actual independent product densities and their conditional gluing. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

theorem pi_positiveDensity_law {A Y : Type*} [Fintype A] [MeasurableSpace Y]
    (my : Measure Y) [SigmaFinite my] (p : A → PositiveEntropyDensity my) :
    Measure.pi (fun a => (p a).law) =
      (Measure.pi (fun _ : A => my)).withDensity
        (fun y => ENNReal.ofReal (∏ a, (p a).density (y a))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hi (a : A) : Integrable (p a).density (my.restrict (s a)) := (p a).integrable.restrict
  let ms : ∀ _ : A, MeasureSpace Y := fun a => ⟨my.restrict (s a)⟩
  have hpi : Integrable (fun y : A → Y => ∏ a, (p a).density (y a))
      (Measure.pi (fun a => my.restrict (s a))) := by
    simpa only [volume_pi] using
      (@Integrable.fintype_prod_dep ℝ inferInstance A inferInstance (fun _ => Y)
        (fun a => (p a).density) ms (fun a =>
          (inferInstance : SigmaFinite (my.restrict (s a)))) hi)
  rw [← ofReal_integral_eq_lintegral_ofReal hpi (ae_of_all _ (fun y =>
    Finset.prod_nonneg (fun a _ => (p a).positive (y a) |>.le)))]
  have hint : (∫ y : A → Y, ∏ a, (p a).density (y a)
      ∂Measure.pi (fun a => my.restrict (s a))) =
      ∏ a, ∫ y, (p a).density y ∂my.restrict (s a) := by
    simpa only [volume_pi] using
      (@integral_fintype_prod_eq_prod ℝ inferInstance A inferInstance (fun _ => Y)
        (fun a => (p a).density) ms (fun a =>
          (inferInstance : SigmaFinite (my.restrict (s a)))))
  rw [hint, ENNReal.ofReal_prod_of_nonneg (fun a _ =>
    integral_nonneg (fun y => ((p a).positive y).le))]
  apply Finset.prod_congr rfl
  intro a _
  rw [PositiveEntropyDensity.law, withDensity_apply _ (hs a)]
  exact ofReal_integral_eq_lintegral_ofReal (hi a) (ae_of_all _ (fun y => ((p a).positive y).le))

theorem finiteConditionalGluingLaw_product {A Y Z : Type*} [Fintype A]
    [MeasurableSpace Y] [MeasurableSpace Z]
    (my : Measure Y) (mz : Measure Z) [SigmaFinite my] [SigmaFinite mz]
    (s : PositiveEntropyDensity mz) (q : A → PositiveEntropyDensity my) :
    finiteConditionalGluingLaw my mz (fun a => s.prod (q a)) s =
      s.law.prod (Measure.pi (fun a => (q a).law)) := by
  have hm : Measurable (fun y : A → Y => ∏ a, (q a).density (y a)) :=
    Finset.measurable_prod _ (fun a _ => (q a).measurable.comp (measurable_pi_apply a))
  rw [pi_positiveDensity_law my q, PositiveEntropyDensity.law,
    prod_withDensity s.measurable.ennreal_ofReal hm.ennreal_ofReal]
  unfold finiteConditionalGluingLaw
  congr 1
  funext zy
  have hpoint : finiteConditionalGluingDensity my mz (fun a => s.prod (q a)) s zy =
      s.density zy.1 * ∏ a, (q a).density (zy.2 a) := by
    unfold finiteConditionalGluingDensity
    congr 1
    apply Finset.prod_congr rfl
    intro a _
    change s.density zy.1 * (q a).density (zy.2 a) / s.density zy.1 = _
    exact mul_div_cancel_left₀ _ (s.positive _).ne'
  rw [hpoint, ENNReal.ofReal_mul (s.positive _).le]

end GaussianWave.BS
