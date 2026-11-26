import GaussianWave.BS.FiniteProductDensities

/-! Conditional gluing depends on actual marginal laws, rather than on
the arbitrary versions of their positive densities. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

theorem PositiveEntropyDensity.density_ae_eq_of_law_eq {X : Type*} [MeasurableSpace X]
    (m : Measure X) [SigmaFinite m] (p q : PositiveEntropyDensity m) (h : p.law = q.law) :
    p.density =ᵐ[m] q.density := by
  have he := (withDensity_eq_iff_of_sigmaFinite p.measurable.ennreal_ofReal.aemeasurable
    q.measurable.ennreal_ofReal.aemeasurable).mp h
  filter_upwards [he] with x hx
  have hh := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal (p.positive _).le,
    ENNReal.toReal_ofReal (q.positive _).le] using hh

theorem finiteConditionalGluingLaw_congr_of_laws {A Y Z : Type*} [Fintype A]
    [MeasurableSpace Y] [MeasurableSpace Z]
    (my : Measure Y) (mz : Measure Z) [SigmaFinite my] [SigmaFinite mz]
    (p q : A → PositiveEntropyDensity (mz.prod my))
    (s t : PositiveEntropyDensity mz)
    (hp : ∀ a, (p a).law = (q a).law) (hs : s.law = t.law) :
    finiteConditionalGluingLaw my mz p s = finiteConditionalGluingLaw my mz q t := by
  have hsz := PositiveEntropyDensity.density_ae_eq_of_law_eq mz s t hs
  have hpa (a : A) := Measure.ae_ae_of_ae_prod
    (PositiveEntropyDensity.density_ae_eq_of_law_eq (mz.prod my) (p a) (q a) (hp a))
  have hpz : ∀ᵐ z ∂mz, ∀ a, ∀ᵐ y ∂my, (p a).density (z, y) = (q a).density (z, y) :=
    (ae_all_iff).mpr hpa
  have hreal : finiteConditionalGluingDensity my mz p s =ᵐ[mz.prod (Measure.pi (fun _ : A => my))]
      finiteConditionalGluingDensity my mz q t := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      (measurable_finiteConditionalGluingDensity my mz p s)
      (measurable_finiteConditionalGluingDensity my mz q t))).mpr
    filter_upwards [hsz, hpz] with z hz hza
    have hy : ∀ᵐ y ∂Measure.pi (fun _ : A => my), ∀ a,
        (p a).density (z, y a) = (q a).density (z, y a) := by
      apply (ae_all_iff).mpr
      intro a
      exact (Measure.tendsto_eval_ae_ae (μ := fun _ : A => my) (i := a)).eventually (hza a)
    filter_upwards [hy] with y hy
    unfold finiteConditionalGluingDensity
    rw [hz]
    congr 1
    apply Finset.prod_congr rfl
    intro a _
    rw [hy a]
  apply withDensity_congr_ae
  exact hreal.mono (fun _ h => congrArg ENNReal.ofReal h)

end GaussianWave.BS
