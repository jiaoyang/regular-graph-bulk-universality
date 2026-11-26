import GaussianWave.BS.ConditionalEntropy

/-! Fiber density identities follow from equality of actual marginal laws.
In particular the final strong-subadditivity interface needs no additional
fiber-normalization or conditional-independence hypothesis. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

section Marginal
variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
  (mx : Measure X) (mz : Measure Z) [SigmaFinite mx] [SigmaFinite mz]

theorem PositiveEntropyDensity.map_fst_density
    (p : PositiveEntropyDensity (mz.prod mx)) :
    Measure.map Prod.fst p.law =
      mz.withDensity (fun z => ENNReal.ofReal (∫ x, p.density (z, x) ∂mx)) := by
  have hfm : Measurable (fun z => ∫ x, p.density (z, x) ∂mx) :=
    p.measurable.stronglyMeasurable.integral_prod_right'.measurable
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ measurable_fst, PositiveEntropyDensity.law,
    lintegral_withDensity_eq_lintegral_mul (g := fun zx : Z × X => φ zx.1)
      (mz.prod mx) p.measurable.ennreal_ofReal
      (hφ.comp measurable_fst),
    lintegral_withDensity_eq_lintegral_mul mz hfm.ennreal_ofReal hφ]
  simp only [Pi.mul_apply]
  rw [lintegral_prod (fun zx : Z × X => ENNReal.ofReal (p.density zx) * φ zx.1)
    ((p.measurable.ennreal_ofReal).mul (hφ.comp measurable_fst)).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [p.integrable.prod_right_ae] with z hz
  rw [lintegral_mul_const (f := fun x => ENNReal.ofReal (p.density (z, x))) (φ z)
      ((p.measurable.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal),
    ← ofReal_integral_eq_lintegral_ofReal hz
      (Filter.Eventually.of_forall (fun x => (p.positive (z, x)).le))]

theorem PositiveEntropyDensity.fiber_integral_eq_of_map_fst
    (p : PositiveEntropyDensity (mz.prod mx)) (s : PositiveEntropyDensity mz)
    (hmap : Measure.map Prod.fst p.law = s.law) :
    ∀ᵐ z ∂mz, (∫ x, p.density (z, x) ∂mx) = s.density z := by
  have hfm : Measurable (fun z => ∫ x, p.density (z, x) ∂mx) :=
    p.measurable.stronglyMeasurable.integral_prod_right'.measurable
  rw [p.map_fst_density mx mz] at hmap
  have hae := (withDensity_eq_iff_of_sigmaFinite hfm.ennreal_ofReal.aemeasurable
    s.measurable.ennreal_ofReal.aemeasurable).mp hmap
  filter_upwards [hae] with z hz
  have hreal := congrArg ENNReal.toReal hz
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun x => (p.positive (z, x)).le)),
    ENNReal.toReal_ofReal (s.positive z).le] using hreal

end Marginal

section SSA
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  (mx : Measure X) (my : Measure Y) (mz : Measure Z)
  [SigmaFinite mx] [SigmaFinite my] [SigmaFinite mz]

theorem strongSubadditivity_of_marginals
    (f : PositiveEntropyDensity (mz.prod (mx.prod my)))
    (p : PositiveEntropyDensity (mz.prod mx)) (q : PositiveEntropyDensity (mz.prod my))
    (s : PositiveEntropyDensity mz)
    (hpx : Measure.map (fun zxy : Z × (X × Y) => (zxy.1, zxy.2.1)) f.law = p.law)
    (hqy : Measure.map (fun zxy : Z × (X × Y) => (zxy.1, zxy.2.2)) f.law = q.law)
    (hsz : Measure.map Prod.fst f.law = s.law) :
    0 ≤ p.entropy + q.entropy - s.entropy - f.entropy := by
  have hp : Measure.map Prod.fst p.law = s.law := by
    rw [← hpx, Measure.map_map (f := fun zxy : Z × (X × Y) => (zxy.1, zxy.2.1)) measurable_fst
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))]
    exact hsz
  have hq : Measure.map Prod.fst q.law = s.law := by
    rw [← hqy, Measure.map_map (f := fun zxy : Z × (X × Y) => (zxy.1, zxy.2.2)) measurable_fst
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))]
    exact hsz
  exact strongSubadditivity_nonneg mx my mz f p q s hpx hqy hsz
    (p.fiber_integral_eq_of_map_fst mx mz s hp) (q.fiber_integral_eq_of_map_fst my mz s hq)

theorem strongSubadditivity_equality_iff_of_marginals
    (f : PositiveEntropyDensity (mz.prod (mx.prod my)))
    (p : PositiveEntropyDensity (mz.prod mx)) (q : PositiveEntropyDensity (mz.prod my))
    (s : PositiveEntropyDensity mz)
    (hpx : Measure.map (fun zxy : Z × (X × Y) => (zxy.1, zxy.2.1)) f.law = p.law)
    (hqy : Measure.map (fun zxy : Z × (X × Y) => (zxy.1, zxy.2.2)) f.law = q.law)
    (hsz : Measure.map Prod.fst f.law = s.law) :
    (p.entropy + q.entropy - s.entropy - f.entropy = 0) ↔
      f.law = conditionalGluingLaw mx my mz p q s := by
  have hp : Measure.map Prod.fst p.law = s.law := by
    rw [← hpx, Measure.map_map (f := fun zxy : Z × (X × Y) => (zxy.1, zxy.2.1)) measurable_fst
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))]
    exact hsz
  have hq : Measure.map Prod.fst q.law = s.law := by
    rw [← hqy, Measure.map_map (f := fun zxy : Z × (X × Y) => (zxy.1, zxy.2.2)) measurable_fst
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))]
    exact hsz
  exact strongSubadditivity_eq_zero_iff mx my mz f p q s hpx hqy hsz
    (p.fiber_integral_eq_of_map_fst mx mz s hp) (q.fiber_integral_eq_of_map_fst my mz s hq)

end SSA
end GaussianWave.BS
