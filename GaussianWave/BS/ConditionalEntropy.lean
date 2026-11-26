import GaussianWave.BS.RelativeEntropyEquality

/-!
# Strong subadditivity for actual finite-entropy density laws

The comparison law is the literal conditional-independent gluing of the
two overlapping marginals. Its normalization and all cross integrability
are derived from the density and marginal identities.
-/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

structure PositiveEntropyDensity {E : Type*} [MeasurableSpace E] (m : Measure E) where
  density : E → ℝ
  measurable : Measurable density
  positive : ∀ x, 0 < density x
  integrable : Integrable density m
  integral_one : (∫ x, density x ∂m) = 1
  integrable_log : Integrable (fun x => density x * Real.log (density x)) m

namespace PositiveEntropyDensity
variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
  {m : Measure E} {n : Measure F}

def law (p : PositiveEntropyDensity m) : Measure E :=
  m.withDensity (fun x => ENNReal.ofReal (p.density x))

def entropy (p : PositiveEntropyDensity m) : ℝ := densityEntropy m p.density

instance (p : PositiveEntropyDensity m) : IsProbabilityMeasure p.law := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal p.integrable
      (Filter.Eventually.of_forall (fun x => (p.positive x).le)), p.integral_one]
  norm_num

theorem integrable_log_law (p : PositiveEntropyDensity m) :
    Integrable (fun x => Real.log (p.density x)) p.law := by
  apply (integrable_withDensity_iff_integrable_smul' p.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (p.positive _).le, smul_eq_mul] using p.integrable_log

theorem integral_log_law (p : PositiveEntropyDensity m) :
    (∫ x, Real.log (p.density x) ∂p.law) = -p.entropy := by
  rw [law, integral_withDensity_eq_integral_toReal_smul p.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (p.positive _).le, smul_eq_mul, entropy, densityEntropy, neg_neg]

theorem integrable_cross_of_map (p : PositiveEntropyDensity m) (q : PositiveEntropyDensity n)
    (T : E → F) (hT : Measurable T) (hmap : Measure.map T p.law = q.law) :
    Integrable (fun x => p.density x * Real.log (q.density (T x))) m := by
  have hi := q.integrable_log_law
  rw [← hmap] at hi
  have hcomp := (integrable_map_measure (q.measurable.log.aestronglyMeasurable)
    hT.aemeasurable).mp hi
  have hh := (integrable_withDensity_iff_integrable_smul' p.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hcomp
  simpa only [ENNReal.toReal_ofReal (p.positive _).le, smul_eq_mul, Function.comp_apply] using hh

theorem integral_cross_of_map (p : PositiveEntropyDensity m) (q : PositiveEntropyDensity n)
    (T : E → F) (hT : Measurable T) (hmap : Measure.map T p.law = q.law) :
    (∫ x, p.density x * Real.log (q.density (T x)) ∂m) = -q.entropy := by
  have hh := integral_map (μ := p.law) hT.aemeasurable q.measurable.log.aestronglyMeasurable
  rw [hmap, q.integral_log_law, law,
    integral_withDensity_eq_integral_toReal_smul p.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at hh
  simpa only [ENNReal.toReal_ofReal (p.positive _).le, smul_eq_mul] using hh.symm

end PositiveEntropyDensity

section Gluing
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  (mx : Measure X) (my : Measure Y) (mz : Measure Z)
  [SigmaFinite mx] [SigmaFinite my] [SigmaFinite mz]

def conditionalGluingDensity
    (p : PositiveEntropyDensity (mz.prod mx)) (q : PositiveEntropyDensity (mz.prod my))
    (s : PositiveEntropyDensity mz) (zxy : Z × (X × Y)) : ℝ :=
  p.density (zxy.1, zxy.2.1) * q.density (zxy.1, zxy.2.2) / s.density zxy.1

theorem measurable_conditionalGluingDensity
    (p : PositiveEntropyDensity (mz.prod mx)) (q : PositiveEntropyDensity (mz.prod my))
    (s : PositiveEntropyDensity mz) : Measurable (conditionalGluingDensity mx my mz p q s) := by
  unfold conditionalGluingDensity
  exact ((p.measurable.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
    (q.measurable.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).div
    (s.measurable.comp measurable_fst)

theorem conditionalGluingDensity_positive
    (p : PositiveEntropyDensity (mz.prod mx)) (q : PositiveEntropyDensity (mz.prod my))
    (s : PositiveEntropyDensity mz) (zxy : Z × (X × Y)) :
    0 < conditionalGluingDensity mx my mz p q s zxy :=
  div_pos (mul_pos (p.positive _) (q.positive _)) (s.positive _)

theorem conditionalGluingDensity_normalized
    (p : PositiveEntropyDensity (mz.prod mx)) (q : PositiveEntropyDensity (mz.prod my))
    (s : PositiveEntropyDensity mz)
    (hp : ∀ᵐ z ∂mz, (∫ x, p.density (z, x) ∂mx) = s.density z)
    (hq : ∀ᵐ z ∂mz, (∫ y, q.density (z, y) ∂my) = s.density z) :
    Integrable (conditionalGluingDensity mx my mz p q s) (mz.prod (mx.prod my)) ∧
      (∫ zxy, conditionalGluingDensity mx my mz p q s zxy ∂mz.prod (mx.prod my)) = 1 := by
  have hprod : ∀ᵐ z ∂mz, Integrable
      (fun xy : X × Y => conditionalGluingDensity mx my mz p q s (z, xy)) (mx.prod my) := by
    filter_upwards [p.integrable.prod_right_ae, q.integrable.prod_right_ae] with z hpz hqz
    exact (hpz.mul_prod hqz).div_const (s.density z)
  have hint : ∀ᵐ z ∂mz,
      (∫ xy : X × Y, conditionalGluingDensity mx my mz p q s (z, xy) ∂mx.prod my) = s.density z := by
    filter_upwards [hp, hq] with z hpz hqz
    dsimp only [conditionalGluingDensity]
    rw [integral_div, integral_prod_mul (fun x => p.density (z, x))
      (fun y => q.density (z, y)), hpz, hqz]
    field_simp [(s.positive z).ne']
  have hinorm : Integrable (fun z => ∫ xy : X × Y,
      ‖conditionalGluingDensity mx my mz p q s (z, xy)‖ ∂mx.prod my) mz := by
    apply s.integrable.congr
    filter_upwards [hint] with z hz
    simpa only [Real.norm_eq_abs, abs_of_pos (conditionalGluingDensity_positive mx my mz p q s _)] using hz.symm
  have hi := (integrable_prod_iff
    (measurable_conditionalGluingDensity mx my mz p q s).aestronglyMeasurable).mpr ⟨hprod, hinorm⟩
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  exact (integral_congr_ae hint).trans s.integral_one

def conditionalGluingLaw
    (p : PositiveEntropyDensity (mz.prod mx)) (q : PositiveEntropyDensity (mz.prod my))
    (s : PositiveEntropyDensity mz) : Measure (Z × (X × Y)) :=
  (mz.prod (mx.prod my)).withDensity
    (fun x => ENNReal.ofReal (conditionalGluingDensity mx my mz p q s x))

theorem log_conditionalGluingDensity
    (p : PositiveEntropyDensity (mz.prod mx)) (q : PositiveEntropyDensity (mz.prod my))
    (s : PositiveEntropyDensity mz) (zxy : Z × (X × Y)) :
    Real.log (conditionalGluingDensity mx my mz p q s zxy) =
      Real.log (p.density (zxy.1, zxy.2.1)) +
        Real.log (q.density (zxy.1, zxy.2.2)) - Real.log (s.density zxy.1) := by
  unfold conditionalGluingDensity
  rw [Real.log_div (mul_pos (p.positive _) (q.positive _)).ne' (s.positive _).ne',
    Real.log_mul (p.positive _).ne' (q.positive _).ne']

theorem conditionalGluing_crossEntropy
    (f : PositiveEntropyDensity (mz.prod (mx.prod my)))
    (p : PositiveEntropyDensity (mz.prod mx)) (q : PositiveEntropyDensity (mz.prod my))
    (s : PositiveEntropyDensity mz)
    (hpx : Measure.map (fun zxy : Z × (X × Y) => (zxy.1, zxy.2.1)) f.law = p.law)
    (hqy : Measure.map (fun zxy : Z × (X × Y) => (zxy.1, zxy.2.2)) f.law = q.law)
    (hsz : Measure.map Prod.fst f.law = s.law) :
    Integrable (fun x => f.density x * Real.log (conditionalGluingDensity mx my mz p q s x))
      (mz.prod (mx.prod my)) ∧
    (∫ x, f.density x * Real.log (conditionalGluingDensity mx my mz p q s x) ∂mz.prod (mx.prod my)) =
      -p.entropy - q.entropy + s.entropy := by
  have hx := f.integrable_cross_of_map p _
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) hpx
  have hy := f.integrable_cross_of_map q _
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) hqy
  have hz := f.integrable_cross_of_map s _ measurable_fst hsz
  have he : (fun x => f.density x * Real.log (conditionalGluingDensity mx my mz p q s x)) =
      (fun x : Z × (X × Y) => f.density x * Real.log (p.density (x.1, x.2.1)) +
        f.density x * Real.log (q.density (x.1, x.2.2)) -
          f.density x * Real.log (s.density x.1)) := by
    funext x
    rw [log_conditionalGluingDensity]
    ring
  rw [he]
  refine ⟨(hx.add hy).sub hz, ?_⟩
  have hxi := f.integral_cross_of_map p _
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) hpx
  have hyi := f.integral_cross_of_map q _
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) hqy
  have hzi := f.integral_cross_of_map s _ measurable_fst hsz
  simp only [Function.comp_apply] at hxi hyi hzi
  rw [integral_sub (f := fun x : Z × (X × Y) =>
      f.density x * Real.log (p.density (x.1, x.2.1)) +
        f.density x * Real.log (q.density (x.1, x.2.2))) (hx.add hy) hz,
    integral_add (f := fun x : Z × (X × Y) =>
      f.density x * Real.log (p.density (x.1, x.2.1)))
      (g := fun x : Z × (X × Y) => f.density x * Real.log (q.density (x.1, x.2.2))) hx hy,
    hxi, hyi, hzi]
  ring

/-- Strong subadditivity proved against the actual normalized gluing law.
The fiber identities are ordinary consistency of the overlapping marginals. -/
theorem strongSubadditivity_nonneg
    (f : PositiveEntropyDensity (mz.prod (mx.prod my)))
    (p : PositiveEntropyDensity (mz.prod mx)) (q : PositiveEntropyDensity (mz.prod my))
    (s : PositiveEntropyDensity mz)
    (hpx : Measure.map (fun zxy : Z × (X × Y) => (zxy.1, zxy.2.1)) f.law = p.law)
    (hqy : Measure.map (fun zxy : Z × (X × Y) => (zxy.1, zxy.2.2)) f.law = q.law)
    (hsz : Measure.map Prod.fst f.law = s.law)
    (hp : ∀ᵐ z ∂mz, (∫ x, p.density (z, x) ∂mx) = s.density z)
    (hq : ∀ᵐ z ∂mz, (∫ y, q.density (z, y) ∂my) = s.density z) :
    0 ≤ p.entropy + q.entropy - s.entropy - f.entropy := by
  obtain ⟨hgi, hg⟩ := conditionalGluingDensity_normalized mx my mz p q s hp hq
  obtain ⟨hcross, hvalue⟩ := conditionalGluing_crossEntropy mx my mz f p q s hpx hqy hsz
  have h := densityEntropy_le_crossEntropy (mz.prod (mx.prod my)) f.density
    (conditionalGluingDensity mx my mz p q s) (fun x => (f.positive x).le)
    (conditionalGluingDensity_positive mx my mz p q s) f.integrable hgi
    f.integral_one hg f.integrable_log hcross
  rw [hvalue] at h
  change f.entropy ≤ _ at h
  linarith

/-- Zero conditional mutual information is equality with the actual
conditional-independent gluing, rather than an assumed Markov property. -/
theorem strongSubadditivity_eq_zero_iff
    (f : PositiveEntropyDensity (mz.prod (mx.prod my)))
    (p : PositiveEntropyDensity (mz.prod mx)) (q : PositiveEntropyDensity (mz.prod my))
    (s : PositiveEntropyDensity mz)
    (hpx : Measure.map (fun zxy : Z × (X × Y) => (zxy.1, zxy.2.1)) f.law = p.law)
    (hqy : Measure.map (fun zxy : Z × (X × Y) => (zxy.1, zxy.2.2)) f.law = q.law)
    (hsz : Measure.map Prod.fst f.law = s.law)
    (hp : ∀ᵐ z ∂mz, (∫ x, p.density (z, x) ∂mx) = s.density z)
    (hq : ∀ᵐ z ∂mz, (∫ y, q.density (z, y) ∂my) = s.density z) :
    (p.entropy + q.entropy - s.entropy - f.entropy = 0) ↔
      f.law = conditionalGluingLaw mx my mz p q s := by
  obtain ⟨hgi, hg⟩ := conditionalGluingDensity_normalized mx my mz p q s hp hq
  obtain ⟨hcross, hvalue⟩ := conditionalGluing_crossEntropy mx my mz f p q s hpx hqy hsz
  have h := densityEntropy_eq_crossEntropy_iff_measure_eq (mz.prod (mx.prod my)) f.density
    (conditionalGluingDensity mx my mz p q s) f.measurable
    (measurable_conditionalGluingDensity mx my mz p q s) (fun x => (f.positive x).le)
    (conditionalGluingDensity_positive mx my mz p q s) f.integrable hgi
    f.integral_one hg f.integrable_log hcross
  rw [hvalue] at h
  change (f.entropy = -(-p.entropy - q.entropy + s.entropy)) ↔
    f.law = conditionalGluingLaw mx my mz p q s at h
  rw [← h]
  constructor <;> intro hh <;> linarith

end Gluing
end GaussianWave.BS
