import GaussianWave.BS.DensityMarginals
import GaussianWave.GaussianProduct

/-! Conditional gluing of an arbitrary finite family over a common core.
The literal comparison density is normalized from actual marginal laws. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

theorem integrable_pi_product_real {A Y : Type*} [Fintype A] [MeasurableSpace Y]
    (my : Measure Y) [SigmaFinite my] (f : A → Y → ℝ) (hf : ∀ a,Integrable (f a) my) :
    Integrable (fun y : A → Y => ∏ a,f a (y a)) (Measure.pi (fun _ : A => my)) := by
  letI : MeasureSpace Y := ⟨my⟩
  simpa only [volume_pi] using Integrable.fintype_prod hf

theorem integral_pi_product_real {A Y : Type*} [Fintype A] [MeasurableSpace Y]
    (my : Measure Y) [SigmaFinite my] (f : A → Y → ℝ) :
    (∫ y : A → Y,∏ a,f a (y a) ∂Measure.pi (fun _ : A => my)) = ∏ a,∫ y,f a y ∂my := by
  let ms : ∀ _ : A,MeasureSpace Y := fun _ => ⟨my⟩
  have h := @integral_fintype_prod_eq_prod ℝ inferInstance A inferInstance (fun _ => Y) f ms
    (fun _ => (inferInstance : SigmaFinite my))
  simpa only [volume_pi] using h

section Family
variable {A Y Z : Type*} [Fintype A] [MeasurableSpace Y] [MeasurableSpace Z]
  (my : Measure Y) (mz : Measure Z) [SigmaFinite my] [SigmaFinite mz]

def finiteConditionalGluingDensity
    (p : A → PositiveEntropyDensity (mz.prod my)) (s : PositiveEntropyDensity mz)
    (zy : Z × (A → Y)) : ℝ :=
  s.density zy.1 * ∏ a,(p a).density (zy.1,zy.2 a) / s.density zy.1

theorem finiteConditionalGluingDensity_positive
    (p : A → PositiveEntropyDensity (mz.prod my)) (s : PositiveEntropyDensity mz)
    (zy : Z × (A → Y)) : 0 < finiteConditionalGluingDensity my mz p s zy := by
  apply mul_pos (s.positive _)
  apply Finset.prod_pos
  intro a _
  exact div_pos ((p a).positive _) (s.positive _)

theorem measurable_finiteConditionalGluingDensity
    (p : A → PositiveEntropyDensity (mz.prod my)) (s : PositiveEntropyDensity mz) :
    Measurable (finiteConditionalGluingDensity my mz p s) := by
  apply (s.measurable.comp measurable_fst).mul
  apply Finset.measurable_prod
  intro a _
  exact ((p a).measurable.comp (measurable_fst.prodMk
    ((measurable_pi_apply a).comp measurable_snd))).div (s.measurable.comp measurable_fst)

theorem finiteConditionalGluingDensity_normalized
    (p : A → PositiveEntropyDensity (mz.prod my)) (s : PositiveEntropyDensity mz)
    (hp : ∀ a,∀ᵐ z ∂mz,(∫ y,(p a).density (z,y) ∂my) = s.density z) :
    Integrable (finiteConditionalGluingDensity my mz p s) (mz.prod (Measure.pi (fun _ : A => my))) ∧
      (∫ zy,finiteConditionalGluingDensity my mz p s zy ∂mz.prod (Measure.pi (fun _ : A => my))) = 1 := by
  have hpoint : ∀ᵐ z ∂mz,∀ a,Integrable (fun y => (p a).density (z,y)) my ∧
      (∫ y,(p a).density (z,y) ∂my) = s.density z := by
    apply (ae_all_iff).mpr
    intro a
    filter_upwards [(p a).integrable.prod_right_ae,hp a] with z hzi hzn
    exact ⟨hzi,hzn⟩
  have hprod : ∀ᵐ z ∂mz,Integrable
      (fun y : A → Y => finiteConditionalGluingDensity my mz p s (z,y)) (Measure.pi (fun _ : A => my)) := by
    filter_upwards [hpoint] with z hz
    change Integrable (fun y : A → Y => s.density z * ∏ a,(p a).density (z,y a)/s.density z)
      (Measure.pi (fun _ : A => my))
    exact (integrable_pi_product_real my (fun a y => (p a).density (z,y)/s.density z)
      (fun a => (hz a).1.div_const (s.density z))).const_mul (s.density z)
  have hvalue : ∀ᵐ z ∂mz,(∫ y : A → Y,finiteConditionalGluingDensity my mz p s (z,y)
      ∂Measure.pi (fun _ : A => my)) = s.density z := by
    filter_upwards [hpoint] with z hz
    change (∫ y : A → Y,s.density z * ∏ a,(p a).density (z,y a)/s.density z
      ∂Measure.pi (fun _ : A => my)) = s.density z
    rw [integral_const_mul,integral_pi_product_real my
      (fun a y => (p a).density (z,y)/s.density z)]
    have he (a : A) : (∫ y,(p a).density (z,y)/s.density z ∂my) = 1 := by
      rw [integral_div,(hz a).2,div_self (s.positive z).ne']
    simp only [he,Finset.prod_const_one,mul_one]
  have hnorm : Integrable (fun z => ∫ y : A → Y,
      ‖finiteConditionalGluingDensity my mz p s (z,y)‖ ∂Measure.pi (fun _ : A => my)) mz := by
    apply s.integrable.congr
    filter_upwards [hvalue] with z hz
    have heq : (fun y : A → Y => ‖finiteConditionalGluingDensity my mz p s (z,y)‖) =
        (fun y => finiteConditionalGluingDensity my mz p s (z,y)) := by
      funext y
      rw [Real.norm_eq_abs,abs_of_pos (finiteConditionalGluingDensity_positive my mz p s (z,y))]
    rw [heq]
    exact hz.symm
  have hi := (integrable_prod_iff
    (measurable_finiteConditionalGluingDensity my mz p s).aestronglyMeasurable).mpr ⟨hprod,hnorm⟩
  refine ⟨hi,?_⟩
  rw [integral_prod _ hi]
  exact (integral_congr_ae hvalue).trans s.integral_one

def finiteConditionalGluingLaw
    (p : A → PositiveEntropyDensity (mz.prod my)) (s : PositiveEntropyDensity mz) :
    Measure (Z × (A → Y)) :=
  (mz.prod (Measure.pi (fun _ : A => my))).withDensity
    (fun zy => ENNReal.ofReal (finiteConditionalGluingDensity my mz p s zy))

theorem log_finiteConditionalGluingDensity
    (p : A → PositiveEntropyDensity (mz.prod my)) (s : PositiveEntropyDensity mz)
    (zy : Z × (A → Y)) :
    Real.log (finiteConditionalGluingDensity my mz p s zy) =
      Real.log (s.density zy.1) + ∑ a,(Real.log ((p a).density (zy.1,zy.2 a))-Real.log (s.density zy.1)) := by
  unfold finiteConditionalGluingDensity
  rw [Real.log_mul (s.positive _).ne'
    (Finset.prod_ne_zero_iff.mpr (fun a _ => (div_pos ((p a).positive _) (s.positive _)).ne')),
    Real.log_prod]
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    exact Real.log_div ((p a).positive _).ne' (s.positive _).ne'
  · intro a _
    exact (div_pos ((p a).positive _) (s.positive _)).ne'

theorem finiteConditionalGluing_crossEntropy
    (f : PositiveEntropyDensity (mz.prod (Measure.pi (fun _ : A => my))))
    (p : A → PositiveEntropyDensity (mz.prod my)) (s : PositiveEntropyDensity mz)
    (hp : ∀ a,Measure.map (fun zy : Z × (A → Y) => (zy.1,zy.2 a)) f.law = (p a).law)
    (hs : Measure.map Prod.fst f.law = s.law) :
    Integrable (fun zy => f.density zy * Real.log (finiteConditionalGluingDensity my mz p s zy))
      (mz.prod (Measure.pi (fun _ : A => my))) ∧
    (∫ zy,f.density zy * Real.log (finiteConditionalGluingDensity my mz p s zy)
      ∂mz.prod (Measure.pi (fun _ : A => my))) =
      (Fintype.card A-1 : ℝ)*s.entropy - ∑ a,(p a).entropy := by
  have hz := f.integrable_cross_of_map s _ measurable_fst hs
  have ha (a : A) : Integrable
      (fun zy : Z × (A → Y) => f.density zy * Real.log ((p a).density (zy.1,zy.2 a)))
      (mz.prod (Measure.pi (fun _ : A => my))) :=
    f.integrable_cross_of_map (p a) _
      (measurable_fst.prodMk ((measurable_pi_apply a).comp measurable_snd)) (hp a)
  have he : (fun zy => f.density zy * Real.log (finiteConditionalGluingDensity my mz p s zy)) =
      (fun zy : Z × (A → Y) => f.density zy * Real.log (s.density zy.1) +
        ∑ a,(f.density zy * Real.log ((p a).density (zy.1,zy.2 a)) -
          f.density zy * Real.log (s.density zy.1))) := by
    funext zy
    rw [log_finiteConditionalGluingDensity,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he]
  have hsum := integrable_finset_sum Finset.univ (fun a _ => (ha a).sub hz)
  refine ⟨hz.add hsum,?_⟩
  rw [integral_add (f := fun zy : Z × (A → Y) => f.density zy * Real.log (s.density zy.1))
    (g := fun zy => ∑ a,(f.density zy * Real.log ((p a).density (zy.1,zy.2 a)) -
      f.density zy * Real.log (s.density zy.1))) hz hsum,
    integral_finset_sum (f := fun a (zy : Z × (A → Y)) =>
      f.density zy * Real.log ((p a).density (zy.1,zy.2 a)) -
        f.density zy * Real.log (s.density zy.1)) Finset.univ (fun a _ => (ha a).sub hz)]
  have hzi := f.integral_cross_of_map s _ measurable_fst hs
  have hai (a : A) := f.integral_cross_of_map (p a) _
    (measurable_fst.prodMk ((measurable_pi_apply a).comp measurable_snd)) (hp a)
  simp only [Function.comp_apply] at hzi hai
  simp_rw [integral_sub (ha _) hz,hai,hzi]
  rw [Finset.sum_sub_distrib,Finset.sum_neg_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

theorem finiteConditionalGluing_fibers_of_marginals
    (f : PositiveEntropyDensity (mz.prod (Measure.pi (fun _ : A => my))))
    (p : A → PositiveEntropyDensity (mz.prod my)) (s : PositiveEntropyDensity mz)
    (hp : ∀ a,Measure.map (fun zy : Z × (A → Y) => (zy.1,zy.2 a)) f.law = (p a).law)
    (hs : Measure.map Prod.fst f.law = s.law) :
    ∀ a,∀ᵐ z ∂mz,(∫ y,(p a).density (z,y) ∂my) = s.density z := by
  intro a
  apply (p a).fiber_integral_eq_of_map_fst my mz s
  have hm : Measurable (fun zy : Z × (A → Y) => (zy.1,zy.2 a)) :=
    measurable_fst.prodMk ((measurable_pi_apply a).comp measurable_snd)
  rw [← hp a,Measure.map_map measurable_fst hm]
  exact hs

theorem finiteStrongSubadditivity_of_marginals
    (f : PositiveEntropyDensity (mz.prod (Measure.pi (fun _ : A => my))))
    (p : A → PositiveEntropyDensity (mz.prod my)) (s : PositiveEntropyDensity mz)
    (hp : ∀ a,Measure.map (fun zy : Z × (A → Y) => (zy.1,zy.2 a)) f.law = (p a).law)
    (hs : Measure.map Prod.fst f.law = s.law) :
    0 ≤ (∑ a,(p a).entropy) - (Fintype.card A-1 : ℝ)*s.entropy - f.entropy := by
  obtain ⟨hgi,hgn⟩ := finiteConditionalGluingDensity_normalized my mz p s
    (finiteConditionalGluing_fibers_of_marginals my mz f p s hp hs)
  obtain ⟨hcross,hvalue⟩ := finiteConditionalGluing_crossEntropy my mz f p s hp hs
  have h := densityEntropy_le_crossEntropy _ f.density (finiteConditionalGluingDensity my mz p s)
    (fun zy => (f.positive zy).le) (finiteConditionalGluingDensity_positive my mz p s)
    f.integrable hgi f.integral_one hgn f.integrable_log hcross
  rw [hvalue] at h
  change f.entropy ≤ _ at h
  linarith

theorem finiteStrongSubadditivity_equality_iff_of_marginals
    (f : PositiveEntropyDensity (mz.prod (Measure.pi (fun _ : A => my))))
    (p : A → PositiveEntropyDensity (mz.prod my)) (s : PositiveEntropyDensity mz)
    (hp : ∀ a,Measure.map (fun zy : Z × (A → Y) => (zy.1,zy.2 a)) f.law = (p a).law)
    (hs : Measure.map Prod.fst f.law = s.law) :
    ((∑ a,(p a).entropy) - (Fintype.card A-1 : ℝ)*s.entropy - f.entropy = 0) ↔
      f.law = finiteConditionalGluingLaw my mz p s := by
  obtain ⟨hgi,hgn⟩ := finiteConditionalGluingDensity_normalized my mz p s
    (finiteConditionalGluing_fibers_of_marginals my mz f p s hp hs)
  obtain ⟨hcross,hvalue⟩ := finiteConditionalGluing_crossEntropy my mz f p s hp hs
  have h := densityEntropy_eq_crossEntropy_iff_measure_eq _ f.density (finiteConditionalGluingDensity my mz p s)
    f.measurable (measurable_finiteConditionalGluingDensity my mz p s)
    (fun zy => (f.positive zy).le) (finiteConditionalGluingDensity_positive my mz p s)
    f.integrable hgi f.integral_one hgn f.integrable_log hcross
  rw [hvalue] at h
  change (f.entropy = -((Fintype.card A-1 : ℝ)*s.entropy - ∑ a,(p a).entropy)) ↔
    f.law = finiteConditionalGluingLaw my mz p s at h
  rw [← h]
  constructor <;> intro hh <;> linarith

end Family
end GaussianWave.BS
