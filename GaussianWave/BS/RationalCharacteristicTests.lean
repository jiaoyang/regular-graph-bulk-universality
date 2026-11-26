import GaussianWave.GaussianContinuity

/-! A concrete countable family of [0,1] bounded continuous tests determines
every finite real probability law: normalized real and imaginary parts of
characteristic functions at rational coefficient vectors. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

variable {J : Type*} [Fintype J]

def characteristicPart (b : Bool) (z : ℂ) : ℝ := if b then z.re else z.im

private theorem abs_characteristicPart_le (b : Bool) (z : ℂ) :
    |characteristicPart b z| ≤ ‖z‖ := by
  cases b
  · exact Complex.abs_im_le_norm z
  · exact Complex.abs_re_le_norm z

private theorem continuous_characteristicPart (b : Bool) : Continuous (characteristicPart b) := by
  cases b
  · exact Complex.continuous_im
  · exact Complex.continuous_re

private theorem characteristic_integrand_norm (t x : J → ℝ) :
    ‖Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I)‖=1 := by simp [Complex.norm_exp]

/-- Either normalized real or normalized imaginary characteristic part. -/
def boundedCharacteristicTest (t : J → ℝ) (b : Bool) :
    BoundedContinuousFunction (J → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (characteristicPart b (Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I))+1)/2)
    (((continuous_characteristicPart b).comp (linearCharacteristic t).continuous).add continuous_const |>.div_const 2)
    1 (fun x => by
      have h := abs_characteristicPart_le b (Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I))
      rw [characteristic_integrand_norm] at h
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor <;> linarith [(abs_le.mp h).1,(abs_le.mp h).2])

theorem boundedCharacteristicTest_bounds (t : J → ℝ) (b : Bool) (x : J → ℝ) :
    0 ≤ boundedCharacteristicTest t b x ∧ boundedCharacteristicTest t b x ≤ 1 := by
  have h := abs_characteristicPart_le b (Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I))
  rw [characteristic_integrand_norm] at h
  simp only [boundedCharacteristicTest,BoundedContinuousFunction.coe_ofNormedAddCommGroup]
  constructor <;> linarith [(abs_le.mp h).1,(abs_le.mp h).2]

private theorem integrable_characteristicIntegrand (μ : Measure (J → ℝ)) [IsProbabilityMeasure μ]
    (t : J → ℝ) : Integrable (fun x => Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I)) μ :=
  (integrable_const (1 : ℝ)).mono' (linearCharacteristic t).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => (characteristic_integrand_norm t x).le))

/-- The test integral is the normalized corresponding characteristic part. -/
theorem integral_boundedCharacteristicTest (μ : Measure (J → ℝ)) [IsProbabilityMeasure μ]
    (t : J → ℝ) (b : Bool) :
    (∫ x,boundedCharacteristicTest t b x ∂μ) =
      (characteristicPart b (∫ x,Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I) ∂μ)+1)/2 := by
  have hi := integrable_characteristicIntegrand μ t
  cases b
  · simp only [boundedCharacteristicTest,BoundedContinuousFunction.coe_ofNormedAddCommGroup,
      characteristicPart,Bool.false_eq_true,if_false]
    have him : Integrable (fun x : J → ℝ => (Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I)).im) μ := hi.im
    have he := integral_im hi
    change (∫ x,(Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I)).im ∂μ) =
      (∫ x,Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I) ∂μ).im at he
    rw [integral_div,integral_add him (integrable_const (1 : ℝ)),integral_const,he]
    simp
  · simp only [boundedCharacteristicTest,BoundedContinuousFunction.coe_ofNormedAddCommGroup,
      characteristicPart,if_true]
    have hre : Integrable (fun x : J → ℝ => (Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I)).re) μ := hi.re
    have he := integral_re hi
    change (∫ x,(Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I)).re ∂μ) =
      (∫ x,Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I) ∂μ).re at he
    rw [integral_div,integral_add hre (integrable_const (1 : ℝ)),integral_const,he]
    simp

/-- Characteristic integrals are continuous in their coefficient vector,
proved by dominated convergence rather than a moment hypothesis. -/
theorem continuous_finiteCharacteristicIntegral (μ : Measure (J → ℝ)) [IsProbabilityMeasure μ] :
    Continuous (fun t : J → ℝ =>
      ∫ x,Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I) ∂μ) := by
  apply continuous_of_dominated
    (fun t => (linearCharacteristic t).continuous.aestronglyMeasurable)
    (fun t => Filter.Eventually.of_forall (fun x => (characteristic_integrand_norm t x).le))
    (integrable_const (1 : ℝ))
  apply Filter.Eventually.of_forall
  intro x
  apply Complex.continuous_exp.comp
  apply Continuous.mul _ continuous_const
  apply Complex.continuous_ofReal.comp
  exact continuous_finset_sum _ (fun j _ => (continuous_apply j).mul continuous_const)

/-- Equality of only the rational normalized characteristic tests already
implies equality of the actual finite probability measures. -/
theorem measure_eq_of_rational_characteristic_tests
    (μ ν : Measure (J → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ (q : J → ℚ) (b : Bool),
      (∫ x,boundedCharacteristicTest (fun j => (q j : ℝ)) b x ∂μ) =
      ∫ x,boundedCharacteristicTest (fun j => (q j : ℝ)) b x ∂ν) : μ=ν := by
  let χ (P : Measure (J → ℝ)) (t : J → ℝ) :=
    ∫ x,Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I) ∂P
  have hr (q : J → ℚ) : χ μ (fun j => (q j : ℝ))=χ ν (fun j => (q j : ℝ)) := by
    apply Complex.ext
    · have hh := h q true
      rw [integral_boundedCharacteristicTest,integral_boundedCharacteristicTest] at hh
      simp only [characteristicPart,if_true] at hh
      dsimp only [χ]
      linarith
    · have hh := h q false
      rw [integral_boundedCharacteristicTest,integral_boundedCharacteristicTest] at hh
      simp only [characteristicPart,Bool.false_eq_true,if_false] at hh
      dsimp only [χ]
      linarith
  have hd : DenseRange (fun q : J → ℚ => fun j => (q j : ℝ)) :=
    DenseRange.piMap (fun _ : J => Rat.denseRange_cast)
  have he := hd.equalizer (continuous_finiteCharacteristicIntegral μ)
    (continuous_finiteCharacteristicIntegral ν) (funext hr)
  apply measure_eq_of_linear_characteristic
  intro t
  exact congrFun he t

end GaussianWave.BS
