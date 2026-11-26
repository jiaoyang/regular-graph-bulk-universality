import BourgadeHuang.BulkExponentialControl

/-! Quantitative control of an exponential expectation near one. -/
noncomputable section
open MeasureTheory
namespace BourgadeHuang

theorem norm_exp_sub_one_le_mul_exp (z : ℂ) :
    ‖Complex.exp z-1‖ ≤ ‖z‖*Real.exp ‖z‖ := by
  simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp z 1

theorem exponential_expectation_close_of_second_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℂ) (hX : Measurable X)
    (hX2 : Integrable (fun x => ‖X x‖^2) μ)
    (he2 : Integrable (fun x => Real.exp (2*‖X x‖)) μ)
    {δ : ℝ} (hδ : 0<δ) :
    Integrable (fun x => Complex.exp (X x)) μ ∧
      ‖(∫ x, Complex.exp (X x) ∂μ)-1‖ ≤
        (∫ x, ‖X x‖^2 ∂μ)/(2*δ) + (δ/2)*(∫ x, Real.exp (2*‖X x‖) ∂μ) := by
  have hei : Integrable (fun x => Complex.exp (X x)) μ := by
    apply he2.mono' (Complex.continuous_exp.measurable.comp hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => (Complex.norm_exp_le_exp_norm _).trans
      (Real.exp_le_exp.mpr (by linarith [norm_nonneg (X x)]))
  refine ⟨hei, ?_⟩
  have hp (x : Ω) : ‖Complex.exp (X x)-1‖ ≤
      ‖X x‖^2/(2*δ)+(δ/2)*Real.exp (2*‖X x‖) := by
    apply (norm_exp_sub_one_le_mul_exp _).trans
    have hs := sq_nonneg (‖X x‖-δ*Real.exp ‖X x‖)
    have heq : Real.exp (2*‖X x‖) = (Real.exp ‖X x‖)^2 := by simpa using Real.exp_nat_mul ‖X x‖ 2
    rw [heq]
    have hrew : ‖X x‖^2/(2*δ)+(δ/2)*(Real.exp ‖X x‖)^2 =
        (‖X x‖^2+δ^2*(Real.exp ‖X x‖)^2)/(2*δ) := by field_simp; ring
    rw [hrew]
    apply (le_div_iff₀ (by positivity : 0<2*δ)).mpr
    nlinarith only [hs]
  have hmajor : Integrable (fun x => ‖X x‖^2/(2*δ)+(δ/2)*Real.exp (2*‖X x‖)) μ :=
    (hX2.div_const _).add (he2.const_mul _)
  calc
    _ = ‖∫ x, Complex.exp (X x)-1 ∂μ‖ := by rw [integral_sub hei (integrable_const 1)]; simp
    _ ≤ ∫ x, ‖Complex.exp (X x)-1‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖X x‖^2/(2*δ)+(δ/2)*Real.exp (2*‖X x‖) ∂μ :=
      integral_mono (hei.sub (integrable_const 1)).norm hmajor hp
    _ = _ := by rw [integral_add (hX2.div_const _) (he2.const_mul _),integral_div,integral_const_mul]

end BourgadeHuang
