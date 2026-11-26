import BourgadeHuang.BulkCompactSources
import BourgadeHuang.FiniteObservableBounds

/-! Jensen--Fubini estimates for genuine integrated edge sources.
The centering is left as an actual function of the parameter, so these lemmas
apply to `s(w)-sqrt(w)` without replacing it by the constant bulk center. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

section Compact
variable {T Ω : Type*} [TopologicalSpace T] [TopologicalSpace.MetrizableSpace T]
  [SecondCountableTopology T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T]
  [MeasurableSpace Ω]

/-- Actual compactly integrated complex source. -/
def integratedSource (κ : Measure T) (X : T → Ω → ℂ) (s : Ω) : ℂ :=
  ∫ t, X t s ∂κ

theorem measurable_integratedSource
    (κ : Measure T) [SFinite κ] (X : T → Ω → ℂ)
    (hc : ∀ s, Continuous (fun t => X t s)) (hm : ∀ t, Measurable (X t)) :
    Measurable (integratedSource κ X) :=
  (measurable_uncurry_of_continuous_of_measurable hc hm).stronglyMeasurable.integral_prod_left.measurable

/-- A uniform exponential moment bound survives genuine integration over a
compact parameter space. -/
theorem integratedSource_exp_bound
    (κ : Measure T) [IsProbabilityMeasure κ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : T → Ω → ℂ) (hc : ∀ s, Continuous (fun t => X t s)) (hm : ∀ t, Measurable (X t))
    {L C : ℝ} (hL : 0 ≤ L)
    (hi : ∀ t, Integrable (fun s => Real.exp (L*‖X t s‖)) ν)
    (hb : ∀ t, (∫ s, Real.exp (L*‖X t s‖) ∂ν) ≤ C) :
    Integrable (fun s => Real.exp (L*‖integratedSource κ X s‖)) ν ∧
      (∫ s, Real.exp (L*‖integratedSource κ X s‖) ∂ν) ≤ C := by
  let G := fun t s => Real.exp (L*‖X t s‖)
  have hXm : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  have hGm : StronglyMeasurable (Function.uncurry G) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul hXm.norm)).stronglyMeasurable
  have hGp : Integrable (Function.uncurry G) (κ.prod ν) :=
    integrable_prod_of_uniform_fiber_norm κ ν hGm hi C (fun t => by
      simpa only [G, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb t)
  have hJ (s : Ω) : Real.exp (L*‖integratedSource κ X s‖) ≤ ∫ t, G t s ∂κ := by
    have hi₁ : Integrable (fun t => L*‖X t s‖) κ :=
      (continuous_const.mul (hc s).norm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi₂ : Integrable (fun t => G t s) κ :=
      (Real.continuous_exp.comp (continuous_const.mul (hc s).norm)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc
      _ ≤ Real.exp (∫ t, L*‖X t s‖ ∂κ) := by
        apply Real.exp_le_exp.mpr
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hL
      _ ≤ _ := exp_integral_le_integral_exp κ hi₁ hi₂
  have ht : Integrable (fun s => Real.exp (L*‖integratedSource κ X s‖)) ν := by
    apply hGp.integral_prod_right.mono'
      (Real.continuous_exp.measurable.comp (measurable_const.mul
        (measurable_integratedSource κ X hc hm).norm)).aestronglyMeasurable
    exact Eventually.of_forall (fun s => by
      dsimp only [Function.comp_apply,Function.uncurry_apply_pair]
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hJ s)
  refine ⟨ht, ?_⟩
  calc
    _ ≤ ∫ s, ∫ t, G t s ∂κ ∂ν := integral_mono ht hGp.integral_prod_right hJ
    _ = ∫ t, ∫ s, G t s ∂ν ∂κ := (integral_integral_swap hGp).symm
    _ ≤ ∫ _ : T, C ∂κ := integral_mono hGp.integral_prod_left (integrable_const _) hb
    _ = C := by simp

/-- A uniform quadratic moment bound also survives parameter integration. -/
theorem integratedSource_second_moment
    (κ : Measure T) [IsProbabilityMeasure κ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : T → Ω → ℂ) (hc : ∀ s, Continuous (fun t => X t s)) (hm : ∀ t, Measurable (X t))
    (C : ℝ) (hi : ∀ t, Integrable (fun s => ‖X t s‖^2) ν)
    (hb : ∀ t, (∫ s, ‖X t s‖^2 ∂ν) ≤ C) :
    Integrable (fun s => ‖integratedSource κ X s‖^2) ν ∧
      (∫ s, ‖integratedSource κ X s‖^2 ∂ν) ≤ C := by
  let G := fun t s => ‖X t s‖^2
  have hXm : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  have hGm : StronglyMeasurable (Function.uncurry G) := (hXm.norm.pow_const 2).stronglyMeasurable
  have hGp : Integrable (Function.uncurry G) (κ.prod ν) :=
    integrable_prod_of_uniform_fiber_norm κ ν hGm hi C (fun t => by
      simpa only [G, Real.norm_eq_abs, abs_pow, abs_norm] using hb t)
  have hJ (s : Ω) : ‖integratedSource κ X s‖^2 ≤ ∫ t, G t s ∂κ := by
    have hi₁ : Integrable (fun t => ‖X t s‖) κ :=
      (hc s).norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi₂ : Integrable (fun t => ‖X t s‖^2) κ :=
      ((hc s).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hcs := integral_le_sqrt_integral_sq κ hi₁ hi₂ (fun t => norm_nonneg _)
    have hn := (norm_integral_le_integral_norm (μ := κ) (fun t => X t s)).trans hcs
    have ht := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hn
    rw [Real.sq_sqrt (integral_nonneg (fun t => sq_nonneg _))] at ht
    exact ht
  have ht : Integrable (fun s => ‖integratedSource κ X s‖^2) ν := by
    apply hGp.integral_prod_right.mono'
      ((measurable_integratedSource κ X hc hm).norm.pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs, abs_pow, abs_norm]
      exact hJ s)
  refine ⟨ht, ?_⟩
  calc
    _ ≤ ∫ s, ∫ t, G t s ∂κ ∂ν := integral_mono ht hGp.integral_prod_right hJ
    _ = ∫ t, ∫ s, G t s ∂ν ∂κ := (integral_integral_swap hGp).symm
    _ ≤ ∫ _ : T, C ∂κ := integral_mono hGp.integral_prod_left (integrable_const _) hb
    _ = C := by simp

/-- A finite family of small integrated sources has an exponentially tilted
expectation close to one, with an explicit error tending to zero. -/
theorem finite_integratedSource_exponential_close
    (κ : Measure T) [IsProbabilityMeasure κ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {d : ℕ} (hd : 0<d) (X : Fin d → T → Ω → ℂ)
    (hc : ∀ j s, Continuous (fun t => X j t s)) (hm : ∀ j t, Measurable (X j t))
    {δ C E : ℝ} (hδ : 0<δ)
    (h2i : ∀ j t, Integrable (fun s => ‖X j t s‖^2) ν)
    (h2b : ∀ j t, (∫ s, ‖X j t s‖^2 ∂ν) ≤ C*δ^2)
    (hEi : ∀ j t, Integrable (fun s => Real.exp (2*(d:ℝ)*‖X j t s‖)) ν)
    (hEb : ∀ j t, (∫ s, Real.exp (2*(d:ℝ)*‖X j t s‖) ∂ν) ≤ E) :
    Integrable (fun s => Complex.exp (∑ j, integratedSource κ (X j) s)) ν ∧
      ‖(∫ s, Complex.exp (∑ j, integratedSource κ (X j) s) ∂ν)-1‖ ≤
        δ*((d:ℝ)^2*C/2+(d:ℝ)*E/2) := by
  let Y := fun j => integratedSource κ (X j)
  have hYm j : Measurable (Y j) := measurable_integratedSource κ (X j) (hc j) (hm j)
  have h2 j := integratedSource_second_moment κ ν (X j) (hc j) (hm j) _ (h2i j) (h2b j)
  obtain ⟨hY2i,hY2b⟩ := finite_sum_second_moment_bound ν Y hYm
    (fun j => (h2 j).1) (C*δ^2) (fun j => (h2 j).2)
  have hE j := integratedSource_exp_bound κ ν (X j) (hc j) (hm j)
    (by positivity : 0≤2*(d:ℝ)) (hEi j) (hEb j)
  obtain ⟨hYEi,hYEb⟩ := finite_sum_exp_moment_bound hd ν Y hYm
    (by norm_num : (0:ℝ)≤2) (fun j => (hE j).1) E (fun j => (hE j).2)
  obtain ⟨hi,hb⟩ := exponential_expectation_close_of_second_moment ν
    (fun s => ∑ j, Y j s) (Finset.measurable_sum _ (fun j _ => hYm j)) hY2i hYEi hδ
  refine ⟨hi, hb.trans ?_⟩
  calc
    _ ≤ ((d:ℝ)^2*(C*δ^2))/(2*δ)+(δ/2)*((d:ℝ)*E) :=
      add_le_add (div_le_div_of_nonneg_right hY2b (by positivity))
        (mul_le_mul_of_nonneg_left hYEb (by positivity))
    _ = _ := by field_simp; ring
end Compact
end BourgadeHuang.RationalEdge
