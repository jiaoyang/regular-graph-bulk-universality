import BourgadeHuang.FiniteSourceBounds

/-! Moment bounds for finite sums without independence assumptions. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Filter
namespace BourgadeHuang

theorem finite_sum_second_moment_bound {Ω : Type*} [MeasurableSpace Ω] {q : ℕ}
    (μ : Measure Ω) (X : Fin q → Ω → ℂ) (hm : ∀j, Measurable (X j))
    (hi : ∀j, Integrable (fun s => ‖X j s‖^2) μ) (C : ℝ)
    (hb : ∀j, (∫ s, ‖X j s‖^2 ∂μ)≤C) :
    Integrable (fun s => ‖∑ j, X j s‖^2) μ ∧
      (∫ s, ‖∑ j, X j s‖^2 ∂μ)≤(q:ℝ)^2*C := by
  have hmeas : Measurable (fun s => ‖∑ j, X j s‖^2) :=
    (Finset.measurable_sum Finset.univ (fun j _ => hm j)).norm.pow_const 2
  have hdom : Integrable (fun s => (q:ℝ)*∑ j, ‖X j s‖^2) μ :=
    (integrable_finset_sum Finset.univ (fun j _ => hi j)).const_mul _
  have hpoint s := norm_sum_sq_le_card_sum_sq (fun j => X j s)
  have hXi : Integrable (fun s => ‖∑ j, X j s‖^2) μ :=
    hdom.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hpoint s)
  refine ⟨hXi, ?_⟩
  calc
    _ ≤ ∫ s, (q:ℝ)*∑ j, ‖X j s‖^2 ∂μ := integral_mono hXi hdom hpoint
    _ = (q:ℝ)*∑ j, ∫ s, ‖X j s‖^2 ∂μ := by
      rw [integral_const_mul,integral_finset_sum _ (fun j _ => hi j)]
    _ ≤ (q:ℝ)*∑ _j : Fin q, C := by gcongr with j; exact hb j
    _ = _ := by simp; ring

theorem finite_sum_exp_moment_bound {Ω : Type*} [MeasurableSpace Ω] {q : ℕ} (hq : 0<q)
    (μ : Measure Ω) (X : Fin q → Ω → ℂ) (hm : ∀j, Measurable (X j))
    {L : ℝ} (hL : 0≤L) (hi : ∀j, Integrable (fun s => Real.exp (L*(q:ℝ)*‖X j s‖)) μ)
    (C : ℝ) (hb : ∀j, (∫ s, Real.exp (L*(q:ℝ)*‖X j s‖) ∂μ)≤C) :
    Integrable (fun s => Real.exp (L*‖∑ j, X j s‖)) μ ∧
      (∫ s, Real.exp (L*‖∑ j, X j s‖) ∂μ)≤(q:ℝ)*C := by
  have hmeas : Measurable (fun s => Real.exp (L*‖∑ j, X j s‖)) :=
    ((Finset.measurable_sum Finset.univ (fun j _ => hm j)).norm.const_mul L).exp
  have hdom := integrable_finset_sum Finset.univ (fun j _ => hi j)
  have hpoint s := exp_norm_sum_le_sum_exp hq (fun j => X j s) hL
  have hXi : Integrable (fun s => Real.exp (L*‖∑ j, X j s‖)) μ :=
    hdom.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact hpoint s)
  refine ⟨hXi, ?_⟩
  calc
    _ ≤ ∫ s, ∑ j, Real.exp (L*(q:ℝ)*‖X j s‖) ∂μ := integral_mono hXi hdom hpoint
    _ = ∑ j, ∫ s, Real.exp (L*(q:ℝ)*‖X j s‖) ∂μ := integral_finset_sum _ (fun j _ => hi j)
    _ ≤ ∑ _j : Fin q, C := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp

/-- Identity or complex conjugation, indexed by the desired half-plane. -/
def reflectComplex (upper : Bool) (z : ℂ) : ℂ := if upper then z else starRingEnd ℂ z

@[simp] theorem norm_reflectComplex (upper : Bool) (z : ℂ) :
    ‖reflectComplex upper z‖ = ‖z‖ := by cases upper <;> simp [reflectComplex]

theorem continuous_reflectComplex (upper : Bool) : Continuous (reflectComplex upper) := by
  cases upper
  · exact Complex.continuous_conj
  · exact continuous_id

end BourgadeHuang
