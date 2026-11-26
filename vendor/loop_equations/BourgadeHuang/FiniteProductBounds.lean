import BourgadeHuang.FiniteObservableBounds

/-! Finite product moment estimates requiring no independence. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Filter
namespace BourgadeHuang

theorem prod_le_sum_pow_card {q : ℕ} (hq : 0<q) (f : Fin q → ℝ) (hf : ∀j, 0≤f j) :
    (∏j, f j)≤∑j, (f j)^q := by
  have hne : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0,hq⟩,Finset.mem_univ _⟩
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image Finset.univ f hne
  calc
    _ ≤ ∏_j : Fin q, f k := Finset.prod_le_prod (fun j _ => hf j) hmax
    _ = (f k)^q := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun j => (f j)^q) (fun j _ => pow_nonneg (hf j) _) hk

theorem finite_product_integral_bound {Ω : Type*} [MeasurableSpace Ω] {q : ℕ}
    (hq : 0<q) (μ : Measure Ω) (f : Fin q → Ω → ℝ)
    (hm : ∀j, Measurable (f j)) (hf : ∀j s, 0≤f j s)
    (hi : ∀j, Integrable (fun s => (f j s)^q) μ) (C : ℝ)
    (hb : ∀j, (∫s, (f j s)^q ∂μ)≤C) :
    Integrable (fun s => ∏j, f j s) μ ∧ (∫s, ∏j, f j s ∂μ)≤(q:ℝ)*C := by
  have hdom := integrable_finset_sum Finset.univ (fun j _ => hi j)
  have hpoint s := prod_le_sum_pow_card hq (fun j => f j s) (fun j => hf j s)
  have hpi : Integrable (fun s => ∏j, f j s) μ := by
    apply hdom.mono' (Finset.measurable_prod _ (fun j _ => hm j)).aestronglyMeasurable
    filter_upwards [] with s
    rw [Real.norm_eq_abs,abs_of_nonneg (Finset.prod_nonneg (fun j _ => hf j s))]
    exact hpoint s
  refine ⟨hpi, ?_⟩
  calc
    _ ≤ ∫s, ∑j, (f j s)^q ∂μ := integral_mono hpi hdom hpoint
    _ = ∑j, ∫s, (f j s)^q ∂μ := integral_finset_sum _ (fun j _ => hi j)
    _ ≤ ∑_j : Fin q, C := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp

end BourgadeHuang
