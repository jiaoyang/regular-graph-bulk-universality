import Mathlib

/-! Finite mixtures of actual measures and their density functions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace GeneralizedBulk.Analysis
variable {S X : Type*} [Fintype S] [MeasurableSpace X]

theorem withDensity_finite_sum (μ : Measure X) (f : S → X → ℝ≥0∞)
    (hf : ∀ s, Measurable (f s)) :
    μ.withDensity (fun x => ∑ s, f s x) = ∑ s, μ.withDensity (f s) := by
  classical
  have hsum (t : Finset S) : μ.withDensity (fun x => ∑ s ∈ t, f s x) =
      ∑ s ∈ t, μ.withDensity (f s) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert s t hs ih =>
      simp only [Finset.sum_insert hs]
      rw [show (fun x => f s x + ∑ j ∈ t, f j x) = f s + fun x => ∑ j ∈ t, f j x from rfl,
        withDensity_add_left (hf s), ih]
  exact hsum Finset.univ

theorem withDensity_finite_mixture (μ : Measure X) (weight : S → ℝ)
    (f : S → X → ℝ) (hweight : ∀ s, 0 ≤ weight s) (hf : ∀ s, Measurable (f s))
    (hpos : ∀ s x, 0 ≤ f s x) :
    μ.withDensity (fun x => ENNReal.ofReal (∑ s, weight s * f s x)) =
      ∑ s, ENNReal.ofReal (weight s) • μ.withDensity (fun x => ENNReal.ofReal (f s x)) := by
  have he : (fun x => ENNReal.ofReal (∑ s, weight s * f s x)) =
      fun x => ∑ s, ENNReal.ofReal (weight s) * ENNReal.ofReal (f s x) := by
    funext x
    rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => mul_nonneg (hweight s) (hpos s x))]
    simp_rw [ENNReal.ofReal_mul (hweight _)]
  rw [he, withDensity_finite_sum μ _ (fun s => measurable_const.mul (hf s).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro s hs
  exact withDensity_smul _ (hf s).ennreal_ofReal

end GeneralizedBulk.Analysis
