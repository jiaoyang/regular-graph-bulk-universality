import Mathlib

/-! Conditional second moments suffice for the weighted degree-two loop response. -/
noncomputable section
open MeasureTheory Filter

namespace GeneralizedBulk.Analysis

theorem integrable_weighted_product_of_second_moments
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (P : Measure S) [SFinite P] (Q : Measure T) [SFinite Q]
    (A B : S → T → ℂ) (weight : S → ℂ) (U V : S → ℝ)
    (hmeas : AEStronglyMeasurable (fun z : S × T => weight z.1 * A z.1 z.2 * B z.1 z.2) (P.prod Q))
    (hA : ∀ᵐ x ∂P, Integrable (fun γ => ‖A x γ‖ ^ 2) Q)
    (hB : ∀ᵐ x ∂P, Integrable (fun γ => ‖B x γ‖ ^ 2) Q)
    (hU : ∀ᵐ x ∂P, (∫ γ, ‖A x γ‖ ^ 2 ∂Q) ≤ U x)
    (hV : ∀ᵐ x ∂P, (∫ γ, ‖B x γ‖ ^ 2 ∂Q) ≤ V x)
    (hweight : Integrable (fun x => ‖weight x‖ * (U x + V x) / 2) P) :
    Integrable (fun z : S × T => weight z.1 * A z.1 z.2 * B z.1 z.2) (P.prod Q) := by
  let F := fun z : S × T => weight z.1 * A z.1 z.2 * B z.1 z.2
  have hpoint (x : S) (γ : T) : ‖F (x, γ)‖ ≤
      (‖weight x‖ / 2) * (‖A x γ‖ ^ 2 + ‖B x γ‖ ^ 2) := by
    have hh : ‖A x γ‖ * ‖B x γ‖ ≤ (‖A x γ‖ ^ 2 + ‖B x γ‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖A x γ‖ - ‖B x γ‖)]
    dsimp [F]
    simp only [norm_mul]
    calc
      ‖weight x‖ * ‖A x γ‖ * ‖B x γ‖ = ‖weight x‖ * (‖A x γ‖ * ‖B x γ‖) := by ring
      _ ≤ ‖weight x‖ * ((‖A x γ‖ ^ 2 + ‖B x γ‖ ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hh (norm_nonneg (weight x))
      _ = _ := by ring
  have hsection : ∀ᵐ x ∂P, Integrable (fun γ => F (x, γ)) Q := by
    filter_upwards [hA, hB, hmeas.prodMk_left] with x hax hbx hmx
    exact ((hax.add hbx).const_mul (‖weight x‖ / 2)).mono' hmx
      (Filter.Eventually.of_forall (hpoint x))
  have hbound : ∀ᵐ x ∂P, (∫ γ, ‖F (x, γ)‖ ∂Q) ≤ ‖weight x‖ * (U x + V x) / 2 := by
    filter_upwards [hA, hB, hU, hV, hsection] with x hax hbx hux hvx hfx
    calc
      _ ≤ ∫ γ, (‖weight x‖ / 2) * (‖A x γ‖ ^ 2 + ‖B x γ‖ ^ 2) ∂Q :=
        integral_mono hfx.norm ((hax.add hbx).const_mul _) (hpoint x)
      _ = (‖weight x‖ / 2) * ((∫ γ, ‖A x γ‖ ^ 2 ∂Q) + ∫ γ, ‖B x γ‖ ^ 2 ∂Q) := by
        rw [integral_const_mul, integral_add hax hbx]
      _ ≤ (‖weight x‖ / 2) * (U x + V x) :=
        mul_le_mul_of_nonneg_left (add_le_add hux hvx) (by positivity)
      _ = _ := by ring
  apply (integrable_prod_iff hmeas).2
  refine ⟨hsection, ?_⟩
  apply hweight.mono' hmeas.norm.integral_prod_right'
  filter_upwards [hbound] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun γ => norm_nonneg _))]
  exact hx

end GeneralizedBulk.Analysis
