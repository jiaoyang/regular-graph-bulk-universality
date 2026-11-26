import Mathlib

/-!
# From a joint L² limit to conditional limits

A single measurable joint representative at the anchor can be used for every
scalar state. A deterministic subsequence has vanishing conditional L² errors
on one full-measure set; no measurable choice of Lp representatives by state
is postulated.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GeneralizedBulk.Analysis

theorem exists_subsequence_conditional_error_zero
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (P : Measure S) [SFinite P] (Q : Measure T) [SFinite Q]
    (F : ℕ → S → T → ℂ) (limit : S → T → ℂ)
    (herror : ∀ n, Integrable (fun z : S × T => ‖F n z.1 z.2 - limit z.1 z.2‖ ^ 2) (P.prod Q))
    (hzero : Tendsto (fun n => ∫ z : S × T, ‖F n z.1 z.2 - limit z.1 z.2‖ ^ 2 ∂P.prod Q)
      atTop (𝓝 0)) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∀ᵐ x ∂P,
      Tendsto (fun n => ∫ γ, ‖F (r n) x γ - limit x γ‖ ^ 2 ∂Q) atTop (𝓝 0) := by
  let G : ℕ → S → ℝ := fun n x => ∫ γ, ‖F n x γ - limit x γ‖ ^ 2 ∂Q
  have hG (n : ℕ) : Integrable (G n) P := (herror n).integral_prod_left
  let Z : ℕ → Lp ℝ 1 P := fun n => (hG n).toL1 (G n)
  have hnorm (n : ℕ) : ‖Z n‖ =
      ∫ z : S × T, ‖F n z.1 z.2 - limit z.1 z.2‖ ^ 2 ∂P.prod Q := by
    rw [L1.norm_of_fun_eq_integral_norm]
    rw [integral_prod _ (herror n)]
    apply integral_congr_ae
    filter_upwards [] with x
    exact Real.norm_of_nonneg (integral_nonneg (fun γ => sq_nonneg _))
  have hZ : Tendsto Z atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [hnorm] using hzero
  have hm := tendstoInMeasure_of_tendsto_Lp hZ
  have hm' : TendstoInMeasure P G atTop (fun _ => (0 : ℝ)) := by
    apply hm.congr
    · intro n
      exact (hG n).coeFn_toL1
    · exact Lp.coeFn_zero _ _ _
  exact hm'.exists_seq_tendsto_ae

end GeneralizedBulk.Analysis
