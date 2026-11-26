import GeneralizedBulk.Entropy.FiniteMixture

/-! Actual differential-entropy bounds for arbitrary finite mixtures of densities. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Analysis
open GeneralizedBulk.Entropy
variable {X S : Type*} [MeasurableSpace X] [Fintype S]

theorem integral_negMulLog_mixture_bounds (μ : Measure X)
    (weight : S → ℝ) (f : S → X → ℝ) (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1)
    (hfp : ∀ s x, 0 ≤ f s x) (hfi : ∀ s, Integrable (f s) μ)
    (hfnorm : ∀ s, ∫ x, f s x ∂μ = 1)
    (hflog : ∀ s, Integrable (fun x => Real.negMulLog (f s x)) μ)
    (hmix : Integrable (fun x => Real.negMulLog (∑ s, weight s * f s x)) μ) :
    (∑ s, weight s * ∫ x, Real.negMulLog (f s x) ∂μ) ≤
      (∫ x, Real.negMulLog (∑ s, weight s * f s x) ∂μ) ∧
    (∫ x, Real.negMulLog (∑ s, weight s * f s x) ∂μ) ≤
      Finite.entropy weight + ∑ s, weight s * ∫ x, Real.negMulLog (f s x) ∂μ := by
  have hlower (x : X) : (∑ s, weight s * Real.negMulLog (f s x)) ≤
      Real.negMulLog (∑ s, weight s * f s x) := by
    simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.le_map_sum
      (t := Finset.univ) (w := weight) (p := fun s => f s x)
      (fun s _ => hw s) hnorm (fun s _ => hfp s x)
  have hupper (x : X) : Real.negMulLog (∑ s, weight s * f s x) ≤
      ∑ s, (f s x * Real.negMulLog (weight s) + weight s * Real.negMulLog (f s x)) := by
    have h := Finite.entropy_lower_total (fun s => weight s * f s x)
      (fun s => mul_nonneg (hw s) (hfp s x))
    simpa only [Finite.entropy, Real.negMulLog_mul] using h
  have hlInt := integrable_finset_sum Finset.univ (fun s _ => (hflog s).const_mul (weight s))
  have huInt := integrable_finset_sum Finset.univ (fun s _ =>
    ((hfi s).mul_const (Real.negMulLog (weight s))).add ((hflog s).const_mul (weight s)))
  have hl := integral_mono hlInt hmix hlower
  have hu := integral_mono hmix huInt hupper
  rw [integral_finset_sum _ (fun s _ => (hflog s).const_mul (weight s))] at hl
  simp only [integral_const_mul] at hl
  refine ⟨hl, ?_⟩
  rw [integral_finset_sum _ (fun s _ =>
    ((hfi s).mul_const (Real.negMulLog (weight s))).add ((hflog s).const_mul (weight s)))] at hu
  have he (s : S) : (∫ x, f s x * Real.negMulLog (weight s) + weight s * Real.negMulLog (f s x) ∂μ) =
      Real.negMulLog (weight s) + weight s * ∫ x, Real.negMulLog (f s x) ∂μ := by
    calc
      _ = (∫ x, f s x * Real.negMulLog (weight s) ∂μ) +
          ∫ x, weight s * Real.negMulLog (f s x) ∂μ :=
        integral_add ((hfi s).mul_const _) ((hflog s).const_mul _)
      _ = _ := by rw [integral_mul_const, integral_const_mul, hfnorm, one_mul]
  change (∫ x, Real.negMulLog (∑ s, weight s * f s x) ∂μ) ≤
    ∑ s, ∫ x, f s x * Real.negMulLog (weight s) + weight s * Real.negMulLog (f s x) ∂μ at hu
  simp_rw [he] at hu
  simpa only [Finite.entropy, Finset.sum_add_distrib] using hu

end GeneralizedBulk.Analysis
