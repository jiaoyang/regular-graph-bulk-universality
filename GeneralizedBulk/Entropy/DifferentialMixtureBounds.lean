import GeneralizedBulk.Analysis.MixtureDensityEntropy
import GeneralizedBulk.Entropy.GaussianMixtureEntropy

/-! Differential-entropy mixture bounds with actual Lebesgue integrals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Analysis
variable {I S : Type*} [Fintype I] [Fintype S]

theorem integral_negMulLog_eq_differentialEntropy (f : (I → ℝ) → ℝ) :
    (∫ x, Real.negMulLog (f x)) = differentialEntropy f := by
  simp only [Real.negMulLog, neg_mul, integral_neg, differentialEntropy]

theorem differentialEntropy_finite_mixture_bounds
    (weight : S → ℝ) (f : S → (I → ℝ) → ℝ) (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1)
    (hfp : ∀ s x, 0 ≤ f s x) (hfi : ∀ s, Integrable (f s)) (hfnorm : ∀ s, ∫ x, f s x = 1)
    (hflog : ∀ s, Integrable (fun x => f s x * Real.log (f s x)))
    (hmix : Integrable (fun x => (∑ s, weight s * f s x) * Real.log (∑ s, weight s * f s x))) :
    (∑ s, weight s * differentialEntropy (f s)) ≤ differentialEntropy (fun x => ∑ s, weight s * f s x) ∧
    differentialEntropy (fun x => ∑ s, weight s * f s x) ≤
      Finite.entropy weight + ∑ s, weight s * differentialEntropy (f s) := by
  have h := integral_negMulLog_mixture_bounds volume weight f hw hnorm hfp hfi hfnorm
    (fun s => by simpa only [Real.negMulLog, neg_mul] using (hflog s).neg)
    (by simpa only [Real.negMulLog, neg_mul] using hmix.neg)
  simp_rw [integral_negMulLog_eq_differentialEntropy] at h
  exact h

end GeneralizedBulk.Entropy
