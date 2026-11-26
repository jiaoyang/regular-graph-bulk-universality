import GeneralizedBulk.Graph.WindowGaussianFactorization
import GeneralizedBulk.Graph.HYDeterministicPadding

/-! Actual HY quantiles discharge the padding hypotheses in window BS factorization. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.KestenMcKay
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def windowPaddingTolerance {P : Measure Ω} [IsProbabilityMeasure P] (hd : 3 ≤ (d : ℝ))
    (H : HYCoarseInput D P (D.kestenMcKayQuantile hd)) (E sigma R : ℝ) (m n : ℕ) : ℝ :=
  max (D.bulkPaddingError hd H E m n) (microscopicStep (N n) sigma * R)

theorem windowPaddingTolerance_tendsto {P : Measure Ω} [IsProbabilityMeasure P] (hd : 3 ≤ (d : ℝ))
    (H : HYCoarseInput D P (D.kestenMcKayQuantile hd)) (E sigma R : ℝ)
    (hE : E ∈ Set.Ioo (-radius d) (radius d)) (m : ℕ) :
    Tendsto (fun n => D.windowPaddingTolerance hd H E sigma R m n) atTop (𝓝 0) := by
  have hsmall := (microscopicStep_tendsto_zero N D.size_tendsto sigma).mul_const R
  simpa only [windowPaddingTolerance,mul_zero,zero_mul,max_self] using
    (D.bulkPaddingError_tendsto hd H E hE m).max hsmall

/-- The padding list is fully constructed from actual Kesten--McKay
quantiles and the literal external HY rigidity estimate. The remaining
fourth-moment hypothesis is the numerical entropy estimate's output. -/
theorem BS_window_count_factorization_of_HY_padding {m : ℕ} (hm : 0 < m) [Nonempty Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : Set ℝ) (BS : BSQualitativeInput D P K)
    (hd : 3 ≤ (d : ℝ)) (HY : HYCoarseInput D P (D.kestenMcKayQuantile hd))
    (E sigma R : ℝ) (hsigma : 0 < sigma) (hE : E ∈ K) (hEd : E ≠ (d : ℝ))
    (hEbulk : E ∈ Set.Ioo (-radius d) (radius d))
    (good : ℕ → Set Ω) (hgood : ∀ n, MeasurableSet (good n))
    (hbad : Tendsto (fun n => (P (good n)ᶜ).toReal) atTop (𝓝 0))
    (hBS : ∀ᶠ n in atTop, good n ⊆ BS.good m n)
    (hHY : ∀ᶠ n in atTop, good n ⊆ HY.events.good n)
    (hfourth : ∀ᶠ n in atTop, ∀ ω ∈ good n, ∀ k : Fin (N n),
      k ≠ ⟨0,D.size_pos n⟩ →
      |D.eigenvalue n ω k - E| ≤ D.windowPaddingTolerance hd HY E sigma R m n → ∀ j : Fin (d + 1),
      |D.empiricalFourthWickDiscrepancy n ω (fun _ : Fin 1 => k) (0,j) (0,j) (0,j) (0,j)| ≤ 1)
    (leaf : Fin d) (F : BoundedContinuousFunction ((Fin m × Fin 4) → ℝ) ℝ)
    (H : ℕ → Ω → ℂ) (hH : ∀ n, Measurable (H n)) (C : ℝ) (hC : ∀ n ω, ‖H n ω‖ ≤ C) :
    Tendsto (fun n => (∫ ω, D.windowCountWeight n E sigma R m (H n) ω *
      (↑(∫ x, F x ∂D.twoEdgeLaw n ω
        (D.paddedWindowSelection n ω E sigma (-R) R (fun _ => D.bulkPaddingIndex E m n)) leaf) : ℂ) ∂P) -
      (∫ ω, D.windowCountWeight n E sigma R m (H n) ω ∂P) *
        (↑(∫ x, F x ∂Gaussian.finiteMarkLaw (E / d) m) : ℂ)) atTop (𝓝 0) := by
  apply D.BS_window_count_factorization hm P K BS E sigma R hsigma hE hEd
    (D.windowPaddingTolerance hd HY E sigma R m)
    (D.windowPaddingTolerance_tendsto hd HY E sigma R hEbulk m)
    (Eventually.of_forall (fun n => le_max_right _ _)) good hgood hbad hBS
    (fun n _ => D.bulkPaddingIndex E m n)
    (fun n j => D.measurable_bulkPaddingIndex E m n j) _ hfourth leaf F H hH C hC
  filter_upwards [hHY,D.HY_bulkPaddingIndex_eventually hd HY E hEbulk m] with n hhy hp
  intro ω hω
  have h := hp ω (hhy hω)
  exact ⟨h.1,h.2.1,fun j => (h.2.2 j).trans (le_max_left _ _)⟩

end GeneralizedBulk.External.RegularSpectralData
