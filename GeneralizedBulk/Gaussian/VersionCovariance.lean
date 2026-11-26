import GeneralizedBulk.Gaussian.FieldVersion

/-! Wick covariance for the common analytic sample version of the L² series. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators

namespace GeneralizedBulk

theorem EntryWickCovariance.congr_ae
    {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p sigma : ℂ}
    {kernel : ι → ι → ℂ} {X Y : ι → Ω → EndpointMatrix}
    (h : EntryWickCovariance μ p sigma kernel X)
    (hXY : ∀ w i j, (fun ω => X w ω i j) =ᵐ[μ] (fun ω => Y w ω i j)) :
    EntryWickCovariance μ p sigma kernel Y := by
  constructor
  · intro w i j
    exact (h.integrable_entry w i j).congr (hXY w i j)
  · intro w i j
    rw [← integral_congr_ae (hXY w i j)]
    exact h.mean_zero w i j
  · intro w u i j a b
    exact (h.integrable_product w u i j a b).congr ((hXY w i j).mul (hXY u a b))
  · intro w u i j a b
    rw [← integral_congr_ae ((hXY w i j).mul (hXY u a b))]
    exact h.covariance w u i j a b

namespace Gaussian
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

def analyticMatrixSeries (s : AnchoredCountingState)
    (marks : s.val.1.ParticleLabels → Matrix (Fin 4) (Fin 4) (Lp ℂ 2 μ))
    (sigma : ℂ) (v : ℂ × Bool) (ω : Ω) : EndpointMatrix :=
  fun i j => if v.2 then analyticDerivativeEntry μ s (fun n => marks n i j) sigma v.1 ω
    else analyticL2Entry μ s (fun n => marks n i j) sigma v.1 ω

theorem analytic_slot_eq_L2_ae [IsFiniteMeasure μ]
    (s : AnchoredCountingState) (marks : s.val.1.ParticleLabels → Lp ℂ 2 μ)
    (sigma : ℂ) (B : ℝ)
    (horth : Pairwise fun i j => @inner ℂ (Lp ℂ 2 μ) _ (marks i) (marks j) = 0)
    (hB : 0 ≤ B) (hbound : ∀ i, ‖marks i‖ ^ 2 ≤ B)
    (hweight : ∀ᵐ ω ∂μ, Summable (fun i =>
      nevanlinnaWeight (s.val.1.particleLocation i) * ‖marks i ω‖)) (v : ℂ × Bool) :
    (fun ω => if v.2 then analyticDerivativeEntry μ s marks sigma v.1 ω
      else analyticL2Entry μ s marks sigma v.1 ω) =ᵐ[μ]
      (fun ω => l2Series μ marks (fun i => sigma * particleCoefficient
        (s.val.1.particleLocation i) v) ω) := by
  rcases v with ⟨w, tag⟩
  by_cases hw : w.im = 0
  · have hz : l2Series μ marks (fun i => sigma * particleCoefficient
        (s.val.1.particleLocation i) (w, tag)) = 0 := by
      simp [l2Series, particleCoefficient, hw]
    cases tag <;>
      simpa only [Bool.false_eq_true, ↓reduceIte, analyticL2Entry, analyticDerivativeEntry,
        anchoredMarkedEntry, hw, if_pos, hz] using (Lp.coeFn_zero ℂ 2 μ).symm
  · cases tag
    · exact analyticL2Entry_eq_ae μ s marks sigma B horth hB hbound hweight hw
    · exact analyticDerivativeEntry_eq_ae μ s marks sigma B horth hB hbound hweight hw

/-- A common analytic version inherits every covariance identity of the
constructed L² series. This is a proved version transfer, not a new Wick premise. -/
theorem entryWickCovariance_analyticMatrixSeries [IsFiniteMeasure μ]
    (s : AnchoredCountingState)
    (marks : s.val.1.ParticleLabels → Matrix (Fin 4) (Fin 4) (Lp ℂ 2 μ))
    (p sigma : ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hbound : ∀ n i j, ‖marks n i j‖ ^ 2 ≤ B)
    (horth : ∀ i j, Pairwise fun n m => @inner ℂ (Lp ℂ 2 μ) _ (marks n i j) (marks m i j) = 0)
    (hmean : ∀ n i j, (∫ ω, marks n i j ω ∂μ) = 0)
    (hoff : ∀ n m, n ≠ m → ∀ i j a b,
      (∫ ω, marks n i j ω * marks m a b ω ∂μ) = 0)
    (hdiag : ∀ n i j a b,
      (∫ ω, marks n i j ω * marks n a b ω ∂μ) =
        covarianceMatrix p i a * covarianceMatrix p j b +
          covarianceMatrix p i b * covarianceMatrix p j a)
    (hweight : ∀ i j, ∀ᵐ ω ∂μ, Summable (fun n =>
      nevanlinnaWeight (s.val.1.particleLocation n) * ‖marks n i j ω‖)) :
    EntryWickCovariance μ p sigma (particleKernel s)
      (analyticMatrixSeries μ s marks sigma) := by
  have hL2 := entryWickCovariance_particleSeries μ s marks p sigma B hB hbound horth hmean hoff hdiag
  apply hL2.congr_ae
  intro v i j
  exact (analytic_slot_eq_L2_ae μ s (fun n => marks n i j) sigma B (horth i j) hB
    (fun n => hbound n i j) (hweight i j) v).symm

end Gaussian
end GeneralizedBulk
