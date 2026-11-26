import GeneralizedBulk.Entropy.ConstructedQuarticEstimate

/-! Exact finite signal Hermite tests are bounded by the proved actual
Gaussian chaos norm. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.Hermite
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

theorem signalChaos_inner_multiLp (weight : S → ℝ) (signal : S → I → ℝ)
    (degree : ℕ) (α : I → ℕ) (hα : ∑ i, α i = degree) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (signalChaos weight signal degree)
      (multiLp I α) = signalHermiteMoment weight signal α := by
  have hh := fullChaosMap_inner_basis I degree
    (fun β => signalHermiteMoment weight signal (degreeIndexNat I β) / multiFactorial I (degreeIndexNat I β))
    (degreeIndexOf I degree α hα)
  rw [degreeIndexNat_of, div_mul_cancel₀ _ (ne_of_gt (multiFactorial_pos I α))] at hh
  exact hh

/-- Exact identification of the finite signal's homogeneous Hermite test
with a genuine Gaussian L² pairing. -/
theorem signalChaos_inner_chaosLp {J : Type*} [Fintype J]
    (weight : S → ℝ) (signal : S → I → ℝ) (degree : ℕ)
    (a : J → I → ℕ) (coeff : J → ℝ) (ha : ∀ j, ∑ i, a j i = degree) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (signalChaos weight signal degree) (chaosLp a coeff) =
      ∑ s, weight s * chaosFunction a coeff (signal s) := by
  simp only [chaosLp, inner_sum, inner_smul_right, signalChaos_inner_multiLp weight signal degree _ (ha _)]
  unfold signalHermiteMoment chaosFunction
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The actual fourth-chaos norm controls any actual homogeneous quartic
Hermite test of the finite signal. -/
theorem signal_chaos_test_bound {J : Type*} [Fintype J]
    (weight : S → ℝ) (signal : S → I → ℝ) (degree : ℕ)
    (a : J → I → ℕ) (coeff : J → ℝ) (ha : ∀ j, ∑ i, a j i = degree) :
    |∑ s, weight s * chaosFunction a coeff (signal s)| ≤
      ‖signalChaos weight signal degree‖ * ‖chaosLp a coeff‖ := by
  rw [← signalChaos_inner_chaosLp weight signal degree a coeff ha]
  exact abs_real_inner_le_norm _ _

/-- In particular every actual Hermite coefficient has the true factorial
normalization, so coordinate fourth cumulants are directly controlled. -/
theorem signalHermiteMoment_bound (weight : S → ℝ) (signal : S → I → ℝ)
    (degree : ℕ) (α : I → ℕ) (hα : ∑ i, α i = degree) :
    |signalHermiteMoment weight signal α| ≤
      ‖signalChaos weight signal degree‖ * Real.sqrt (multiFactorial I α) := by
  rw [← signalChaos_inner_multiLp weight signal degree α hα]
  have hn : ‖multiLp I α‖ = Real.sqrt (multiFactorial I α) := by
    rw [← multiLp_norm_sq I α, Real.sqrt_sq (norm_nonneg _)]
  rw [← hn]
  exact abs_real_inner_le_norm _ _

end GeneralizedBulk.Entropy.Mehler
