import GeneralizedBulk.Entropy.MehlerChaosExpansion

/-! The actual finite-signal Mehler density has the uniform fourth-chaos
lower bound required by the entropy argument. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy.Hermite GeneralizedBulk.Entropy.Mehler

/-- Uniform actual Mehler coercivity with all spectral/Hilbert inputs proved.
The scale, finite signal, and true L² density can vary independently. -/
theorem uniform_actual_Mehler_fourth_lower {S : Type*} [Fintype S]
    (d k : ℕ) (hd : 3 ≤ d) (K : Set (StarParameters k)) (hK : IsCompact K)
    (hbulk : ∀ c ∈ K, ∀ a, (c.val a) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ c ∈ K,
      ∀ (weight : S → ℝ) (signal : S → ScalarCoordinate d k → ℝ),
      (∑ s, weight s = 1) → ∀ a : ℝ, 0 < 1 - a ^ 2 →
      ∀ f : Lp ℝ 2 (standardGaussian (ScalarCoordinate d k)),
      ((f : (ScalarCoordinate d k → ℝ) → ℝ) =ᵐ[standardGaussian (ScalarCoordinate d k)]
        fun z => finiteMixtureKernel weight signal a z - 1) →
      (coloredGaussianFrameSystem d k (by omega) c.val c.property).Admissible f →
      kappa * a ^ 8 * ‖signalChaos weight signal 4‖ ^ 2 ≤
        (coloredGaussianFrameSystem d k (by omega) c.val c.property).defect f := by
  obtain ⟨κ, hκ, hfull⟩ := uniform_actual_defect_fourth_lower d k hd K hK hbulk
  refine ⟨κ, hκ, ?_⟩
  intro c hc weight signal hnorm a ha f hf hadm
  have hcenter := centered_density_integral_zero weight signal hnorm a ha f hf
  have hh := hfull c hc f hadm hcenter
  have hcomp := chaosComponent_centered_density weight signal a ha f hf 4 (by decide)
  have hnorm : ‖chaosComponent (ScalarCoordinate d k) f 4‖ ^ 2 =
      a ^ 8 * ‖signalChaos weight signal 4‖ ^ 2 := by
    change ‖(chaosComponent (ScalarCoordinate d k) f 4 : Lp ℝ 2 (standardGaussian (ScalarCoordinate d k)))‖ ^ 2 = _
    rw [hcomp, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← pow_mul]
    rfl
  rw [hnorm] at hh
  exact (show κ * a ^ 8 * ‖signalChaos weight signal 4‖ ^ 2 =
    κ * (a ^ 8 * ‖signalChaos weight signal 4‖ ^ 2) by ring).trans_le hh

end GeneralizedBulk.Entropy.Channel
