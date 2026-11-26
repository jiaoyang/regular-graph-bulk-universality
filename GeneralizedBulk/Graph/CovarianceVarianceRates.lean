import GeneralizedBulk.Graph.ReciprocalRates
import GeneralizedBulk.Graph.ProposalFiberVariance

/-!
# Polynomial quadratic-covariance rates feed the finite scalar tail mechanism

The sole missing model estimate is stated at its literal fourth-moment
location: finite centered quadratic-mark covariances. HY supplies the L1
coefficient bound, and all subsequent variance and relative-failure steps
are proved internally.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GeneralizedBulk.Graph

/-- The retained off-diagonal error has the exact exponent `-chi+2 alpha`.
In particular no rate is inferred from qualitative weak convergence. -/
theorem covariance_l1_error_le_rpow (N : ℕ) (hN : 0 < N)
    (alpha chi C0 B epsilon S : ℝ) (hC0 : 0 ≤ C0) (hB : 0 ≤ B)
    (hepsilon : 0 ≤ epsilon) (hS : 0 ≤ S)
    (hcovrate : epsilon ≤ C0 * (N : ℝ) ^ (-chi))
    (hL1 : S ≤ B * (N : ℝ) ^ alpha) :
    epsilon * S ^ 2 ≤ C0 * B ^ 2 * (N : ℝ) ^ (-chi + 2 * alpha) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hpow : S ^ 2 ≤ (B * (N : ℝ) ^ alpha) ^ 2 :=
    (sq_le_sq₀ hS (mul_nonneg hB (Real.rpow_nonneg hNR.le _))).mpr hL1
  calc
    _ ≤ (C0 * (N : ℝ) ^ (-chi)) * (B * (N : ℝ) ^ alpha) ^ 2 :=
      mul_le_mul hcovrate hpow (sq_nonneg _) (mul_nonneg hC0 (Real.rpow_nonneg hNR.le _))
    _ = C0 * B ^ 2 * ((N : ℝ) ^ (-chi) * ((N : ℝ) ^ alpha) ^ 2) := by ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hNR.le alpha 2, ← Real.rpow_add hNR]
      congr 2
      ring

/-- Below the critical exponent, the covariance error is uniformly bounded
for every positive finite graph size. -/
theorem covariance_l1_error_le_constant (N : ℕ) (hN : 0 < N)
    (alpha chi C0 B epsilon S : ℝ) (hC0 : 0 ≤ C0) (hB : 0 ≤ B)
    (hepsilon : 0 ≤ epsilon) (hS : 0 ≤ S) (hchi : 2 * alpha ≤ chi)
    (hcovrate : epsilon ≤ C0 * (N : ℝ) ^ (-chi))
    (hL1 : S ≤ B * (N : ℝ) ^ alpha) :
    epsilon * S ^ 2 ≤ C0 * B ^ 2 := by
  apply (covariance_l1_error_le_rpow N hN alpha chi C0 B epsilon S hC0 hB hepsilon hS hcovrate hL1).trans
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by linarith : -chi + 2 * alpha ≤ 0))
    (by positivity : 0 ≤ C0 * B ^ 2)).trans_eq (mul_one _)

/-- The same explicit error vanishes when the covariance exponent strictly
exceeds the two coefficient powers. -/
theorem covariance_error_rate_tendsto_zero (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (alpha chi C0 B : ℝ) (hchi : 2 * alpha < chi) :
    Tendsto (fun n => C0 * B ^ 2 * (N n : ℝ) ^ (-chi + 2 * alpha)) atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_neg_atTop (show 0 < chi - 2 * alpha by linarith)).comp
    (tendsto_natCast_atTop_atTop.comp hN)
  have heq : -chi + 2 * alpha = -(chi - 2 * alpha) := by ring
  simpa only [heq, mul_zero] using hpow.const_mul (C0 * B ^ 2)

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

/-- HY and a symbolic literal polynomial fourth-covariance rate give the
uniform linear-in-scalar-height conditional variance on the physical graph
fibers. No concentration or tail conclusion appears among the premises. -/
theorem graphFiber_linear_variance_of_HY_covariance_rate
    {P : Measure Ω} [IsProbabilityMeasure P] {K : Set ℝ} {alpha : ℝ}
    (H : HYMesoscopicInput D P K alpha) (hd : 0 < d) (E : ℝ) (hE : E ∈ K)
    (cstar gap : ℝ) (hcstar : 0 < cstar) (hgap : 0 < gap)
    (L : ℕ) (C C0 chi : ℝ) (hC : 0 ≤ C) (hC0 : 0 ≤ C0) (hchi : 2 * alpha ≤ chi) :
    ∃ V : ℝ, 0 < V ∧ ∀ᶠ n in atTop,
      ∀ ω ∈ H.events.good n, ∀ s : Finset (Fin (N n)),
      (∀ k ∈ s, |D.eigenvalue n ω k - E| ≤ (2 : ℝ) ^ L) →
      sᶜ ⊆ D.remoteEigenvalues n ω E gap → ∀ i j : Fin 4,
      (∀ k ∈ s, ∀ l ∈ s, |∫ t, D.centeredProposalQuadratic n ω k i j t *
          D.centeredProposalQuadratic n ω l i j t ∂uniformOrientedProposals (N n) d| ≤
        C * (if k = l then 1 else 0) + C0 * (N n : ℝ) ^ (-chi)) →
      ∀ eta : ℝ, 0 < eta → cstar ≤ (N n : ℝ) * eta →
        (∫ t : {t : EdgePairState (N n) d // edgePairGraph t = D.spectralRegularGraph n ω},
          ‖graphDeviation t.val (spectralParameter E eta) i j‖ ^ 2
          ∂finiteUniform {t : EdgePairState (N n) d // edgePairGraph t = D.spectralRegularGraph n ω}) ≤
            V * (1 + graphHeight (D.spectralRegularGraph n ω) (spectralParameter E eta)) := by
  obtain ⟨B, hB, hL1⟩ := D.normalized_reciprocal_sum_le_rpow_of_HY H E hE cstar hcstar L
  let V := 2 * C / cstar + 2 * (C0 * B ^ 2) + 2 * (2 / gap) ^ 2
  have hV : 0 < V := by
    have hp : 0 < (2 / gap) ^ 2 := sq_pos_of_pos (div_pos (by norm_num) hgap)
    dsimp [V]
    positivity
  refine ⟨V, hV, ?_⟩
  filter_upwards [hL1] with n hn
  intro ω hω s hs hremote i j hcov eta heta hheight
  apply D.graphFiber_variance_le_linear_height n ω hd s E eta gap cstar heta hgap hcstar hheight
    hremote C (C0 * (N n : ℝ) ^ (-chi)) (C0 * B ^ 2) hC (by positivity) i j hcov
  exact covariance_l1_error_le_constant (N n) (D.size_pos n) alpha chi C0 B
    (C0 * (N n : ℝ) ^ (-chi)) _ hC0 hB.le (by positivity)
    (Finset.sum_nonneg (fun k _ => norm_nonneg _)) hchi le_rfl (hn ω hω s hs eta heta hheight)

end GeneralizedBulk.External.RegularSpectralData
