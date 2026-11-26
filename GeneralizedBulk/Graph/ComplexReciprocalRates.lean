import GeneralizedBulk.Graph.CovarianceVarianceRates
import GeneralizedBulk.Graph.ComplexRemoteVariance

/-! HY reciprocal bounds at every fixed nonreal microscopic spectral point. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace GeneralizedBulk.Graph

/-- Comparing denominators costs a fixed spectral factor and requires no
assumption on the real variable. -/
theorem inverse_real_difference_norm_le (x : ℝ) (z z0 : ℂ)
    (hz : z.im ≠ 0) (hz0 : z0.im ≠ 0) :
    ‖((x : ℂ) - z)⁻¹‖ ≤ (1 + ‖z - z0‖ / |z.im|) * ‖((x : ℂ) - z0)⁻¹‖ := by
  have hi : 0 < |z.im| := abs_pos.mpr hz
  have hden : 0 < ‖(x : ℂ) - z‖ := by
    have h := Complex.abs_im_le_norm ((x : ℂ) - z)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
    exact hi.trans_le h
  have hden0 : 0 < ‖(x : ℂ) - z0‖ := by
    have h := Complex.abs_im_le_norm ((x : ℂ) - z0)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
    exact (abs_pos.mpr hz0).trans_le h
  have hbound : |z.im| ≤ ‖(x : ℂ) - z‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] using
      Complex.abs_im_le_norm ((x : ℂ) - z)
  have hr : ‖z - z0‖ ≤ (‖z - z0‖ / |z.im|) * ‖(x : ℂ) - z‖ := by
    calc
      _ = (‖z - z0‖ / |z.im|) * |z.im| := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound (div_nonneg (norm_nonneg _) hi.le)
  have htri : ‖(x : ℂ) - z0‖ ≤ ‖(x : ℂ) - z‖ + ‖z - z0‖ := by
    convert norm_add_le ((x : ℂ) - z) (z - z0) using 1 <;> ring_nf
  have hcomp : ‖(x : ℂ) - z0‖ ≤ (1 + ‖z - z0‖ / |z.im|) * ‖(x : ℂ) - z‖ := by
    nlinarith only [htri, hr]
  calc
    _ = 1 / ‖(x : ℂ) - z‖ := by rw [norm_inv, one_div]
    _ ≤ (1 + ‖z - z0‖ / |z.im|) / ‖(x : ℂ) - z0‖ :=
      (div_le_div_iff₀ hden hden0).mpr (by simpa only [one_mul] using hcomp)
    _ = _ := by rw [norm_inv]; ring

/-- The comparison constant for a fixed microscopic parameter is independent
of the finite graph size and the positive microscopic scale. -/
def microscopicComparison (w : GraphNonreal) : ℝ :=
  1 + ‖w.1 - Complex.I‖ / |w.1.im|

theorem microscopicComparison_pos (w : GraphNonreal) : 0 < microscopicComparison w := by
  unfold microscopicComparison
  have := div_nonneg (norm_nonneg (w.1 - Complex.I)) (abs_nonneg w.1.im)
  linarith

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

/-- Each actual finite microscopic coefficient is bounded by its vertical
counterpart, with a constant depending only on `w`. -/
theorem microscopic_coefficient_norm_le_vertical
    (n : ℕ) (ω : Ω) (E sigma : ℝ) (hsigma : 0 < sigma)
    (w : GraphNonreal) (k : Fin (N n)) :
    ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) -
      (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1)⁻¹‖ ≤
      microscopicComparison w * ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) -
        spectralParameter E (microscopicStep (N n) sigma))⁻¹‖ := by
  let c := microscopicStep (N n) sigma
  have hc : 0 < c := microscopicStep_pos (N n) (D.size_pos n) sigma hsigma
  let z := (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1
  let z0 := spectralParameter E c
  have hzim : z.im = c * w.1.im := by simp [z, microscopicParameter, c]
  have hz0im : z0.im = c := by simp [z0]
  have hdiff : z - z0 = (c : ℂ) * (w.1 - Complex.I) := by
    dsimp [z, z0, microscopicParameter, spectralParameter, c]
    ring
  have hfactor : 1 + ‖z - z0‖ / |z.im| = microscopicComparison w := by
    rw [hdiff, hzim, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc, abs_mul, abs_of_pos hc]
    unfold microscopicComparison
    congr 1
    exact mul_div_mul_left _ _ (ne_of_gt hc)
  have h := inverse_real_difference_norm_le (D.eigenvalue n ω k) z z0
    (by rw [hzim]; exact mul_ne_zero (ne_of_gt hc) w.2)
    (by rw [hz0im]; exact ne_of_gt hc)
  rw [hfactor] at h
  simp only [norm_mul]
  convert mul_le_mul_of_nonneg_left h (norm_nonneg ((N n : ℂ)⁻¹)) using 1 <;> ring

/-- The HY dyadic reciprocal estimate holds at the actual arbitrary fixed
nonreal microscopic point, including the lower half plane. -/
theorem microscopic_reciprocal_sum_le_rpow_of_HY
    {P : Measure Ω} [IsProbabilityMeasure P] {K : Set ℝ} {alpha : ℝ}
    (H : HYMesoscopicInput D P K alpha) (E : ℝ) (hE : E ∈ K)
    (sigma : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) (L : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop,
      ∀ ω ∈ H.events.good n, ∀ s : Finset (Fin (N n)),
      (∀ k ∈ s, |D.eigenvalue n ω k - E| ≤ (2 : ℝ) ^ L) →
        (∑ k ∈ s, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) -
          (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1)⁻¹‖) ≤
          B * (N n : ℝ) ^ alpha := by
  obtain ⟨B, hB, hbound⟩ := D.normalized_reciprocal_sum_le_rpow_of_HY H E hE
    sigma⁻¹ (inv_pos.mpr hsigma) L
  refine ⟨microscopicComparison w * B, mul_pos (microscopicComparison_pos w) hB, ?_⟩
  filter_upwards [hbound] with n hn
  intro ω hω s hs
  have hheight : sigma⁻¹ ≤ (N n : ℝ) * microscopicStep (N n) sigma := by
    have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
    have heq : (N n : ℝ) * microscopicStep (N n) sigma = sigma⁻¹ := by
      dsimp [microscopicStep]
      field_simp
    rw [heq]
  calc
    _ ≤ ∑ k ∈ s, microscopicComparison w * ‖(N n : ℂ)⁻¹ *
        ((D.eigenvalue n ω k : ℂ) - spectralParameter E (microscopicStep (N n) sigma))⁻¹‖ :=
      Finset.sum_le_sum (fun k hk => D.microscopic_coefficient_norm_le_vertical n ω E sigma hsigma w k)
    _ = microscopicComparison w * (∑ k ∈ s, ‖(N n : ℂ)⁻¹ *
        ((D.eigenvalue n ω k : ℂ) - spectralParameter E (microscopicStep (N n) sigma))⁻¹‖) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ microscopicComparison w * (B * (N n : ℝ) ^ alpha) :=
      mul_le_mul_of_nonneg_left
        (hn ω hω s hs _ (microscopicStep_pos (N n) (D.size_pos n) sigma hsigma) hheight)
        (microscopicComparison_pos w).le
    _ = _ := by ring

/-- HY and the literal finite fourth-covariance rate give the complex
microscopic weighted remote bound, retaining the complete polynomial error. -/
theorem weighted_microscopic_remote_variance_of_HY_covariance_rate
    {P : Measure Ω} [IsProbabilityMeasure P] {K : Set ℝ} {alpha : ℝ}
    (H : HYMesoscopicInput D P K alpha) (hd : 0 < d) (E : ℝ) (hE : E ∈ K)
    (sigma : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) (L : ℕ)
    (C C0 chi : ℝ) (hC : 0 ≤ C) (hC0 : 0 ≤ C0) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop,
      ∀ ω ∈ H.events.good n, ∀ s : Finset (Fin (N n)),
      (∀ k ∈ s, |D.eigenvalue n ω k - E| ≤ (2 : ℝ) ^ L) →
      ∀ theta : Fin (N n) → ℝ, (∀ k ∈ s, |theta k| ≤ 1) →
      ∀ R : ℝ, 0 < R → 2 * |w.1.re| ≤ R →
      s ⊆ D.remoteEigenvalues n ω E (microscopicStep (N n) sigma * R) →
      ∀ i j : Fin 4,
      (∀ k ∈ s, ∀ l ∈ s, |∫ t, D.centeredProposalQuadratic n ω k i j t *
          D.centeredProposalQuadratic n ω l i j t ∂uniformOrientedProposals (N n) d| ≤
        C * (if k = l then 1 else 0) + C0 * (N n : ℝ) ^ (-chi)) →
      (∫ t, ‖D.weightedCenteredPartialProposalResolvent n ω s theta
        (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j t‖ ^ 2
        ∂uniformOrientedProposals (N n) d) ≤
        C * ((8 * sigma / R) * (D.scalarResolvent n ω
          (spectralParameter E (microscopicStep (N n) sigma * R))).im) +
        C0 * B ^ 2 * (N n : ℝ) ^ (-chi + 2 * alpha) := by
  obtain ⟨B,hB,hbound⟩ := D.microscopic_reciprocal_sum_le_rpow_of_HY H E hE sigma hsigma w L
  refine ⟨B,hB,?_⟩
  filter_upwards [hbound] with n hn
  intro ω hω s hs theta htheta R hR hw hremote i j hcov
  apply (D.weighted_microscopic_remote_variance_le n ω hd s theta htheta E sigma hsigma
    w R hR hw hremote C (C0 * (N n : ℝ) ^ (-chi)) hC (by positivity) i j hcov).trans
  apply add_le_add_left
  exact covariance_l1_error_le_rpow (N n) (D.size_pos n) alpha chi C0 B
    (C0 * (N n : ℝ) ^ (-chi)) _ hC0 hB.le (by positivity)
    (Finset.sum_nonneg (fun k _ => norm_nonneg _)) le_rfl (hn ω hω s hs)

end GeneralizedBulk.External.RegularSpectralData
