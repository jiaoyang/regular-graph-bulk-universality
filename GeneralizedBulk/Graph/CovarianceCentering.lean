import GeneralizedBulk.Graph.FiniteTruncation
import GeneralizedBulk.Graph.MicroscopicOuter

/-! The finite channel covariance can be replaced by the bulk covariance. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GeneralizedBulk.Graph

theorem covarianceMatrix_entry_sub_abs_le (p q : ℝ) (i j : Fin 4) :
    |covarianceMatrix p i j - covarianceMatrix q i j| ≤ |p - q| := by
  rw [covarianceMatrix_eq, covarianceMatrix_eq]
  fin_cases i <;> fin_cases j <;> simp

/-- The microscopic step itself vanishes as the actual graph size grows. -/
theorem microscopicStep_tendsto_zero (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (sigma : ℝ) :
    Tendsto (fun n => microscopicStep (N n) sigma) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)).mul_const sigma⁻¹
  simpa only [microscopicStep, mul_inv_rev, mul_comm, Function.comp_def, zero_mul, mul_zero] using h

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def fixedCovariancePartialProposalResolvent (n : ℕ) (ω : Ω)
    (s : Finset (Fin (N n))) (p : ℝ) (z : ℂ) (i j : Fin 4)
    (t : ProposalSample (N n) d) : ℂ :=
  ∑ k ∈ s, ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) *
    ((D.proposalQuadratic n ω k i j t - covarianceMatrix p i j : ℝ) : ℂ)

/-- The covariance substitution error is deterministic and proportional to
the spectral width times the actual coefficient L1 sum. -/
theorem fixedCovariancePartialProposalResolvent_error_le
    (n : ℕ) (ω : Ω) (hd : 0 < d) (s : Finset (Fin (N n)))
    (hs : ∀ k ∈ s, k ≠ ⟨0,D.size_pos n⟩)
    (E eta : ℝ) (hnear : ∀ k ∈ s, |D.eigenvalue n ω k - E| ≤ eta)
    (z : ℂ) (i j : Fin 4) (t : ProposalSample (N n) d) :
    ‖D.centeredPartialProposalResolvent n ω s z i j t -
      D.fixedCovariancePartialProposalResolvent n ω s (E / d) z i j t‖ ≤
      (eta / (d : ℝ)) *
        (∑ k ∈ s, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹‖) := by
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  rw [D.centeredPartialProposalResolvent_eq_covariance_series n ω hd s hs]
  unfold fixedCovariancePartialProposalResolvent
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ s, ‖((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) *
        ((D.proposalQuadratic n ω k i j t - covarianceMatrix (D.eigenvalue n ω k / d) i j : ℝ) : ℂ) -
      ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) *
        ((D.proposalQuadratic n ω k i j t - covarianceMatrix (E / d) i j : ℝ) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ s, (eta / (d : ℝ)) *
        ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹‖ := by
      apply Finset.sum_le_sum
      intro k hk
      have heq : ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) *
          ((D.proposalQuadratic n ω k i j t - covarianceMatrix (D.eigenvalue n ω k / d) i j : ℝ) : ℂ) -
        ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) *
          ((D.proposalQuadratic n ω k i j t - covarianceMatrix (E / d) i j : ℝ) : ℂ) =
        ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) *
          ((covarianceMatrix (E / d) i j - covarianceMatrix (D.eigenvalue n ω k / d) i j : ℝ) : ℂ) := by
        push_cast
        ring
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hc : |covarianceMatrix (E / d) i j - covarianceMatrix (D.eigenvalue n ω k / d) i j| ≤
          eta / (d : ℝ) := by
        apply (covarianceMatrix_entry_sub_abs_le _ _ i j).trans
        rw [← sub_div, abs_div, abs_of_pos hdR, abs_sub_comm]
        exact div_le_div_of_nonneg_right (hnear k hk) hdR.le
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hc
        (norm_nonneg ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The distinguished constant channel eventually lies outside every fixed
microscopic window about a center distinct from d. -/
theorem microscopic_window_nonconstant_eventually (E sigma R : ℝ) (hE : E ≠ (d : ℝ)) :
    ∀ᶠ n in atTop, ∀ ω : Ω, ∀ k ∈ D.eigenvalueWindow n ω E
      (microscopicStep (N n) sigma * R), k ≠ ⟨0,D.size_pos n⟩ := by
  have hgap : 0 < |(d : ℝ) - E| := abs_pos.mpr (sub_ne_zero.mpr hE.symm)
  have hzero : Tendsto (fun n => microscopicStep (N n) sigma * R) atTop (𝓝 0) := by
    simpa only [zero_mul] using (microscopicStep_tendsto_zero N D.size_tendsto sigma).mul_const R
  filter_upwards [(tendsto_order.mp hzero).2 _ hgap] with n hn
  intro ω k hk heq
  subst k
  have hb := (Finset.mem_filter.mp hk).2
  rw [D.constant_eigenvalue] at hb
  exact (not_le_of_gt hn) hb

/-- HY bounds the actual covariance substitution error uniformly in the
proposal sample by the explicit decaying finite-size rate. -/
theorem microscopic_covariance_centering_error_le_of_HY
    {P : Measure Ω} [IsProbabilityMeasure P] {K : Set ℝ} {alpha : ℝ}
    (H : HYMesoscopicInput D P K alpha) (hd : 0 < d)
    (E : ℝ) (hE : E ∈ K) (hEd : E ≠ (d : ℝ))
    (sigma : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) (R : ℝ) (hR : 0 < R) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop, ∀ ω ∈ H.events.good n,
      ∀ i j : Fin 4, ∀ t : ProposalSample (N n) d,
      ‖D.centeredPartialProposalResolvent n ω
          (D.eigenvalueWindow n ω E (microscopicStep (N n) sigma * R))
          (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j t -
        D.fixedCovariancePartialProposalResolvent n ω
          (D.eigenvalueWindow n ω E (microscopicStep (N n) sigma * R)) (E / d)
          (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j t‖ ≤
        (B * R / (sigma * (d : ℝ))) * (N n : ℝ) ^ (-1 + alpha) := by
  obtain ⟨B,hB,hL1⟩ := D.microscopic_reciprocal_sum_le_rpow_of_HY H E hE sigma hsigma w 0
  have hzero : Tendsto (fun n => microscopicStep (N n) sigma * R) atTop (𝓝 0) := by
    simpa only [zero_mul] using (microscopicStep_tendsto_zero N D.size_tendsto sigma).mul_const R
  refine ⟨B,hB,?_⟩
  filter_upwards [hL1, D.microscopic_window_nonconstant_eventually E sigma R hEd,
    (tendsto_order.mp hzero).2 1 zero_lt_one] with n hn hnonconstant hsmall
  intro ω hω i j t
  let s := D.eigenvalueWindow n ω E (microscopicStep (N n) sigma * R)
  have hnear (k) (hk : k ∈ s) : |D.eigenvalue n ω k - E| ≤ microscopicStep (N n) sigma * R :=
    (Finset.mem_filter.mp hk).2
  have hwindow (k) (hk : k ∈ s) : |D.eigenvalue n ω k - E| ≤ (2 : ℝ) ^ 0 := by
    simpa only [pow_zero] using (hnear k hk).trans hsmall.le
  have hb := D.fixedCovariancePartialProposalResolvent_error_le n ω hd s
    (hnonconstant ω) E _ hnear
    (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j t
  have hL := hn ω hω s hwindow
  have hfactor : 0 ≤ (microscopicStep (N n) sigma * R) / (d : ℝ) := by
    exact div_nonneg (mul_nonneg
      (microscopicStep_pos (N n) (D.size_pos n) sigma hsigma).le hR.le) (Nat.cast_nonneg _)
  apply hb.trans
  calc
    _ ≤ ((microscopicStep (N n) sigma * R) / (d : ℝ)) * (B * (N n : ℝ) ^ alpha) :=
      mul_le_mul_of_nonneg_left hL hfactor
    _ = _ := by
      have hNR : 0 < (N n : ℝ) := Nat.cast_pos.mpr (D.size_pos n)
      rw [Real.rpow_add hNR, Real.rpow_neg_one]
      dsimp [microscopicStep]
      field_simp
      ring

/-- Along any sequence of actual HY-good graph samples, the retained
covariance centering error tends to zero uniformly in endpoint samples. -/
theorem microscopic_covariance_centering_error_tendsto_zero
    {P : Measure Ω} [IsProbabilityMeasure P] {K : Set ℝ} {alpha : ℝ}
    (H : HYMesoscopicInput D P K alpha) (halpha : alpha < 1) (hd : 0 < d)
    (E : ℝ) (hE : E ∈ K) (hEd : E ≠ (d : ℝ))
    (sigma : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) (R : ℝ) (hR : 0 < R)
    (sample : ℕ → Ω) (hgood : ∀ᶠ n in atTop, sample n ∈ H.events.good n)
    (i j : Fin 4) (t : ∀ n, ProposalSample (N n) d) :
    Tendsto (fun n => ‖D.centeredPartialProposalResolvent n (sample n)
        (D.eigenvalueWindow n (sample n) E (microscopicStep (N n) sigma * R))
        (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j (t n) -
      D.fixedCovariancePartialProposalResolvent n (sample n)
        (D.eigenvalueWindow n (sample n) E (microscopicStep (N n) sigma * R)) (E / d)
        (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j (t n)‖)
      atTop (𝓝 0) := by
  obtain ⟨B,_hB,hbound⟩ := D.microscopic_covariance_centering_error_le_of_HY
    H hd E hE hEd sigma hsigma w R hR
  have hpow := (tendsto_rpow_neg_atTop (show 0 < 1 - alpha by linarith)).comp
    (tendsto_natCast_atTop_atTop.comp D.size_tendsto)
  have hdecay : Tendsto (fun n => (B * R / (sigma * (d : ℝ))) *
      (N n : ℝ) ^ (-1 + alpha)) atTop (𝓝 0) := by
    have heq : -1 + alpha = -(1 - alpha) := by ring
    simpa only [heq, mul_zero] using hpow.const_mul (B * R / (sigma * (d : ℝ)))
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) _ hdecay
  filter_upwards [hbound,hgood] with n hn hg
  exact hn (sample n) hg i j (t n)

end GeneralizedBulk.External.RegularSpectralData
