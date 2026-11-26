import GeneralizedBulk.Graph.TruncationErrorMeasurable
import GeneralizedBulk.Analysis.GoodFiberMoments

/-! The actual finite-window covariance replacement vanishes in joint
graph/proposal probability. The exceptional HY event is retained explicitly. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem microscopic_covariance_centering_probability
    {P : Measure Ω} [IsProbabilityMeasure P] {K : Set ℝ} {alpha : ℝ}
    (H : HYMesoscopicInput D P K alpha) (halpha : alpha < 1) (hd : 0 < d)
    (E : ℝ) (hE : E ∈ K) (hEd : E ≠ (d:ℝ))
    (sigma : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) (R : ℝ) (hR : 0 < R)
    (i j : Fin 4) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (P.prod (uniformOrientedProposals (N n) d)).real
      {z : Ω × ProposalSample (N n) d | ε <
        ‖D.centeredPartialProposalResolvent n z.1
          (D.eigenvalueWindow n z.1 E (microscopicStep (N n) sigma*R))
          (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j z.2 -
        D.fixedCovariancePartialProposalResolvent n z.1
          (D.eigenvalueWindow n z.1 E (microscopicStep (N n) sigma*R)) (E/d)
          (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j z.2‖}) atTop (𝓝 0) := by
  letI : ∀ n,IsProbabilityMeasure (uniformOrientedProposals (N n) d) :=
    fun n => uniformOrientedProposals_isProbability _ _ (D.size_pos n) hd
  obtain ⟨B,hB,hbound⟩ := D.microscopic_covariance_centering_error_le_of_HY
    H hd E hE hEd sigma hsigma w R hR
  have hp := (tendsto_rpow_neg_atTop (show 0 < 1-alpha by linarith)).comp
    (tendsto_natCast_atTop_atTop.comp D.size_tendsto)
  have hrate : Tendsto (fun n => (B*R/(sigma*(d:ℝ)))*(N n:ℝ)^(-1+alpha)) atTop (𝓝 0) := by
    simpa only [show -1+alpha= -(1-alpha) by ring,mul_zero] using hp.const_mul (B*R/(sigma*(d:ℝ)))
  apply squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) _
    (H.events.failure_tendsto_zero D.size_tendsto)
  filter_upwards [hbound,(tendsto_order.mp hrate).2 ε hε] with n hn hsmall
  have hsub : {z : Ω × ProposalSample (N n) d | ε <
        ‖D.centeredPartialProposalResolvent n z.1
          (D.eigenvalueWindow n z.1 E (microscopicStep (N n) sigma*R))
          (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j z.2 -
        D.fixedCovariancePartialProposalResolvent n z.1
          (D.eigenvalueWindow n z.1 E (microscopicStep (N n) sigma*R)) (E/d)
          (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j z.2‖} ⊆
      (H.events.good n ×ˢ univ)ᶜ := by
    intro z hz hg
    exact (not_lt_of_ge ((hn z.1 hg.1 i j z.2).trans hsmall.le)) hz
  exact (measureReal_mono hsub).trans_eq
    (product_good_failure_mass P (uniformOrientedProposals (N n) d) (H.events.good n))

end GeneralizedBulk.External.RegularSpectralData
