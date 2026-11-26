import GeneralizedBulk.Graph.BulkProposalVariance
import GeneralizedBulk.Analysis.PolynomialEventIntersection

/-! The actual physical variance event is measurable and has a polynomial
exceptional probability under the uniform simple regular graph model. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Analysis GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def commonProposalGood (P : Measure Ω) [IsProbabilityMeasure P]
    (coarse localEvents mesoscopic : PolynomialGoodEvents P N) (n : ℕ) : Set Ω :=
  D.commonOneTwoEntropyGood P coarse localEvents n ∩ mesoscopic.good n

theorem measurableSet_commonProposalGood (P : Measure Ω) [IsProbabilityMeasure P]
    (coarse localEvents mesoscopic : PolynomialGoodEvents P N) (n : ℕ) :
    MeasurableSet (D.commonProposalGood P coarse localEvents mesoscopic n) :=
  (D.measurableSet_commonOneTwoEntropyGood P coarse localEvents n).inter (mesoscopic.measurable_good n)

theorem commonProposalGood_failure_tendsto_zero {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 0 < d) (coarse localEvents mesoscopic : PolynomialGoodEvents P N) :
    Tendsto (fun n => P.real (D.commonProposalGood P coarse localEvents mesoscopic n)ᶜ) atTop (nhds 0) :=
  intersection_failure_tendsto_zero P _ _
    (D.commonOneTwoEntropyGood_failure_tendsto_zero hUniform hd coarse localEvents)
    (mesoscopic.failure_tendsto_zero D.size_tendsto)

set_option maxHeartbeats 1500000 in
theorem commonProposalGood_failure_polynomial {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 0 < d) (coarse localEvents mesoscopic : PolynomialGoodEvents P N) :
    ∃ β C : ℝ,0 < β ∧ 0 < C ∧ ∀ᶠ n in atTop,
      P.real (D.commonProposalGood P coarse localEvents mesoscopic n)ᶜ ≤ C*(N n : ℝ)^(-β) := by
  obtain ⟨a,A,ha,hA,hfirst⟩ := D.commonEntropyGood_failure_polynomial hUniform hd 1 coarse localEvents
  obtain ⟨b,B,hb,hB,hsecond⟩ := D.commonEntropyGood_failure_polynomial hUniform hd 2 coarse localEvents
  obtain ⟨c,C,hc,hC,hboth⟩ := intersection_polynomial_failure P N D.size_pos _ _ a b A B ha hb hA hB hfirst hsecond
  have hm : ∀ᶠ n in atTop,P.real (mesoscopic.good n)ᶜ ≤ mesoscopic.constant*(N n : ℝ)^(-mesoscopic.exponent) := by
    filter_upwards [eventually_ge_atTop mesoscopic.threshold] with n hn
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (mesoscopic.failure_bound n hn)
    simpa only [measureReal_def,ENNReal.toReal_ofReal (mul_nonneg mesoscopic.constant_pos.le
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))] using h
  exact intersection_polynomial_failure P N D.size_pos _ _ c mesoscopic.exponent C mesoscopic.constant
    hc mesoscopic.exponent_pos hC mesoscopic.constant_pos hboth hm

theorem channelTheta_two_le_one (d : ℕ) : channelTheta 2 d ≤ channelTheta 1 d := by
  unfold channelTheta
  norm_num only [Nat.cast_ofNat]
  apply one_div_le_one_div_of_le (show (0 : ℝ) < 2000*((d : ℝ)+1) by positivity)
  nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

theorem entropyHeight_one_two_bounds (rigidity : ℝ) (hr : 0 < rigidity) :
    0 < entropyHeight 2 d rigidity ∧
    entropyHeight 2 d rigidity < channelNoiseExponent (channelTheta 1 d) ∧
    entropyHeight 2 d rigidity < channelNoiseExponent (channelTheta 2 d) ∧
    entropyHeight 2 d rigidity < rigidity ∧ entropyHeight 2 d rigidity ≤ 1/16 := by
  have h := entropyHeight_bounds 2 d rigidity hr
  have hm : channelNoiseExponent (channelTheta 2 d) ≤ channelNoiseExponent (channelTheta 1 d) :=
    div_le_div_of_nonneg_right (channelTheta_two_le_one d) (by norm_num)
  exact ⟨h.1,h.2.1.trans_le hm,h.2.1,h.2.2.1,h.2.2.2⟩

end GeneralizedBulk.External.RegularSpectralData
