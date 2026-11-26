import GeneralizedBulk.Graph.BulkProposalGoodEvent

/-! Ordinary choices of compact bulk neighborhoods and positive exponents
used by the final finite-graph theorem. These are proved choices, not extra
analytic assumptions on a graph sequence. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace GeneralizedBulk.Graph
open GeneralizedBulk.External.RegularSpectralData

theorem exists_compact_bulk_window (d : ℕ) (E : ℝ)
    (hbulk : E^2 < 4*((d:ℝ)-1)) :
    ∃ (K : Set ℝ) (gap : ℝ) (L : ℕ),IsCompact K ∧ E ∈ K ∧ 0 < gap ∧
      (∀ x ∈ K,x^2 < 4*((d:ℝ)-1)) ∧
      Icc (E-2*gap) (E+2*gap) ⊆ K ∧ 2*gap ≤ (2:ℝ)^L := by
  have ho : IsOpen {x : ℝ | x^2 < 4*((d:ℝ)-1)} :=
    isOpen_lt (continuous_id.pow 2) continuous_const
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp ho E hbulk
  let gap := δ/4
  let K := Icc (E-2*gap) (E+2*gap)
  obtain ⟨L,hL⟩ := exists_nat_gt (2*gap)
  have hpow : ∀ n : ℕ,(n:ℝ) ≤ (2:ℝ)^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [Nat.cast_succ,pow_succ]
        have hp : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
        nlinarith
  refine ⟨K,gap,L,isCompact_Icc,?_,by dsimp [gap]; positivity,?_,Subset.rfl,hL.le.trans (hpow L)⟩
  · constructor <;> dsimp [K,gap] <;> linarith
  · intro x hx
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    have ha : |x-E| ≤ δ/2 := abs_le.mpr (by
      dsimp [K,gap] at hx
      constructor <;> linarith [hx.1,hx.2])
    exact ha.trans_lt (by linarith)

theorem canonical_entropy_height_bounds (d : ℕ) (rigidity : ℝ) (hr : 0 < rigidity) :
    let c := GeneralizedBulk.Entropy.ChannelRates.entropyHeight 2 d rigidity
    0 < c ∧ c < GeneralizedBulk.Entropy.ChannelRates.channelNoiseExponent
        (GeneralizedBulk.Entropy.ChannelRates.channelTheta 1 d) ∧
      c < GeneralizedBulk.Entropy.ChannelRates.channelNoiseExponent
        (GeneralizedBulk.Entropy.ChannelRates.channelTheta 2 d) ∧
      c < rigidity ∧ c ≤ 1/16 := entropyHeight_one_two_bounds rigidity hr

theorem exists_admissible_mesoscopic_exponent (d : ℕ) (rigidity localExponent height : ℝ)
    (hl : 0 < localExponent) (hh : 0 < height) (hr : height < rigidity) (h1 : height < 1) :
    ∃ alpha : ℝ,0 < alpha ∧
      2*alpha ≤ proposalCovarianceExponent d rigidity localExponent height := by
  have hc := proposalCovarianceExponent_pos (d := d) rigidity localExponent height hl hh hr h1
  refine ⟨proposalCovarianceExponent d rigidity localExponent height/4,by positivity,?_⟩
  linarith

theorem exists_strict_mesoscopic_exponent (d : ℕ) (rigidity localExponent height : ℝ)
    (hl : 0 < localExponent) (hh : 0 < height) (hr : height < rigidity) (h1 : height < 1) :
    ∃ alpha : ℝ,0 < alpha ∧ alpha < 1 ∧
      2*alpha < proposalCovarianceExponent d rigidity localExponent height := by
  have hc := proposalCovarianceExponent_pos (d := d) rigidity localExponent height hl hh hr h1
  let alpha := min (proposalCovarianceExponent d rigidity localExponent height/4) (1/4)
  have ha0 : 0 < alpha := lt_min (by positivity) (by norm_num)
  have ha1 : alpha ≤ (1:ℝ)/4 := min_le_right _ _
  have hac : alpha ≤ proposalCovarianceExponent d rigidity localExponent height/4 := min_le_left _ _
  exact ⟨alpha,ha0,by linarith,by linarith⟩

end GeneralizedBulk.Graph
