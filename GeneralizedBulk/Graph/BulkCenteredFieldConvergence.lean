import GeneralizedBulk.Graph.CenteredFieldConvergence
import GeneralizedBulk.Graph.WindowFieldConvergence
import GeneralizedBulk.Graph.BulkTruncationProbability
import GeneralizedBulk.Graph.CovarianceCenteringProbability
import GeneralizedBulk.Counting.MeanIntensity

/-! The actual finite centered microscopic field converges to the genuinely
constructed mixed Gaussian series. All truncation errors are proved from HY. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Gaussian GeneralizedBulk.Analysis GeneralizedBulk.Counting
open GeneralizedBulk.KestenMcKay GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω V : Type*} [MeasurableSpace Ω] [Fintype V]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2500000 in
theorem HY_microscopic_fixedCovariance_truncation_probability
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 3 ≤ d) (HC : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)))
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1))
    (c0 : ℝ) (hc1 : c0 < channelNoiseExponent (channelTheta 1 d))
    (hc2 : c0 < channelNoiseExponent (channelTheta 2 d))
    (hcr : c0 < HC.rigidity_exponent) (hcs : c0 ≤ 1/16)
    (HL : HYLocalStarInput D P K c0 (treeGreenStar d (by exact_mod_cast hd)))
    {Km : Set ℝ} {alpha : ℝ} (HM : HYMesoscopicInput D P Km alpha) (halpha : alpha < 1)
    (hchi : 2*alpha < proposalCovarianceExponent d HC.rigidity_exponent HL.local_exponent c0)
    (E : ℝ) (hE : E ∈ Km) (gap : ℝ) (hgap : 0 < gap)
    (hwindow : Icc (E-2*gap) (E+2*gap) ⊆ K) (L : ℕ) (hL : 2*gap ≤ (2 : ℝ)^L)
    (center : ℝ) (parameters : Parameters) (hp : parameters.p=E/d)
    (HG : HYGeometryInput D P) (w : GraphNonreal)
    (R : ℕ → ℝ) (hR : ∀ k : ℕ,(k:ℝ)+1 ≤ R k) (r : ℕ → ℕ) (hr : StrictMono r)
    (i j : Fin 4) :
    ∀ ε δ : ℝ,0 < ε → 0 < δ → ∃ k0 : ℕ,∀ k : ℕ,k0 ≤ k →
      ∀ᶠ n in atTop,(P.prod (uniformOrientedProposals (N (r n)) d)).real
        {z | ε < ‖D.microscopicCenteredMatrix (r n) E parameters w z i j -
          D.microscopicWindowMatrix (r n) E parameters (R k) w z i j‖} ≤ δ := by
  have hdpos : 0 < d := by omega
  letI : ∀ n,IsProbabilityMeasure (uniformOrientedProposals (N n) d) :=
    fun n => uniformOrientedProposals_isProbability _ _ (D.size_pos n) hdpos
  have hEd : E ≠ (d : ℝ) := by
    intro he
    have hb := hbulk E (hwindow ⟨by linarith,by linarith⟩)
    rw [he] at hb
    nlinarith [sq_nonneg ((d : ℝ)-2)]
  have hmain := D.HY_microscopic_centered_truncation_probability hUniform hd HC K hK hbulk
    c0 hc1 hc2 hcr hcs HL HM hchi E hE gap hgap hwindow L hL parameters.scale center
    parameters.scale_pos HG w R hR i j
  intro ε δ hε hδ
  obtain ⟨k0,hk0⟩ := hmain (ε/2) (δ/2) (half_pos hε) (half_pos hδ)
  refine ⟨k0,fun k hk => ?_⟩
  have hRpos : 0 < R k := (show (0:ℝ)<(k:ℝ)+1 by positivity).trans_le (hR k)
  have hcov := D.microscopic_covariance_centering_probability HM halpha hdpos E hE hEd
    parameters.scale parameters.scale_pos w (R k) hRpos i j (ε/2) (half_pos hε)
  have hcovsmall := ((tendsto_order.mp (hcov.comp hr.tendsto_atTop)).2 (δ/2) (half_pos hδ)).mono
    (fun n hn => hn.le)
  filter_upwards [hr.tendsto_atTop.eventually (hk0 k hk),hcovsmall] with n hn hcn
  let Q := P.prod (uniformOrientedProposals (N (r n)) d)
  let A := {z | ε/2 < ‖D.microscopicCenteredTruncationError (r n) E parameters.scale parameters.scale_pos w (R k) i j z‖}
  let B := {z : Ω × ProposalSample (N (r n)) d | ε/2 <
    ‖D.centeredPartialProposalResolvent (r n) z.1
      (D.eigenvalueWindow (r n) z.1 E (microscopicStep (N (r n)) parameters.scale*R k))
      (microscopicParameter (N (r n)) (D.size_pos (r n)) E parameters.scale parameters.scale_pos w).val i j z.2 -
    D.fixedCovariancePartialProposalResolvent (r n) z.1
      (D.eigenvalueWindow (r n) z.1 E (microscopicStep (N (r n)) parameters.scale*R k)) parameters.p
      (microscopicParameter (N (r n)) (D.size_pos (r n)) E parameters.scale parameters.scale_pos w).val i j z.2‖}
  have hsub : {z | ε < ‖D.microscopicCenteredMatrix (r n) E parameters w z i j -
      D.microscopicWindowMatrix (r n) E parameters (R k) w z i j‖} ⊆ A ∪ B := by
    intro z hz
    by_cases ha : z ∈ A
    · exact Or.inl ha
    · apply Or.inr
      by_contra hb
      have htri := norm_sub_le_norm_sub_add_norm_sub
        (D.microscopicCenteredMatrix (r n) E parameters w z i j)
        (D.centeredPartialProposalResolvent (r n) z.1
          (D.eigenvalueWindow (r n) z.1 E (microscopicStep (N (r n)) parameters.scale*R k))
          (microscopicParameter (N (r n)) (D.size_pos (r n)) E parameters.scale parameters.scale_pos w).val i j z.2)
        (D.microscopicWindowMatrix (r n) E parameters (R k) w z i j)
      have ha' : ‖D.microscopicCenteredMatrix (r n) E parameters w z i j -
          D.centeredPartialProposalResolvent (r n) z.1
            (D.eigenvalueWindow (r n) z.1 E (microscopicStep (N (r n)) parameters.scale*R k))
            (microscopicParameter (N (r n)) (D.size_pos (r n)) E parameters.scale parameters.scale_pos w).val i j z.2‖ ≤ ε/2 :=
        le_of_not_gt ha
      have hb' : ‖D.centeredPartialProposalResolvent (r n) z.1
          (D.eigenvalueWindow (r n) z.1 E (microscopicStep (N (r n)) parameters.scale*R k))
          (microscopicParameter (N (r n)) (D.size_pos (r n)) E parameters.scale parameters.scale_pos w).val i j z.2 -
          D.microscopicWindowMatrix (r n) E parameters (R k) w z i j‖ ≤ ε/2 := le_of_not_gt hb
      change ε < ‖D.microscopicCenteredMatrix (r n) E parameters w z i j -
        D.microscopicWindowMatrix (r n) E parameters (R k) w z i j‖ at hz
      linarith
  have hbound := (measureReal_mono (μ := Q) hsub).trans (measureReal_union_le A B)
  have hB : Q.real B ≤ δ/2 := by simpa only [B,Q,hp] using hcn
  have hA : Q.real A ≤ δ/2 := hn
  linarith

set_option maxHeartbeats 3000000 in
/-- Ordinary BS/HY inputs and an actual scalar subsequential limit construct
the full joint Gaussian marked-series limit, allowing finite total mass. -/
theorem microscopicCenteredState_converges_of_BS_HY [Nonempty Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 3 ≤ d) (HC : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)))
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1))
    (c0 : ℝ) (hc1 : c0 < channelNoiseExponent (channelTheta 1 d))
    (hc2 : c0 < channelNoiseExponent (channelTheta 2 d))
    (hcr : c0 < HC.rigidity_exponent) (hcs : c0 ≤ 1/16)
    (HL : HYLocalStarInput D P K c0 (treeGreenStar d (by exact_mod_cast hd)))
    {Km : Set ℝ} {alpha : ℝ} (HM : HYMesoscopicInput D P Km alpha) (halpha : alpha < 1)
    (hchi : 2*alpha < proposalCovarianceExponent d HC.rigidity_exponent HL.local_exponent c0)
    (KBS : Set ℝ) (BS : BSQualitativeInput D P KBS)
    (E : ℝ) (hE : E ∈ Km) (hEBS : E ∈ KBS) (gap : ℝ) (hgap : 0 < gap)
    (hwindow : Icc (E-2*gap) (E+2*gap) ⊆ K) (L : ℕ) (hL : 2*gap ≤ (2 : ℝ)^L)
    (center : ℝ) (parameters : Parameters) (hp : parameters.p=E/d) (HG : HYGeometryInput D P)
    (r : ℕ → ℕ) (hr : StrictMono r)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (hscalar : WeakLawConverges
      (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E parameters.scale center)) ν)
    (R : ℕ → ℝ) (hR : ∀ k : ℕ,(k:ℝ)+1 ≤ R k)
    (hboundary : ∀ k,∀ᵐ s ∂ν,s.val.1.measure {-R k}=0 ∧ s.val.1.measure {R k}=0)
    (w : V → GraphNonreal) :
    WeakLawConverges
      (fun n => Measure.map (D.microscopicCenteredState (r n) E center parameters w)
        (P.prod (uniformOrientedProposals (N (r n)) d)))
      (Measure.map (massCenteredState ν hm parameters (fun v => ((w v).val,false)))
        (massMarkedLaw ν parameters)) := by
  have hRtendsto : Tendsto R atTop atTop :=
    tendsto_atTop_mono hR (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hsmall : Icc (E-gap) (E+gap) ⊆ K := by
    intro x hx
    exact hwindow ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hfinite (k) := D.microscopicWindowState_converges_of_BS_HY r hr P hUniform KBS BS HC
    K hK hbulk c0 hc1 hcr hcs HL E center (R k) gap parameters hp hEBS hgap hsmall
    ⟨0,by omega⟩ ν hscalar (hboundary k) w
  apply D.microscopicCenteredState_converges_of_window_tails r P (by omega) E center parameters w
    ν hm R hRtendsto hfinite
  intro v i j
  exact D.HY_microscopic_fixedCovariance_truncation_probability hUniform hd HC K hK hbulk
    c0 hc1 hc2 hcr hcs HL HM halpha hchi E hE gap hgap hwindow L hL center parameters hp
    HG (w v) R hR r hr i j

set_option maxHeartbeats 3000000 in
/-- The atom-free windows are constructed from the actual limiting scalar
law; no cutoff or boundary regularity certificate is an input. -/
theorem microscopicCenteredState_converges_of_BS_HY_limit [Nonempty Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 3 ≤ d) (HC : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)))
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1))
    (c0 : ℝ) (hc1 : c0 < channelNoiseExponent (channelTheta 1 d))
    (hc2 : c0 < channelNoiseExponent (channelTheta 2 d))
    (hcr : c0 < HC.rigidity_exponent) (hcs : c0 ≤ 1/16)
    (HL : HYLocalStarInput D P K c0 (treeGreenStar d (by exact_mod_cast hd)))
    {Km : Set ℝ} {alpha : ℝ} (HM : HYMesoscopicInput D P Km alpha) (halpha : alpha < 1)
    (hchi : 2*alpha < proposalCovarianceExponent d HC.rigidity_exponent HL.local_exponent c0)
    (KBS : Set ℝ) (BS : BSQualitativeInput D P KBS)
    (E : ℝ) (hE : E ∈ Km) (hEBS : E ∈ KBS) (gap : ℝ) (hgap : 0 < gap)
    (hwindow : Icc (E-2*gap) (E+2*gap) ⊆ K) (L : ℕ) (hL : 2*gap ≤ (2 : ℝ)^L)
    (center : ℝ) (parameters : Parameters) (hp : parameters.p=E/d) (HG : HYGeometryInput D P)
    (r : ℕ → ℕ) (hr : StrictMono r)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (hscalar : WeakLawConverges
      (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E parameters.scale center)) ν)
    (w : V → GraphNonreal) :
    WeakLawConverges
      (fun n => Measure.map (D.microscopicCenteredState (r n) E center parameters w)
        (P.prod (uniformOrientedProposals (N (r n)) d)))
      (Measure.map (massCenteredState ν hm parameters (fun v => ((w v).val,false)))
        (massMarkedLaw ν parameters)) := by
  obtain ⟨R,hmono,hRt,hR,hboundary⟩ := exists_atom_free_radii ν hm
  have hR' (k : ℕ) : (k : ℝ)+1 ≤ R (k+1) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (hR (k+1)).le
  have hb (k : ℕ) : ∀ᵐ s ∂ν,s.val.1.measure {-R (k+1)}=0 ∧ s.val.1.measure {R (k+1)}=0 :=
    hboundary.mono (fun s hs => ⟨(hs (k+1)).2,(hs (k+1)).1⟩)
  exact D.microscopicCenteredState_converges_of_BS_HY P hUniform hd HC K hK hbulk c0 hc1 hc2
    hcr hcs HL HM halpha hchi KBS BS E hE hEBS gap hgap hwindow L hL center parameters hp HG
    r hr ν hm hscalar (fun k => R (k+1)) hR' hb w

end GeneralizedBulk.External.RegularSpectralData
