import GeneralizedBulk.Graph.ResolventChannelParameters
import GeneralizedBulk.Graph.SpectralPortTransport
import GeneralizedBulk.Graph.GrowingPaletteGood

/-! The common graph entropy inequality instantiated with the actual colored
resolvent factor and the actual HY-delocalized eigenvector signal. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical Matrix.L2OpNorm

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph GeneralizedBulk.Graph.Configuration GeneralizedBulk.Entropy GeneralizedBulk.Entropy.ChannelRates

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem regularGraph_handshake {V degree : ℕ} (G : RegularGraph V degree) :
    V*degree = 2*(V*degree/2) := by
  have h := G.val.sum_degrees_eq_twice_card_edges
  simp only [G.property.degree_eq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  have he : V*degree = 2*G.val.edgeFinset.card := by simpa using h
  rw [he]
  omega

def entropyCountingGood (k : ℕ) (C : ℝ) (M : ℕ) (n : ℕ) : Set Ω :=
  {ω | GraphProfileGood (q := channelPalette k (channelTheta k d) (N n)) (m := N n*d/2)
    C ((N n : ℝ)^(1/4 : ℝ)) M (D.spectralRegularGraph n ω)}

set_option maxHeartbeats 2000000 in
theorem HY_actual_resolvent_channel_eventually {P : Measure Ω} [IsProbabilityMeasure P]
    {quantile : ∀ n,Fin (N n) → ℝ} (H : HYCoarseInput D P quantile)
    (k : ℕ) (hd : 0 < d) (C : ℝ) (M : ℕ) (c0 : ℝ) (hc0 : 0 < c0)
    (hsmall : c0 < channelNoiseExponent (channelTheta k d))
    (s S : ℝ) (hs : 0 < s) (hS : 0 < S) :
    ∀ᶠ n in atTop,∀ ω ∈ H.events.good n,ω ∈ D.entropyCountingGood k C M n →
      ∀ (selection : Fin k → Fin (N n)) (sigma : Fin k → ℝ) (hsigma : ∀ a,s ≤ sigma a ∧ sigma a ≤ S),
      let θ := channelTheta k d
      let lo := channelCovarianceFloor θ (N n)
      let eta := (N n : ℝ)^(-c0)
      let A := D.coloredResolventCovarianceFactor n ω (fun a => D.eigenvalue n ω (selection a)) eta sigma
      ∃ hlower : ∀ x : Fin k × Fin (N n) → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x),
        ∀ r ∈ Set.Icc (0 : ℝ) 1,
          differentialEntropy (wholeGaussianDensity A lo
            (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _) hlower 0)/(N n : ℝ) ≤
            differentialEntropy (starGaussianDensity A lo
              (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _) hlower (D.spectralRegularGraph n ω)
              (fun i => r*D.rawEigenSignal n ω selection i))-
            (d : ℝ)/2*differentialEntropy (edgeGaussianDensity A lo
              (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _) hlower (D.spectralRegularGraph n ω)
              (fun i => r*D.rawEigenSignal n ω selection i))+(N n : ℝ)^(-θ/2) := by
  have hbase := D.size_tendsto.eventually (eventually_correlated_gaussian_channel_polynomial k d M C)
  have hnoise := D.colored_resolvent_channel_bounds_eventually (k := k) (channelTheta k d) c0 hc0 hsmall s S hs hS
  have hsignal := D.HY_rawEigenSignal_polynomial_eventually H (channelTheta k d) (channelTheta_pos k d)
  filter_upwards [hbase,hnoise,hsignal] with n hbase hnoise hsignal
  intro ω hω hG selection sigma hsigma θ lo eta A
  have hb := hnoise ω (fun a => D.eigenvalue n ω (selection a)) sigma hsigma
    (fun a => D.eigenvalue_abs_le_degree n ω (selection a))
  refine ⟨hb.2,?_⟩
  intro r hr
  have hNd := regularGraph_handshake (D.spectralRegularGraph n ω)
  let e : (Fin k → Fin (2*channelCutoff θ (N n))) ≃ Fin (channelPalette k θ (N n)) :=
    Fintype.equivFinOfCardEq (by simp only [Fintype.card_fun,Fintype.card_fin,channelPalette])
  exact hbase (N n*d/2) A (D.spectralRegularGraph n ω) hd hNd hb.1
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _) hb.2 hG e
    (D.rawEigenSignal n ω selection) (hsignal ω hω selection) r hr

set_option maxHeartbeats 1000000 in
theorem measurable_spectralRegularGraph (n : ℕ) : Measurable (D.spectralRegularGraph n) := by
  let f : RegularGraph (N n) d → (Fin (N n) → Fin (N n) → ℝ) := fun G => G.val.adjMatrix ℝ
  have hi : Function.Injective f := by
    intro G H he
    apply Subtype.ext
    apply SimpleGraph.ext
    funext v w
    apply propext
    have hh := congrFun (congrFun he v) w
    by_cases hg : G.val.Adj v w <;> by_cases hh' : H.val.Adj v w <;>
      simp [f,SimpleGraph.adjMatrix_apply,hg,hh'] at hh ⊢
  have hf : MeasurableEmbedding f := ⟨hi,measurable_of_finite _,by
    intro t ht
    exact ((Set.toFinite t).image f).measurableSet⟩
  apply hf.measurable_comp_iff.mp
  have he : f ∘ D.spectralRegularGraph n = D.adjacency n := by
    funext ω v w
    rcases D.entry_zero_one n ω v w with hz | ho
    · simp [f,spectralRegularGraph,simpleGraph,SimpleGraph.adjMatrix_apply,hz]
    · simp [f,spectralRegularGraph,simpleGraph,SimpleGraph.adjMatrix_apply,ho]
  rw [he]
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro w
  exact D.measurable_adjacency n v w

theorem measurableSet_entropyCountingGood (k : ℕ) (C : ℝ) (M n : ℕ) :
    MeasurableSet (D.entropyCountingGood k C M n) := by
  change MeasurableSet ((D.spectralRegularGraph n) ⁻¹' {G | GraphProfileGood
    (q := channelPalette k (channelTheta k d) (N n)) (m := N n*d/2) C ((N n : ℝ)^(1/4 : ℝ)) M G})
  exact (D.measurable_spectralRegularGraph n) (Set.to_countable _).measurableSet

theorem entropyCountingGood_polynomial_failure {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P = regularGraphLaw (N n) d)
    (hd : 0 < d) (k : ℕ) (C : ℝ)
    (hC : ∀ j : ℕ,|Real.log j.factorial-logFactorialMain j| ≤ C+Real.log (j+1))
    (M : ℕ) (hM : 8*d*(d+1) ≤ M) (Dpow : ℝ) :
    ∀ᶠ n in atTop,P.real (D.entropyCountingGood k C M n)ᶜ ≤ (N n : ℝ)^(-Dpow) := by
  have hgraphs (n) : Nonempty (RegularGraph (N n) d) := by
    have hn : Nonempty Ω := by
      by_contra h
      letI : IsEmpty Ω := not_nonempty_iff.mp h
      have hu := measure_univ (μ := P)
      have he : (Set.univ : Set Ω) = ∅ := by ext x; exact isEmptyElim x
      rw [he,measure_empty] at hu
      exact zero_ne_one hu
    exact ⟨D.spectralRegularGraph n (Classical.choice hn)⟩
  have hNd (n) : N n*d = 2*(N n*d/2) := by
    exact regularGraph_handshake (Classical.choice (hgraphs n))
  have h := growing_palette_good_polynomial_failure d hd N (fun n => channelPalette k (channelTheta k d) (N n))
    (fun n => N n*d/2) D.size_tendsto hgraphs hNd C hC M hM (1/4) (by norm_num) Dpow
  filter_upwards [h] with n hn
  have hs : MeasurableSet {G : RegularGraph (N n) d | ¬ GraphProfileGood (q := channelPalette k (channelTheta k d) (N n))
      (m := N n*d/2) C ((N n : ℝ)^(1/4 : ℝ)) M G} := (Set.to_countable _).measurableSet
  have he : P.real (D.entropyCountingGood k C M n)ᶜ =
      (regularGraphLaw (N n) d).real {G | ¬ GraphProfileGood (q := channelPalette k (channelTheta k d) (N n))
        (m := N n*d/2) C ((N n : ℝ)^(1/4 : ℝ)) M G} := by
    rw [← hUniform n]
    change (P (D.entropyCountingGood k C M n)ᶜ).toReal =
      ((Measure.map (D.spectralRegularGraph n) P) _).toReal
    rw [Measure.map_apply (D.measurable_spectralRegularGraph n) hs]
    rfl
  exact he ▸ hn

end GeneralizedBulk.External.RegularSpectralData
