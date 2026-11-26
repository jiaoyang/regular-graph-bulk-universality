import GeneralizedBulk.Graph.HYResolventChannel
import GeneralizedBulk.Graph.SpectralSampleDensities
import GeneralizedBulk.Graph.ColoredNoiseEntropy
import GeneralizedBulk.Graph.EntropyGoodEvent

/-! The genuine correlated entropy channel is expressed in the physical
sample densities used by the local comparisons, with the actual global
colored resolvent noise on its left. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy GeneralizedBulk.Entropy.ChannelRates GeneralizedBulk.Graph.Configuration
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem HY_actual_physical_entropy_channel_eventually {P : Measure Ω} [IsProbabilityMeasure P]
    {quantile : ∀ n,Fin (N n) → ℝ} (H : HYCoarseInput D P quantile)
    (k : ℕ) (hd : 0 < d) (c0 : ℝ) (hc0 : 0 < c0)
    (hsmall : c0 < channelNoiseExponent (channelTheta k d))
    (s S : ℝ) (hs : 0 < s) (hS : 0 < S) :
    ∀ᶠ n in atTop,∀ ω ∈ H.events.good n,
      ω ∈ D.entropyCountingGood k entropyCountingConstant (entropyCountingSimplicity d) n →
      ∀ (selection : Fin k → Fin (N n)) (sigma : Fin k → ℝ) (hsigma : ∀ a,s ≤ sigma a ∧ sigma a ≤ S),
      let θ := channelTheta k d
      let lo := channelCovarianceFloor θ (N n)
      let eta := (N n : ℝ)^(-c0)
      let A := D.coloredResolventCovarianceFactor n ω (fun a => D.eigenvalue n ω (selection a)) eta sigma
      ∃ hlower : ∀ x : Fin k × Fin (N n) → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x),
        ∀ r ∈ Set.Icc (0 : ℝ) 1,
          differentialEntropy (affineGaussianPDF 0 A)/(N n : ℝ) ≤
            differentialEntropy (D.spectralStarGaussianDensity n ω A lo
              (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _) hlower
              (fun i => r*D.rawEigenSignal n ω selection i))-
            (d : ℝ)/2*differentialEntropy (D.spectralEdgeGaussianDensity n ω A lo
              (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _) hlower
              (fun i => r*D.rawEigenSignal n ω selection i))+(N n : ℝ)^(-θ/2) := by
  have hbase := D.HY_actual_resolvent_channel_eventually H k hd entropyCountingConstant (entropyCountingSimplicity d)
    c0 hc0 hsmall s S hs hS
  filter_upwards [hbase] with n hn
  intro ω hω hG selection sigma hsigma θ lo eta A
  obtain ⟨hlower,hchannel⟩ := hn ω hω hG selection sigma hsigma
  refine ⟨hlower,?_⟩
  intro r hr
  have hh := hchannel r hr
  have heta : 0 < eta := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _
  have hdet : A.det ≠ 0 := D.coloredResolventCovarianceFactor_det_ne_zero n ω _ sigma eta heta
    (fun a => hs.trans_le (hsigma a).1)
  rw [wholeGaussianDensity_entropy_square_factor A hdet,
    D.starGaussianDensity_entropy_spectral n ω,D.edgeGaussianDensity_entropy_spectral n ω _ _ _ _ hd] at hh
  exact hh

end GeneralizedBulk.External.RegularSpectralData
