import GeneralizedBulk.Graph.EmpiricalEntropyDeficit
import GeneralizedBulk.Graph.PhysicalEntropyChannel
import GeneralizedBulk.Graph.EntropyDeficitComparison

/-! The literal empirical Mehler deficit follows from the actual physical
channel and its local/global entropy comparisons. Gaussian baseline
cancellation is a theorem here, rather than an additional comparison premise. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Entropy GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem empirical_deficit_le_of_physical_comparisons {k : ℕ} (hd : 3 ≤ d) (hd2 : 2 ≤ d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (hE : ∀ j,|D.eigenvalue n ω (selection j)| < d)
    (hbulk : ∀ j,|D.eigenvalue n ω (selection j)| < 2*Real.sqrt ((d : ℝ)-1))
    (a : ℝ) (ha : 0 < 1-a^2) (leaf : Fin d) (eta : ℝ) (heta : 0 < eta)
    (sigma : Fin k → ℝ) (hsigma : ∀ j,0 < sigma j)
    (lo : ℝ) (hlo : 0 < lo)
    (hlower : ∀ x : Fin k × Fin (N n) → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x
      ((D.coloredResolventCovarianceFactor n ω (fun j => D.eigenvalue n ω (selection j)) eta sigma*
        (D.coloredResolventCovarianceFactor n ω (fun j => D.eigenvalue n ω (selection j)) eta sigma).transpose).mulVec x)) :
    let energy := fun j => D.eigenvalue n ω (selection j)
    let A := D.coloredResolventCovarianceFactor n ω energy eta sigma
    let F := D.empiricalNormalizedSignal n ω hd2 selection hinj hE
    let r := physicalSignalScale a
    let global := differentialEntropy (affineGaussianPDF 0 A)/(N n : ℝ)
    let star := differentialEntropy (D.spectralStarGaussianDensity n ω A lo hlo hlower
      (fun i => r*D.rawEigenSignal n ω selection i))
    let edge := differentialEntropy (D.spectralEdgeGaussianDensity n ω A lo hlo hlower
      (fun i => r*D.rawEigenSignal n ω selection i))
    let idealStar := idealStarEntropy d k hd2 energy (D.empiricalStarWeight n) (fun q => r • F.signal q)
    let idealEdge := idealEdgeEntropy d k hd2 energy (D.empiricalStarWeight n) (fun q => r • F.signal q) leaf
    let jacobian := ∑ j,Real.log (starNormalRescaleFactor d (energy j) eta (sigma j))
    let baseline := ∑ j,((1+Real.log (2*Real.pi)+Real.log (eta/sigma j))/2-GeneralizedBulk.KestenMcKay.bulkPotential d (energy j))
    ∀ channelError starError edgeError globalError : ℝ,
      global ≤ star-(d : ℝ)/2*edge+channelError →
      |star-(idealStar-jacobian)| ≤ starError → |edge-idealEdge| ≤ edgeError →
      |global-baseline| ≤ globalError →
      F.observationEntropyDeficit (coloredObservationMatrix d k hd2) (coloredObservationMatrix_orthogonal d k hd2)
        (coloredObserved d k hd2) a ≤ channelError+starError+(d : ℝ)/2*edgeError+globalError := by
  intro energy A F r global star edge idealStar idealEdge jacobian baseline channelError starError edgeError globalError
    hchannel hstar hedge hglobal
  have hc := D.empirical_observationEntropyDeficit_rescaled_ideal n ω hd hd2 selection hinj hE hbulk
    a ha leaf eta heta sigma hsigma
  apply entropy_deficit_of_channel_comparisons (d : ℝ) global star edge idealStar idealEdge jacobian baseline
    (F.observationEntropyDeficit (coloredObservationMatrix d k hd2) (coloredObservationMatrix_orthogonal d k hd2)
      (coloredObserved d k hd2) a) channelError starError edgeError globalError (Nat.cast_nonneg d)
      hchannel hstar hedge hglobal
  change F.observationEntropyDeficit (coloredObservationMatrix d k hd2) (coloredObservationMatrix_orthogonal d k hd2)
    (coloredObserved d k hd2) a= -(idealStar-jacobian)+(d : ℝ)/2*idealEdge+baseline at hc
  linarith only [hc]

end GeneralizedBulk.External.RegularSpectralData
