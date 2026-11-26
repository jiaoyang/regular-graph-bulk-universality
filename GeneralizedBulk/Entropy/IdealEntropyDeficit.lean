import GeneralizedBulk.Entropy.StarEdgeFunctional
import GeneralizedBulk.Gaussian.ColoredDimensions
import GeneralizedBulk.Entropy.MehlerSignalScale

/-! The genuine Mehler observation deficit is exactly the ideal physical
star-minus-edges entropy expression. This is an identity for actual finite
signals, with no analytic or entropy premise. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Mehler.NormalizedFiniteSignal
open GeneralizedBulk.Entropy GeneralizedBulk.Entropy.Channel GeneralizedBulk.Gaussian
variable {S : Type*} [Fintype S]

theorem observationEntropyDeficit_eq_ideal (d k : ℕ) (hd : 3 ≤ d) (hd2 : 2 ≤ d)
    (D : NormalizedFiniteSignal (ScalarCoordinate d k) S) (energy : Fin k → ℝ)
    (hbulk : ∀ j, |energy j| < 2*Real.sqrt ((d : ℝ)-1)) (a : ℝ) (ha : 0 < 1-a^2) :
    D.observationEntropyDeficit (coloredObservationMatrix d k hd2)
      (coloredObservationMatrix_orthogonal d k hd2) (coloredObserved d k hd2) a =
      -idealStarEntropy d k hd2 energy D.weight (fun s => physicalSignalScale a • D.signal s) +
        (∑ i : Fin d, idealEdgeEntropy d k hd2 energy D.weight
          (fun s => physicalSignalScale a • D.signal s) i)/2 +
        (k : ℝ)/2*(1+Real.log (2*Real.pi)) +
        ∑ j, (Real.log ((d : ℝ)+energy j^2)/2 - GeneralizedBulk.KestenMcKay.bulkPotential d (energy j)) := by
  have hm := D.observationEntropyDeficit_eq_signalNoise (coloredObservationMatrix d k hd2)
    (coloredObservationMatrix_orthogonal d k hd2) (coloredObserved d k hd2)
    (coloredObserved_balanced d k hd2) a ha
  have hobs (i : Fin d) : differentialEntropy ((D.observedSignal (coloredObservationMatrix d k hd2 i)
      (coloredObservationMatrix_orthogonal d k hd2 i) (coloredObserved d k hd2 i)).signalNoiseDensity (physicalSignalScale a)) =
      edgeObservedNoiseEntropy d k hd2 D.weight (fun s => physicalSignalScale a • D.signal s) i := by
    unfold edgeObservedNoiseEntropy identityNoiseEntropy NormalizedFiniteSignal.signalNoiseDensity
    apply congrArg (fun mean => differentialEntropy (gaussianMixturePDF D.weight mean
      (fun _ => (1 : Matrix (coloredObserved d k hd2 i) (coloredObserved d k hd2 i) ℝ))))
    funext s j
    change physicalSignalScale a * ((coloredObservationMatrix d k hd2 i).transpose.mulVec (D.signal s)) j = _
    rw [Matrix.mulVec_smul]
    rfl
  simp_rw [hobs] at hm
  have hwhite : differentialEntropy (D.signalNoiseDensity (physicalSignalScale a)) =
      identityNoiseEntropy D.weight (fun s => physicalSignalScale a • D.signal s) := rfl
  rw [hwhite] at hm
  have hf := idealStarEdgeFunctional d k hd energy hbulk D.weight
    (fun s => physicalSignalScale a • D.signal s) D.nonneg D.total
  linarith

end GeneralizedBulk.Entropy.Mehler.NormalizedFiniteSignal
