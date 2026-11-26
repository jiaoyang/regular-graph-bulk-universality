import GeneralizedBulk.Graph.EmpiricalEdgeEntropySymmetry
import GeneralizedBulk.Gaussian.ColoredDimensions
import GeneralizedBulk.Entropy.IdealEntropyDeficit
import GeneralizedBulk.Entropy.NormalEntropyCancellation

/-! The actual normalized empirical Mehler entropy deficit equals the literal
ideal physical star-minus-edge entropy expression with its evaluated Gaussian
baseline. All channel dimensions and ordered-leaf symmetry are proved. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped BigOperators Matrix
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Entropy GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy.Mehler
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem empirical_observationEntropyDeficit_ideal {k : ℕ} (hd : 3 ≤ d) (hd2 : 2 ≤ d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d)
    (hbulk : ∀ a, |D.eigenvalue n ω (selection a)| < 2 * Real.sqrt ((d : ℝ)-1))
    (a : ℝ) (ha : 0 < 1-a^2) (leaf : Fin d) :
    (D.empiricalNormalizedSignal n ω hd2 selection hinj hE).observationEntropyDeficit
      (coloredObservationMatrix d k hd2) (coloredObservationMatrix_orthogonal d k hd2)
      (coloredObserved d k hd2) a =
      -idealStarEntropy d k hd2 (fun j => D.eigenvalue n ω (selection j)) (D.empiricalStarWeight n)
        (fun s => physicalSignalScale a • (D.empiricalNormalizedSignal n ω hd2 selection hinj hE).signal s) +
      (d : ℝ)/2 * idealEdgeEntropy d k hd2 (fun j => D.eigenvalue n ω (selection j)) (D.empiricalStarWeight n)
        (fun s => physicalSignalScale a • (D.empiricalNormalizedSignal n ω hd2 selection hinj hE).signal s) leaf +
      (k : ℝ)/2*(1+Real.log (2*Real.pi)) +
      ∑ j, (Real.log ((d : ℝ)+D.eigenvalue n ω (selection j)^2)/2 -
        GeneralizedBulk.KestenMcKay.bulkPotential d (D.eigenvalue n ω (selection j))) := by
  let F := D.empiricalNormalizedSignal n ω hd2 selection hinj hE
  let r := physicalSignalScale a
  have hh := GeneralizedBulk.Entropy.Mehler.NormalizedFiniteSignal.observationEntropyDeficit_eq_ideal d k hd hd2 F
    (fun j => D.eigenvalue n ω (selection j)) hbulk a ha
  have hw : F.weight = D.empiricalStarWeight n := rfl
  rw [hw] at hh
  have hleaf (i : Fin d) : idealEdgeEntropy d k hd2 (fun j => D.eigenvalue n ω (selection j))
      (D.empiricalStarWeight n) (fun s => r • F.signal s) i =
      idealEdgeEntropy d k hd2 (fun j => D.eigenvalue n ω (selection j))
        (D.empiricalStarWeight n) (fun s => r • F.signal s) leaf :=
    D.empirical_idealEdgeEntropy_leaf_eq n ω hd2 selection hinj hE r i leaf
  dsimp only [r] at hleaf
  simp_rw [hleaf] at hh
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  convert hh using 1 <;> ring

theorem empirical_observationEntropyDeficit_rescaled_ideal {k : ℕ} (hd : 3 ≤ d) (hd2 : 2 ≤ d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d)
    (hbulk : ∀ a, |D.eigenvalue n ω (selection a)| < 2 * Real.sqrt ((d : ℝ)-1))
    (a : ℝ) (ha : 0 < 1-a^2) (leaf : Fin d) (eta : ℝ) (heta : 0 < eta)
    (sigma : Fin k → ℝ) (hsigma : ∀ j, 0 < sigma j) :
    (D.empiricalNormalizedSignal n ω hd2 selection hinj hE).observationEntropyDeficit
      (coloredObservationMatrix d k hd2) (coloredObservationMatrix_orthogonal d k hd2)
      (coloredObserved d k hd2) a =
      -(idealStarEntropy d k hd2 (fun j => D.eigenvalue n ω (selection j)) (D.empiricalStarWeight n)
        (fun s => physicalSignalScale a • (D.empiricalNormalizedSignal n ω hd2 selection hinj hE).signal s) -
        ∑ j, Real.log (starNormalRescaleFactor d (D.eigenvalue n ω (selection j)) eta (sigma j))) +
      (d : ℝ)/2 * idealEdgeEntropy d k hd2 (fun j => D.eigenvalue n ω (selection j)) (D.empiricalStarWeight n)
        (fun s => physicalSignalScale a • (D.empiricalNormalizedSignal n ω hd2 selection hinj hE).signal s) leaf +
      ∑ j, ((1+Real.log (2*Real.pi)+Real.log (eta/sigma j))/2 -
        GeneralizedBulk.KestenMcKay.bulkPotential d (D.eigenvalue n ω (selection j))) := by
  have hh := D.empirical_observationEntropyDeficit_ideal n ω hd hd2 selection hinj hE hbulk a ha leaf
  have hb := coloredNormal_gaussianBaseline d k (by omega) (fun j => D.eigenvalue n ω (selection j)) sigma eta heta hsigma
  linarith

end GeneralizedBulk.External.RegularSpectralData
