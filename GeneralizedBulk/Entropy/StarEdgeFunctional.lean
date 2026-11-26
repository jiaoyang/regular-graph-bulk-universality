import GeneralizedBulk.Entropy.ExtendedWhiteningEntropy
import GeneralizedBulk.Entropy.EdgeWhiteningEntropy

/-! Exact star-minus-edges entropy for the actual ideal Gaussian mixtures.
The Gaussian baseline is evaluated through the proved Kesten--McKay potential. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped BigOperators Matrix
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Channel
open GeneralizedBulk.External.RegularSpectralData
variable {S : Type*} [Fintype S]

def identityNoiseEntropy {I : Type*} [Fintype I] [DecidableEq I]
    (weight : S → ℝ) (signal : S → I → ℝ) : ℝ :=
  differentialEntropy (gaussianMixturePDF weight signal (fun _ => (1 : Matrix I I ℝ)))

def edgeObservedNoiseEntropy (d k : ℕ) (hd : 2 ≤ d) (weight : S → ℝ)
    (signal : S → ScalarCoordinate d k → ℝ) (i : Fin d) : ℝ :=
  identityNoiseEntropy weight (fun s => fun a : coloredObserved d k hd i =>
    ((coloredObservationMatrix d k hd i).transpose.mulVec (signal s)) a)

def idealStarEntropy (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (weight : S → ℝ) (signal : S → ScalarCoordinate d k → ℝ) : ℝ :=
  differentialEntropy (gaussianMixturePDF weight
    (fun s => (coloredExtendedCoefficients d k hd energy).mulVec (Sum.elim (signal s) (fun _ : Fin k => 0)))
    (fun _ => coloredExtendedFactor d k hd energy))

def idealEdgeEntropy (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (weight : S → ℝ) (signal : S → ScalarCoordinate d k → ℝ) (i : Fin d) : ℝ :=
  differentialEntropy (gaussianMixturePDF weight
    (fun s j => @inner ℝ (ColoredStar d k) _ (physicalEdgeRow d k hd energy i j)
      ((scalarCoordinates d k).symm (signal s)))
    (fun _ => edgePhysicalFactor d k hd energy i))

theorem idealEdgeEntropy_eq (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) (weight : S → ℝ) (signal : S → ScalarCoordinate d k → ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (i : Fin d) :
    idealEdgeEntropy d k hd energy weight signal i = edgeObservedNoiseEntropy d k hd weight signal i +
      ∑ a, Real.log ((edgeWaveCovariance d (energy a)).det) / 2 := by
  have hh := edgePhysicalMixture_entropy_coordinates d k hd energy hE i weight
    (fun s => (scalarCoordinates d k).symm (signal s)) hw hnorm
  simpa only [(scalarCoordinates d k).apply_symm_apply] using hh

theorem idealStarEdgeFunctional (d k : ℕ) (hd : 3 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < 2 * Real.sqrt ((d : ℝ)-1))
    (weight : S → ℝ) (signal : S → ScalarCoordinate d k → ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) :
    idealStarEntropy d k (by omega) energy weight signal -
      (∑ i : Fin d, idealEdgeEntropy d k (by omega) energy weight signal i) / 2 =
      identityNoiseEntropy weight signal - (∑ i : Fin d, edgeObservedNoiseEntropy d k (by omega) weight signal i) / 2 +
        (k : ℝ) / 2 * (1 + Real.log (2 * Real.pi)) +
        ∑ a, (Real.log ((d : ℝ) + energy a ^ 2) / 2 - GeneralizedBulk.KestenMcKay.bulkPotential d (energy a)) := by
  have hd2 : 2 ≤ d := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 ≤ (d : ℝ)-1 := by linarith
  have hr : 2 * Real.sqrt ((d : ℝ)-1) < d := by
    have hs := Real.sq_sqrt hd1
    have hpos : 0 < ((d : ℝ)-2)^2 := sq_pos_of_pos (by linarith)
    nlinarith [Real.sqrt_nonneg ((d : ℝ)-1)]
  have hEd (a : Fin k) : |energy a| < d := (hE a).trans hr
  have hs := coloredExtendedMixture_entropy d k hd2 energy hEd weight signal hw hnorm
  change idealStarEntropy d k hd2 energy weight signal = identityNoiseEntropy weight signal + _ + _ at hs
  have he (i : Fin d) := idealEdgeEntropy_eq d k hd2 energy hEd weight signal hw hnorm i
  have hb : (∑ a, Real.log ((starWaveCovariance d (energy a) + starNormalProjection d (energy a)).det) / 2) -
      (d : ℝ) / 2 * (∑ a, Real.log ((edgeWaveCovariance d (energy a)).det) / 2) =
      ∑ a, (Real.log ((d : ℝ) + energy a ^ 2) / 2 - GeneralizedBulk.KestenMcKay.bulkPotential d (energy a)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    convert gaussianStarFunctional d hd (energy a) (hE a) using 1 <;> ring
  rw [hs]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

end GeneralizedBulk.Entropy
