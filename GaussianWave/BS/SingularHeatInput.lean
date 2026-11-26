import GaussianWave.BS.ChannelSupportReduction
import GaussianWave.BS.ColoredGaussianStrictness

/-!
# A regularized upper-bound input with arbitrary PSD channel covariance

The heat entropy is computed on the actual rank support after the proved
channel reduction. The source law may initially be singular. No original
density, finite entropy, Gaussianity, or channel independence is required.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

theorem channelReducedLaw_gaussian
    {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S] [DecidableEq S]
    (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :
    channelReducedLaw C hC
      (gaussianCovarianceLaw (channelCovariance C S) (channelCovariance_posSemidef C hC)) =
        standardVector (Fin C.rank × S) := by
  let L := channelSupportL C hC S
  let B := channelSupportB C hC S
  have hG : linearImageGaussian L =
      gaussianCovarianceLaw (channelCovariance C S) (channelCovariance_posSemidef C hC) := by
    apply eq_gaussianCovarianceLaw _ _ _
    intro t
    simpa only [L, channelSupport_gram] using linearImageGaussian_characteristic L t
  rw [← hG]
  unfold channelReducedLaw linearImageGaussian
  rw [Measure.map_map (measurable_finiteMatrixAction B) (measurable_finiteMatrixAction L)]
  have heq : ((fun x => B.mulVec x) ∘ fun y => L.mulVec y) = id := by
    funext y
    change B.mulVec (L.mulVec y) = y
    rw [Matrix.mulVec_mulVec, channelSupport_left_inverse, Matrix.one_mulVec]
  rw [heq, Measure.map_id]

def singularChannelHeatEntropy (d k : ℕ) (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (μ : Measure ((Fin k × Fin d) → ℝ)) (c t : ℝ) : ℝ :=
  heatFrameEntropy (channelReducedLaw C hC μ) (coloredStarEdgeProjection d C.rank c) t

theorem singular_channel_heated_entropy_upper
    (d k : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (μ : Measure ((Fin k × Fin d) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin k × Fin d)) μ)
    (hmom : HasSecondMoments μ (channelCovariance C (Fin d)))
    (hrev : ∀ i, Measure.map (edgeFlipLinear k)
      (Measure.map (fun x => (coloredStarEdgeProjection d k c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d k c i).mulVec x) μ)
    {t : ℝ} (ht : 0 < t) : singularChannelHeatEntropy d k C hC μ c t ≤ 0 :=
  colored_star_heatFrameEntropy_nonpos d C.rank hd c hbulk (channelReducedLaw C hC μ)
    (channelReducedLaw_identitySecondMoments C hC μ hμ hmom)
    (fun i => channelReducedLaw_edge_reversal d k C hC μ c i (hrev i)) ht

/-- The upper/equality input used by a subsequent lower entropy proof.
Zero directions have already been removed constructively and rank zero is
included. The conclusion is the actual ambient Gaussian with covariance C⊗I. -/
theorem singular_channel_heated_entropy_equality_iff_gaussian
    (d k : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (μ : Measure ((Fin k × Fin d) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin k × Fin d)) μ)
    (hmom : HasSecondMoments μ (channelCovariance C (Fin d)))
    (hrev : ∀ i, Measure.map (edgeFlipLinear k)
      (Measure.map (fun x => (coloredStarEdgeProjection d k c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d k c i).mulVec x) μ)
    (hperm : ∀ p : Equiv.Perm (Fin d), Measure.map (spatialPermutationMap p) μ = μ)
    {t : ℝ} (ht : 0 < t) :
    singularChannelHeatEntropy d k C hC μ c t = 0 ↔
      μ = gaussianCovarianceLaw (channelCovariance C (Fin d)) (channelCovariance_posSemidef C hC) := by
  have hm := channelReducedLaw_identitySecondMoments C hC μ hμ hmom
  have hr := fun i => channelReducedLaw_edge_reversal d k C hC μ c i (hrev i)
  have hp := fun p => channelReducedLaw_spatialPermutation C hC μ p (hperm p)
  constructor
  · intro hequality
    have hwhite := colored_star_eq_standardVector_of_heated_entropy_zero d C.rank hd c hbulk
      (channelReducedLaw C hC μ) hm hr hp ht hequality
    exact channel_gaussian_of_reduced_standard C hC μ hμ hmom hwhite
  · intro hGaussian
    apply (colored_star_heated_entropy_equality_iff_standardVector d C.rank hd c hbulk
      (channelReducedLaw C hC μ) hm hr hp ht).mpr
    rw [hGaussian]
    exact channelReducedLaw_gaussian C hC

end GaussianWave.BS
