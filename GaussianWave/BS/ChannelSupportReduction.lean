import GaussianWave.BS.CovarianceSupport
import GaussianWave.BS.RankSupportReduction
import GaussianWave.BS.ColoredFisherMonotonicity

/-!
# Removing singular channel covariance before entropy calculations

The channel maps act simultaneously at every spatial coordinate. Genuine
second moments imply both identity moments of the reduced law and actual
almost-everywhere reconstruction of the source law. Zero channel directions
are removed before finite-dimensional density or entropy statements.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

/-- M tensor the spatial identity, with channel × spatial coordinates. -/
def channelLift {I J : Type*} (M : Matrix J I ℝ) (S : Type*) [DecidableEq S] :
    Matrix (J × S) (I × S) ℝ :=
  fun p q => if q.2 = p.2 then M p.1 q.1 else 0

lemma channelLift_mulVec {I J S : Type*} [Fintype I] [Fintype S] [DecidableEq S]
    (M : Matrix J I ℝ) (x : (I × S) → ℝ) (j : J) (s : S) :
    (channelLift M S).mulVec x (j, s) = ∑ i, M j i * x (i, s) := by
  simp [channelLift, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

lemma channelLift_transpose {I J S : Type*} [DecidableEq S] (M : Matrix J I ℝ) :
    (channelLift M S).transpose = channelLift M.transpose S := by
  ext ⟨i, s⟩ ⟨j, t⟩
  simp only [Matrix.transpose_apply, channelLift]
  by_cases h : s = t <;> simp [h, Ne.symm]

lemma channelLift_mul {I J K S : Type*} [Fintype J] [Fintype S] [DecidableEq S]
    (A : Matrix K J ℝ) (B : Matrix J I ℝ) :
    channelLift A S * channelLift B S = channelLift (A * B) S := by
  ext ⟨a, s⟩ ⟨b, t⟩
  by_cases h : t = s
  · subst t
    simp [channelLift, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul, mul_ite]
  · simp [channelLift, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul, mul_ite, h, Ne.symm h]

lemma channelLift_one (I S : Type*) [DecidableEq I] [DecidableEq S] :
    channelLift (1 : Matrix I I ℝ) S = 1 := by
  ext ⟨i, s⟩ ⟨j, t⟩
  by_cases h : s = t
  · subst t
    simp [channelLift, Matrix.one_apply]
  · simp [channelLift, Matrix.one_apply, Prod.mk.injEq, h, Ne.symm h]

/-- The source colored white-star covariance C tensor the spatial identity. -/
def channelCovariance {κ : Type*} (C : Matrix κ κ ℝ) (S : Type*) [DecidableEq S] :
    Matrix (κ × S) (κ × S) ℝ := channelLift C S

section Support
variable {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S] [DecidableEq S]

/-- Full-column reconstruction map applied at every spatial site. -/
def channelSupportL (C : Matrix κ κ ℝ) (hC : C.PosSemidef) (S : Type*) [DecidableEq S] :
    Matrix (κ × S) (Fin C.rank × S) ℝ := channelLift (covarianceRankL C hC) S

/-- Actual channel-whitening map applied at every spatial site. -/
def channelSupportB (C : Matrix κ κ ℝ) (hC : C.PosSemidef) (S : Type*) [DecidableEq S] :
    Matrix (Fin C.rank × S) (κ × S) ℝ := channelLift (covarianceRankB C hC) S

lemma channelSupport_gram (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :
    channelSupportL C hC S * (channelSupportL C hC S).transpose = channelCovariance C S := by
  rw [channelSupportL, channelLift_transpose, channelLift_mul, covarianceRankL_mul_transpose]
  rfl

lemma channelSupport_left_inverse (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :
    channelSupportB C hC S * channelSupportL C hC S = 1 := by
  rw [channelSupportB, channelSupportL, channelLift_mul, covarianceRankB_mul_L, channelLift_one]

lemma channelCovariance_posSemidef (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :
    (channelCovariance C S).PosSemidef := by
  rw [← channelSupport_gram C hC]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (channelSupportL C hC S)

/-- The actual law after deleting zero-variance channel directions. -/
def channelReducedLaw (C : Matrix κ κ ℝ) (hC : C.PosSemidef) (μ : Measure ((κ × S) → ℝ)) :
    Measure ((Fin C.rank × S) → ℝ) :=
  Measure.map (fun x => (channelSupportB C hC S).mulVec x) μ

instance channelReducedLaw_isProbability (C : Matrix κ κ ℝ) (hC : C.PosSemidef)
    (μ : Measure ((κ × S) → ℝ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (channelReducedLaw C hC μ) :=
  isProbabilityMeasure_map (measurable_finiteMatrixAction _).aemeasurable

theorem channelReducedLaw_integrable_squareRadius (C : Matrix κ κ ℝ) (hC : C.PosSemidef)
    (μ : Measure ((κ × S) → ℝ)) (hμ : Integrable (squareRadius (I := κ × S)) μ) :
    Integrable (squareRadius (I := Fin C.rank × S)) (channelReducedLaw C hC μ) :=
  integrable_squareRadius_matrixImage μ hμ (channelSupportB C hC S)

/-- Identity second moments are computed from the original second moments;
they are not a hypothesis on the reduced law. -/
theorem channelReducedLaw_identitySecondMoments (C : Matrix κ κ ℝ) (hC : C.PosSemidef)
    (μ : Measure ((κ × S) → ℝ)) (hμ : Integrable (squareRadius (I := κ × S)) μ)
    (hmom : HasSecondMoments μ (channelCovariance C S)) :
    HasIdentitySecondMoments (channelReducedLaw C hC μ) := by
  apply identitySecondMoments_of_gram_leftInverse μ hμ (channelSupportL C hC S)
    (channelSupportB C hC S) _ (channelSupport_left_inverse C hC)
  rw [channelSupport_gram]
  exact hmom

/-- Original samples lie in the actual reconstructed channel support almost
surely, without Gaussianity. -/
theorem channelSupport_reconstruction_ae (C : Matrix κ κ ℝ) (hC : C.PosSemidef)
    (μ : Measure ((κ × S) → ℝ)) (hμ : Integrable (squareRadius (I := κ × S)) μ)
    (hmom : HasSecondMoments μ (channelCovariance C S)) :
    ∀ᵐ x ∂μ, (channelSupportL C hC S).mulVec ((channelSupportB C hC S).mulVec x) = x := by
  apply gram_leftInverse_reconstruction_ae μ hμ (channelSupportL C hC S)
    (channelSupportB C hC S) _ (channelSupport_left_inverse C hC)
  rw [channelSupport_gram]
  exact hmom

/-- Actual reconstruction of the entire source law after support reduction. -/
theorem channelSupport_reconstruction_law (C : Matrix κ κ ℝ) (hC : C.PosSemidef)
    (μ : Measure ((κ × S) → ℝ)) (hμ : Integrable (squareRadius (I := κ × S)) μ)
    (hmom : HasSecondMoments μ (channelCovariance C S)) :
    Measure.map (fun y => (channelSupportL C hC S).mulVec y) (channelReducedLaw C hC μ) = μ := by
  apply gram_leftInverse_reconstruction_law μ hμ (channelSupportL C hC S)
    (channelSupportB C hC S) _ (channelSupport_left_inverse C hC)
  rw [channelSupport_gram]
  exact hmom

/-- A Gaussian reduced law reconstructs the actual possibly singular
Gaussian source law with covariance C tensor the spatial identity. -/
theorem channel_gaussian_of_reduced_standard (C : Matrix κ κ ℝ) (hC : C.PosSemidef)
    (μ : Measure ((κ × S) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := κ × S)) μ)
    (hmom : HasSecondMoments μ (channelCovariance C S))
    (hwhite : channelReducedLaw C hC μ = standardVector (Fin C.rank × S)) :
    μ = gaussianCovarianceLaw (channelCovariance C S) (channelCovariance_posSemidef C hC) := by
  have hgram : HasSecondMoments μ (channelSupportL C hC S * (channelSupportL C hC S).transpose) := by
    rw [channelSupport_gram]
    exact hmom
  have hg := gaussian_of_standard_whitened_gram_law μ hμ (channelSupportL C hC S)
    (channelSupportB C hC S) hgram (channelSupport_left_inverse C hC) hwhite
  apply eq_gaussianCovarianceLaw μ _ (channelCovariance_posSemidef C hC)
  rw [hg]
  intro t
  simpa only [channelSupport_gram] using linearImageGaussian_characteristic (channelSupportL C hC S) t

/-- At rank zero the reduced coordinate law is automatically the unique
probability law on the zero-dimensional coordinate space. -/
theorem channelReducedLaw_standard_of_rank_zero (C : Matrix κ κ ℝ) (hC : C.PosSemidef)
    (μ : Measure ((κ × S) → ℝ)) [IsProbabilityMeasure μ] (hrank : C.rank = 0) :
    channelReducedLaw C hC μ = standardVector (Fin C.rank × S) := by
  haveI : IsEmpty (Fin C.rank) := by rw [hrank]; infer_instance
  apply measure_eq_of_linear_characteristic
  intro t
  simp

/-- Rank-zero source covariance therefore gives its actual degenerate
Gaussian law, before any density or entropy is introduced. -/
theorem channel_gaussian_of_rank_zero (C : Matrix κ κ ℝ) (hC : C.PosSemidef)
    (μ : Measure ((κ × S) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := κ × S)) μ)
    (hmom : HasSecondMoments μ (channelCovariance C S)) (hrank : C.rank = 0) :
    μ = gaussianCovarianceLaw (channelCovariance C S) (channelCovariance_posSemidef C hC) :=
  channel_gaussian_of_reduced_standard C hC μ hμ hmom
    (channelReducedLaw_standard_of_rank_zero C hC μ hrank)

end Support


/-- Pushing forward an invariant law through an actually intertwining map
preserves its symmetry. -/
theorem map_invariant_of_intertwining
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (e : X → X) (e' : Y → Y)
    (hf : Measurable f) (he : Measurable e) (he' : Measurable e')
    (hcomm : e' ∘ f = f ∘ e) (hinv : Measure.map e μ = μ) :
    Measure.map e' (Measure.map f μ) = Measure.map f μ := by
  rw [Measure.map_map he' hf, hcomm, ← Measure.map_map hf he, hinv]

/-- Simultaneous permutation of the spatial coordinates in every channel. -/
def spatialPermutationMap {I S : Type*} (p : Equiv.Perm S) (x : (I × S) → ℝ) :
    (I × S) → ℝ := fun q => x (q.1, p q.2)

lemma measurable_spatialPermutationMap (I S : Type*) (p : Equiv.Perm S) :
    Measurable (@spatialPermutationMap I S p) := by
  apply measurable_pi_lambda
  rintro ⟨i, s⟩
  exact measurable_pi_apply (i, p s)

lemma channelLift_spatialPermutation {I J S : Type*}
    [Fintype I] [Fintype S] [DecidableEq S]
    (M : Matrix J I ℝ) (p : Equiv.Perm S) (x : (I × S) → ℝ) :
    (channelLift M S).mulVec (spatialPermutationMap p x) =
      spatialPermutationMap p ((channelLift M S).mulVec x) := by
  funext ⟨j, s⟩
  change (channelLift M S).mulVec (spatialPermutationMap p x) (j, s) =
    (channelLift M S).mulVec x (j, p s)
  simp only [channelLift_mulVec, spatialPermutationMap]

/-- Original neighbor permutation symmetry passes to the actual support law. -/
theorem channelReducedLaw_spatialPermutation
    {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S] [DecidableEq S]
    (C : Matrix κ κ ℝ) (hC : C.PosSemidef) (μ : Measure ((κ × S) → ℝ))
    (p : Equiv.Perm S) (hperm : Measure.map (spatialPermutationMap p) μ = μ) :
    Measure.map (spatialPermutationMap p) (channelReducedLaw C hC μ) =
      channelReducedLaw C hC μ := by
  apply map_invariant_of_intertwining μ (fun x => (channelSupportB C hC S).mulVec x)
    (spatialPermutationMap p) (spatialPermutationMap p)
    (measurable_finiteMatrixAction _) (measurable_spatialPermutationMap κ S p)
    (measurable_spatialPermutationMap (Fin C.rank) S p) _ hperm
  funext x
  exact (channelLift_spatialPermutation (covarianceRankB C hC) p x).symm

/-- The same channel matrix applied at both endpoints (identity tensor M). -/
def endpointChannelLift {I J : Type*} (M : Matrix J I ℝ) :
    Matrix (Bool × J) (Bool × I) ℝ :=
  fun p q => if q.1 = p.1 then M p.2 q.2 else 0

lemma endpointChannelLift_mulVec {I J : Type*} [Fintype I]
    (M : Matrix J I ℝ) (x : (Bool × I) → ℝ) (b : Bool) (j : J) :
    (endpointChannelLift M).mulVec x (b, j) = ∑ i, M j i * x (b, i) := by
  cases b <;> simp [endpointChannelLift, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fintype.sum_bool, ite_mul]

/-- Channel support reduction intertwines the entire 2r-dimensional edge
observation, rather than only individual scalar rows. -/
theorem coloredStarEdgeProjection_channelLift (d k r : ℕ) (c : ℝ) (i : Fin d)
    (B : Matrix (Fin r) (Fin k) ℝ) :
    coloredStarEdgeProjection d r c i * channelLift B (Fin d) =
      endpointChannelLift B * coloredStarEdgeProjection d k c i := by
  ext ⟨b, a⟩ ⟨q, j⟩
  simp [Matrix.mul_apply, channelLift, endpointChannelLift, coloredStarEdgeProjection,
    Fintype.sum_prod_type, ite_mul, mul_ite, eq_comm, mul_comm]

lemma endpointChannelLift_edgeFlip (k r : ℕ) (B : Matrix (Fin r) (Fin k) ℝ)
    (x : (Bool × Fin k) → ℝ) :
    (endpointChannelLift B).mulVec (edgeFlipLinear k x) =
      edgeFlipLinear r ((endpointChannelLift B).mulVec x) := by
  funext ⟨b, a⟩
  rw [endpointChannelLift_mulVec]
  change (∑ i, B a i * x (!b, i)) = (endpointChannelLift B).mulVec x (!b, a)
  rw [endpointChannelLift_mulVec]

/-- Actual whole-edge reversal is retained under a simultaneous channel map. -/
theorem endpointChannelLift_reversal (k r : ℕ) (B : Matrix (Fin r) (Fin k) ℝ)
    (ν : Measure ((Bool × Fin k) → ℝ))
    (hrev : Measure.map (edgeFlipLinear k) ν = ν) :
    Measure.map (edgeFlipLinear r) (Measure.map (fun x => (endpointChannelLift B).mulVec x) ν) =
      Measure.map (fun x => (endpointChannelLift B).mulVec x) ν := by
  apply map_invariant_of_intertwining ν (fun x => (endpointChannelLift B).mulVec x)
    (edgeFlipLinear k) (edgeFlipLinear r) (measurable_finiteMatrixAction _)
    (edgeFlipLinear k).continuous.measurable (edgeFlipLinear r).continuous.measurable _ hrev
  funext x
  exact (endpointChannelLift_edgeFlip k r B x).symm

/-- Exact actual law of a reduced edge. -/
theorem channelReducedLaw_edge_law (d k : ℕ)
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (μ : Measure ((Fin k × Fin d) → ℝ)) (c : ℝ) (i : Fin d) :
    Measure.map (fun x => (coloredStarEdgeProjection d C.rank c i).mulVec x)
      (channelReducedLaw C hC μ) =
      Measure.map (fun z => (endpointChannelLift (covarianceRankB C hC)).mulVec z)
        (Measure.map (fun x => (coloredStarEdgeProjection d k c i).mulVec x) μ) := by
  rw [channelReducedLaw, Measure.map_map (measurable_finiteMatrixAction _)
    (measurable_finiteMatrixAction _), Measure.map_map (measurable_finiteMatrixAction _)
      (measurable_finiteMatrixAction _)]
  congr 1
  funext x
  have h := congrArg (fun M => M.mulVec x)
    (coloredStarEdgeProjection_channelLift d k C.rank c i (covarianceRankB C hC))
  simpa only [← Matrix.mulVec_mulVec] using h

/-- Endpoint reversal of every original edge passes to the exact-rank
support law. No independence among original channels is required. -/
theorem channelReducedLaw_edge_reversal (d k : ℕ)
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (μ : Measure ((Fin k × Fin d) → ℝ)) (c : ℝ) (i : Fin d)
    (hrev : Measure.map (edgeFlipLinear k)
      (Measure.map (fun x => (coloredStarEdgeProjection d k c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d k c i).mulVec x) μ) :
    Measure.map (edgeFlipLinear C.rank)
      (Measure.map (fun x => (coloredStarEdgeProjection d C.rank c i).mulVec x)
        (channelReducedLaw C hC μ)) =
      Measure.map (fun x => (coloredStarEdgeProjection d C.rank c i).mulVec x)
        (channelReducedLaw C hC μ) := by
  rw [channelReducedLaw_edge_law d k C hC μ c i]
  exact endpointChannelLift_reversal k C.rank (covarianceRankB C hC) _ hrev

end GaussianWave.BS
