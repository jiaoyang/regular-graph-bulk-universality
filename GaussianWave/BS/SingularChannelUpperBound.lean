import GaussianWave.BS.ChannelSupportReduction
import GaussianWave.BS.EmbeddingEntropy
import GaussianWave.BS.ColoredGaussianStrictness

/-!
# The actual intrinsic BS upper bound for singular channel covariance

All entropy witnesses live on the actual range of the channel covariance
factor, in its rank-dimensional coordinates. Ambient singular laws are never
assigned an ambient Lebesgue density. The support law, its exact-rank edge
laws, and the actual Gaussian references are constructed explicitly.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

theorem endpointChannelLift_mul {I J K : Type*} [Fintype J]
    (A : Matrix K J ℝ) (B : Matrix J I ℝ) :
    endpointChannelLift A * endpointChannelLift B = endpointChannelLift (A * B) := by
  ext p q
  rcases p with ⟨b, i⟩
  rcases q with ⟨b', j⟩
  cases b <;> cases b' <;>
    simp [endpointChannelLift, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
      ite_mul, mul_ite]

@[simp] theorem endpointChannelLift_one {I : Type*} [DecidableEq I] :
    endpointChannelLift (1 : Matrix I I ℝ) = 1 := by
  ext p q
  rcases p with ⟨b, i⟩
  rcases q with ⟨b', j⟩
  cases b <;> cases b' <;> simp [endpointChannelLift, Matrix.one_apply]

def singularEdgeL {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) :
    Matrix (Bool × Fin k) (Bool × Fin C.rank) ℝ := endpointChannelLift (covarianceRankL C hC)

def singularEdgeB {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) :
    Matrix (Bool × Fin C.rank) (Bool × Fin k) ℝ := endpointChannelLift (covarianceRankB C hC)

theorem singularEdge_left_inverse {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) :
    singularEdgeB C hC * singularEdgeL C hC = 1 := by
  rw [singularEdgeB, singularEdgeL, endpointChannelLift_mul, covarianceRankB_mul_L, endpointChannelLift_one]

abbrev SingularStarSupport (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) :=
  MatrixRange (channelSupportL C hC (Fin d))

abbrev SingularEdgeSupport {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) :=
  MatrixRange (singularEdgeL C hC)

/-- The actual whole-edge observation on the rank support. Its ambient
coordinates agree with the original k-channel observation, proved below. -/
def singularChannelEdge (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (i : Fin d) : SingularStarSupport d C hC →ₗ[ℝ] SingularEdgeSupport C hC :=
  (matrixRangeEquiv (singularEdgeL C hC) (singularEdgeB C hC) (singularEdge_left_inverse C hC)).toLinearMap.comp
    ((coloredStarEdgeProjection d C.rank c i).mulVecLin.comp
      (matrixRangeEquiv (channelSupportL C hC (Fin d)) (channelSupportB C hC (Fin d))
        (channelSupport_left_inverse C hC)).symm.toLinearMap)

theorem singularChannelEdge_coe (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (i : Fin d) (z : SingularStarSupport d C hC) :
    (singularChannelEdge d C hC c i z : (Bool × Fin k) → ℝ) =
      (coloredStarEdgeProjection d k c i).mulVec z := by
  let E := matrixRangeEquiv (channelSupportL C hC (Fin d)) (channelSupportB C hC (Fin d))
    (channelSupport_left_inverse C hC)
  let y := E.symm z
  have hz : (channelSupportL C hC (Fin d)).mulVec y = z := by
    change (E (E.symm z) : (Fin k × Fin d) → ℝ) = z
    rw [E.apply_symm_apply]
  have h := congrArg (fun M => M.mulVec y)
    (coloredStarEdgeProjection_channelLift d C.rank k c i (covarianceRankL C hC))
  simp only [← Matrix.mulVec_mulVec] at h
  change (singularEdgeL C hC).mulVec ((coloredStarEdgeProjection d C.rank c i).mulVec y) = _
  rw [← hz]
  exact h.symm

/-- The support edge is the actual original edge law in ambient coordinates. -/
theorem singularChannelEdge_ambient_law (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (i : Fin d) (N : Measure (SingularStarSupport d C hC)) :
    Measure.map (fun z : SingularEdgeSupport C hC => (z : (Bool × Fin k) → ℝ))
      (Measure.map (singularChannelEdge d C hC c i) N) =
      Measure.map (fun x => (coloredStarEdgeProjection d k c i).mulVec x)
        (Measure.map (fun z : SingularStarSupport d C hC => (z : (Fin k × Fin d) → ℝ)) N) := by
  rw [Measure.map_map measurable_subtype_coe (singularChannelEdge d C hC c i).continuous_of_finiteDimensional.measurable,
    Measure.map_map (measurable_finiteMatrixAction _) measurable_subtype_coe]
  congr 1
  funext z
  exact singularChannelEdge_coe d C hC c i z

/-- The exact-rank law of the actual support edge. -/
theorem singularChannelEdge_white_law (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (i : Fin d) (N : Measure (SingularStarSupport d C hC)) :
    embeddingWhiteLaw (singularEdgeL C hC) (singularEdgeB C hC) (singularEdge_left_inverse C hC)
      (Measure.map (singularChannelEdge d C hC c i) N) =
      Measure.map (fun y => (coloredStarEdgeProjection d C.rank c i).mulVec y)
        (embeddingWhiteLaw (channelSupportL C hC (Fin d)) (channelSupportB C hC (Fin d))
          (channelSupport_left_inverse C hC) N) := by
  rw [embeddingWhiteLaw, Measure.map_map
      (matrixRangeEquiv (singularEdgeL C hC) (singularEdgeB C hC) (singularEdge_left_inverse C hC)).symm.continuous.measurable
      (singularChannelEdge d C hC c i).continuous_of_finiteDimensional.measurable,
    embeddingWhiteLaw, Measure.map_map (measurable_finiteMatrixAction _)
      (matrixRangeEquiv (channelSupportL C hC (Fin d)) (channelSupportB C hC (Fin d))
        (channelSupport_left_inverse C hC)).symm.continuous.measurable]
  congr 1
  funext z
  change (matrixRangeEquiv (singularEdgeL C hC) (singularEdgeB C hC) (singularEdge_left_inverse C hC)).symm
    ((matrixRangeEquiv (singularEdgeL C hC) (singularEdgeB C hC) (singularEdge_left_inverse C hC))
      ((coloredStarEdgeProjection d C.rank c i).mulVec
        ((matrixRangeEquiv (channelSupportL C hC (Fin d)) (channelSupportB C hC (Fin d))
          (channelSupport_left_inverse C hC)).symm z))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- The actual white star law agrees with the already proved channel
support reduction of the actual ambient source law. -/
theorem singularStar_white_law (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (N : Measure (SingularStarSupport d C hC)) :
    embeddingWhiteLaw (channelSupportL C hC (Fin d)) (channelSupportB C hC (Fin d))
      (channelSupport_left_inverse C hC) N =
      channelReducedLaw C hC (Measure.map
        (fun z : SingularStarSupport d C hC => (z : (Fin k × Fin d) → ℝ)) N) :=
  embeddingWhiteLaw_eq_ambient_leftInverse _ _ _ N

def singularStarWhiteLaw (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (N : Measure (SingularStarSupport d C hC)) : Measure ((Fin C.rank × Fin d) → ℝ) :=
  embeddingWhiteLaw (channelSupportL C hC (Fin d)) (channelSupportB C hC (Fin d))
    (channelSupport_left_inverse C hC) N

instance singularStarWhiteLaw_isProbability (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (N : Measure (SingularStarSupport d C hC)) [IsProbabilityMeasure N] :
    IsProbabilityMeasure (singularStarWhiteLaw d C hC N) := by
  unfold singularStarWhiteLaw
  infer_instance

def singularStarGaussian (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) :=
  embeddingGaussian (channelSupportL C hC (Fin d)) (channelSupportB C hC (Fin d))
    (channelSupport_left_inverse C hC)

def singularEdgeGaussian {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) :=
  embeddingGaussian (singularEdgeL C hC) (singularEdgeB C hC) (singularEdge_left_inverse C hC)

def singularStarGaussianChartDensity (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (chart : SingularStarSupport d C hC ≃ₗ[ℝ] ((Fin C.rank × Fin d) → ℝ)) :=
  embeddingGaussianChartDensity (channelSupportL C hC (Fin d)) (channelSupportB C hC (Fin d))
    (channelSupport_left_inverse C hC) chart

def singularEdgeGaussianChartDensity {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (chart : SingularEdgeSupport C hC ≃ₗ[ℝ] ((Bool × Fin C.rank) → ℝ)) :=
  embeddingGaussianChartDensity (singularEdgeL C hC) (singularEdgeB C hC) (singularEdge_left_inverse C hC) chart

theorem singularChannelEdge_gaussian_law
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    Measure.map (singularChannelEdge d C hC c i) (singularStarGaussian d C hC) = singularEdgeGaussian C hC := by
  let E := matrixRangeEquiv (singularEdgeL C hC) (singularEdgeB C hC) (singularEdge_left_inverse C hC)
  apply MeasurableEquiv.map_measurableEquiv_injective E.symm.toHomeomorph.toMeasurableEquiv
  change embeddingWhiteLaw (singularEdgeL C hC) (singularEdgeB C hC) (singularEdge_left_inverse C hC)
      (Measure.map (singularChannelEdge d C hC c i) (singularStarGaussian d C hC)) =
    embeddingWhiteLaw (singularEdgeL C hC) (singularEdgeB C hC) (singularEdge_left_inverse C hC)
      (singularEdgeGaussian C hC)
  rw [singularChannelEdge_white_law, singularStarGaussian, singularEdgeGaussian,
    embeddingWhiteLaw_embeddingGaussian, embeddingWhiteLaw_embeddingGaussian,
    ← heatGaussian_half_eq_standardVector (Fin C.rank × Fin d),
    heatGaussian_map_orthonormal_rows _ (coloredStarEdgeProjection_mul_transpose d C.rank hd c hc i),
    heatGaussian_half_eq_standardVector (Bool × Fin C.rank)]

theorem singularStarGaussian_ambient_law (d : ℕ) {k : ℕ}
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) :
    Measure.map (fun z : SingularStarSupport d C hC => (z : (Fin k × Fin d) → ℝ))
      (singularStarGaussian d C hC) =
      gaussianCovarianceLaw (channelCovariance C (Fin d)) (channelCovariance_posSemidef C hC) := by
  rw [singularStarGaussian, embeddingGaussian_ambient_law]
  apply eq_gaussianCovarianceLaw
  intro t
  simpa only [channelSupport_gram] using linearImageGaussian_characteristic (channelSupportL C hC (Fin d)) t

def singularStarWhiteEntropyDensity
    (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (chart : SingularStarSupport d C hC ≃ₗ[ℝ] ((Fin C.rank × Fin d) → ℝ))
    (N : Measure (SingularStarSupport d C hC)) [IsProbabilityMeasure N]
    (f : FiniteEntropyDensity (Measure.map chart N)) : FiniteEntropyDensity (singularStarWhiteLaw d C hC N) :=
  f.embeddingWhite (channelSupportL C hC (Fin d)) (channelSupportB C hC (Fin d))
    (channelSupport_left_inverse C hC) chart N

def singularEdgeWhiteEntropyDensity
    (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ)
    (chart : SingularEdgeSupport C hC ≃ₗ[ℝ] ((Bool × Fin C.rank) → ℝ))
    (N : Measure (SingularStarSupport d C hC)) [IsProbabilityMeasure N]
    (i : Fin d) (g : FiniteEntropyDensity (Measure.map chart (Measure.map (singularChannelEdge d C hC c i) N))) :
    FiniteEntropyDensity (Measure.map (fun y => (coloredStarEdgeProjection d C.rank c i).mulVec y)
      (singularStarWhiteLaw d C hC N)) := by
  letI : IsProbabilityMeasure (Measure.map (singularChannelEdge d C hC c i) N) :=
    isProbabilityMeasure_map (singularChannelEdge d C hC c i).continuous_of_finiteDimensional.measurable.aemeasurable
  exact (g.embeddingWhite (singularEdgeL C hC) (singularEdgeB C hC)
    (singularEdge_left_inverse C hC) chart (Measure.map (singularChannelEdge d C hC c i) N)).cast
      (singularChannelEdge_white_law d C hC c i N).symm

theorem singularStar_relative_entropy_whitening
    (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (chart : SingularStarSupport d C hC ≃ₗ[ℝ] ((Fin C.rank × Fin d) → ℝ))
    (N : Measure (SingularStarSupport d C hC)) [IsProbabilityMeasure N]
    (f : FiniteEntropyDensity (Measure.map chart N)) :
    f.entropy - (singularStarGaussianChartDensity d C hC chart).entropy =
      (singularStarWhiteEntropyDensity d C hC chart N f).entropy -
        (standardVectorEntropyDensity (Fin C.rank × Fin d)).entropy :=
  embeddingGaussian_relative_entropy_cancellation _ _ _ chart N f

theorem singularEdge_relative_entropy_whitening
    (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ)
    (chart : SingularEdgeSupport C hC ≃ₗ[ℝ] ((Bool × Fin C.rank) → ℝ))
    (N : Measure (SingularStarSupport d C hC)) [IsProbabilityMeasure N]
    (i : Fin d) (g : FiniteEntropyDensity (Measure.map chart (Measure.map (singularChannelEdge d C hC c i) N))) :
    g.entropy - (singularEdgeGaussianChartDensity C hC chart).entropy =
      (singularEdgeWhiteEntropyDensity d C hC c chart N i g).entropy -
        (standardVectorEntropyDensity (Bool × Fin C.rank)).entropy := by
  letI : IsProbabilityMeasure (Measure.map (singularChannelEdge d C hC c i) N) :=
    isProbabilityMeasure_map (singularChannelEdge d C hC c i).continuous_of_finiteDimensional.measurable.aemeasurable
  exact embeddingGaussian_relative_entropy_cancellation _ _ _ chart _ g

/-- Exact cancellation of both intrinsic support Jacobians, before any
entropy inequality or Gaussian equality classification is used. -/
theorem singularFrameEntropy_whitening
    (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ)
    (starChart : SingularStarSupport d C hC ≃ₗ[ℝ] ((Fin C.rank × Fin d) → ℝ))
    (edgeChart : SingularEdgeSupport C hC ≃ₗ[ℝ] ((Bool × Fin C.rank) → ℝ))
    (N : Measure (SingularStarSupport d C hC)) [IsProbabilityMeasure N]
    (f : FiniteEntropyDensity (Measure.map starChart N))
    (g : ∀ i, FiniteEntropyDensity (Measure.map edgeChart (Measure.map (singularChannelEdge d C hC c i) N))) :
    (f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy) -
      ((singularStarGaussianChartDensity d C hC starChart).entropy -
        (d : ℝ) / 2 * (singularEdgeGaussianChartDensity C hC edgeChart).entropy) =
      initialFrameEntropy (singularStarWhiteEntropyDensity d C hC starChart N f)
        (fun i => singularEdgeWhiteEntropyDensity d C hC c edgeChart N i (g i)) := by
  have hGauss : (standardVectorEntropyDensity (Fin C.rank × Fin d)).entropy -
      (d : ℝ) / 2 * (standardVectorEntropyDensity (Bool × Fin C.rank)).entropy = 0 := by
    rw [standardVectorEntropyDensity_entropy, standardVectorEntropyDensity_entropy]
    simp only [gaussianEntropyValue, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      Nat.cast_mul, Nat.cast_ofNat, NNReal.coe_one]
    ring
  calc
    _ = (f.entropy - (singularStarGaussianChartDensity d C hC starChart).entropy) -
        (1 / 2 : ℝ) * ∑ i, ((g i).entropy - (singularEdgeGaussianChartDensity C hC edgeChart).entropy) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = _ := by
      rw [singularStar_relative_entropy_whitening]
      simp_rw [singularEdge_relative_entropy_whitening]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, initialFrameEntropy]
      linarith

theorem singularStarWhiteLaw_eq_standard_iff
    (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (N : Measure (SingularStarSupport d C hC)) :
    singularStarWhiteLaw d C hC N = standardVector (Fin C.rank × Fin d) ↔ N = singularStarGaussian d C hC := by
  constructor
  · intro hwhite
    rw [← matrixRangeEquiv_map_embeddingWhiteLaw (channelSupportL C hC (Fin d))
      (channelSupportB C hC (Fin d)) (channelSupport_left_inverse C hC) N]
    change Measure.map _ (singularStarWhiteLaw d C hC N) = _
    rw [hwhite]
    rfl
  · intro hN
    rw [hN]
    exact embeddingWhiteLaw_embeddingGaussian _ _ _

def singularStarAmbientLaw (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (N : Measure (SingularStarSupport d C hC)) : Measure ((Fin k × Fin d) → ℝ) :=
  Measure.map (fun z : SingularStarSupport d C hC => (z : (Fin k × Fin d) → ℝ)) N

def singularOriginalEdgeLaw (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (i : Fin d) (N : Measure (SingularStarSupport d C hC)) : Measure ((Bool × Fin k) → ℝ) :=
  Measure.map (fun x => (coloredStarEdgeProjection d k c i).mulVec x) (singularStarAmbientLaw d C hC N)

theorem singularStarWhiteLaw_identitySecondMoments
    (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (N : Measure (SingularStarSupport d C hC))
    (hfinite : Integrable (squareRadius (I := Fin k × Fin d)) (singularStarAmbientLaw d C hC N))
    (hmom : HasSecondMoments (singularStarAmbientLaw d C hC N) (channelCovariance C (Fin d))) :
    HasIdentitySecondMoments (singularStarWhiteLaw d C hC N) := by
  rw [singularStarWhiteLaw, singularStar_white_law]
  exact channelReducedLaw_identitySecondMoments C hC _ hfinite hmom

theorem singularStarWhiteLaw_edge_reversal
    (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ)
    (N : Measure (SingularStarSupport d C hC)) (i : Fin d)
    (hrev : Measure.map (edgeFlipLinear k) (singularOriginalEdgeLaw d C hC c i N) =
      singularOriginalEdgeLaw d C hC c i N) :
    Measure.map (edgeFlipLinear C.rank)
      (Measure.map (fun y => (coloredStarEdgeProjection d C.rank c i).mulVec y) (singularStarWhiteLaw d C hC N)) =
      Measure.map (fun y => (coloredStarEdgeProjection d C.rank c i).mulVec y) (singularStarWhiteLaw d C hC N) := by
  rw [singularStarWhiteLaw, singularStar_white_law]
  exact channelReducedLaw_edge_reversal d k C hC (singularStarAmbientLaw d C hC N) c i hrev

theorem singularStarWhiteLaw_neighbor_permutation
    (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (N : Measure (SingularStarSupport d C hC)) (p : Equiv.Perm (Fin d))
    (hperm : Measure.map (spatialPermutationMap p) (singularStarAmbientLaw d C hC N) =
      singularStarAmbientLaw d C hC N) :
    Measure.map (spatialPermutationMap p) (singularStarWhiteLaw d C hC N) = singularStarWhiteLaw d C hC N := by
  rw [singularStarWhiteLaw, singularStar_white_law]
  exact channelReducedLaw_spatialPermutation C hC (singularStarAmbientLaw d C hC N) p hperm

/-- The genuine intrinsic support entropy upper bound for every positive
semidefinite channel covariance, including zero rank. Original whole-edge
reversal is the sole symmetry needed for this averaged-edge inequality.
Every entropy is taken in rank support coordinates, never in singular
ambient channel coordinates. -/
theorem singular_channel_entropy_upper
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (starChart : SingularStarSupport d C hC ≃ₗ[ℝ] ((Fin C.rank × Fin d) → ℝ))
    (edgeChart : SingularEdgeSupport C hC ≃ₗ[ℝ] ((Bool × Fin C.rank) → ℝ))
    (N : Measure (SingularStarSupport d C hC)) [IsProbabilityMeasure N]
    (hfinite : Integrable (squareRadius (I := Fin k × Fin d)) (singularStarAmbientLaw d C hC N))
    (hmom : HasSecondMoments (singularStarAmbientLaw d C hC N) (channelCovariance C (Fin d)))
    (f : FiniteEntropyDensity (Measure.map starChart N))
    (g : ∀ i, FiniteEntropyDensity (Measure.map edgeChart (Measure.map (singularChannelEdge d C hC c i) N)))
    (hrev : ∀ i, Measure.map (edgeFlipLinear k) (singularOriginalEdgeLaw d C hC c i N) =
      singularOriginalEdgeLaw d C hC c i N) :
    f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy ≤
      (singularStarGaussianChartDensity d C hC starChart).entropy -
        (d : ℝ) / 2 * (singularEdgeGaussianChartDensity C hC edgeChart).entropy := by
  have hwhite := singularStarWhiteLaw_identitySecondMoments d C hC N hfinite hmom
  have hupper := colored_star_entropy_upper d C.rank hd c hbulk (singularStarWhiteLaw d C hC N)
    (integrable_squareRadius_of_identitySecondMoments _ hwhite) hwhite
    (singularStarWhiteEntropyDensity d C hC starChart N f)
    (fun i => singularEdgeWhiteEntropyDensity d C hC c edgeChart N i (g i))
    (fun i => singularStarWhiteLaw_edge_reversal d C hC c N i (hrev i))
  have hrel : initialFrameEntropy (singularStarWhiteEntropyDensity d C hC starChart N f)
      (fun i => singularEdgeWhiteEntropyDensity d C hC c edgeChart N i (g i)) ≤ 0 := sub_nonpos.mpr hupper
  rw [← singularFrameEntropy_whitening d C hC c starChart edgeChart N f g] at hrel
  exact sub_nonpos.mp hrel

/-- Gaussian equality classification on the actual rank support. The
unknown source law may have arbitrary channel dependence and the channel
covariance may be singular. Equality identifies the actual embedded Gaussian
probability law, whose ambient covariance is proved to be C tensor I. -/
theorem singular_channel_entropy_equality_iff_gaussian
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (starChart : SingularStarSupport d C hC ≃ₗ[ℝ] ((Fin C.rank × Fin d) → ℝ))
    (edgeChart : SingularEdgeSupport C hC ≃ₗ[ℝ] ((Bool × Fin C.rank) → ℝ))
    (N : Measure (SingularStarSupport d C hC)) [IsProbabilityMeasure N]
    (hfinite : Integrable (squareRadius (I := Fin k × Fin d)) (singularStarAmbientLaw d C hC N))
    (hmom : HasSecondMoments (singularStarAmbientLaw d C hC N) (channelCovariance C (Fin d)))
    (f : FiniteEntropyDensity (Measure.map starChart N))
    (g : ∀ i, FiniteEntropyDensity (Measure.map edgeChart (Measure.map (singularChannelEdge d C hC c i) N)))
    (hrev : ∀ i, Measure.map (edgeFlipLinear k) (singularOriginalEdgeLaw d C hC c i N) =
      singularOriginalEdgeLaw d C hC c i N)
    (hperm : ∀ p : Equiv.Perm (Fin d), Measure.map (spatialPermutationMap p)
      (singularStarAmbientLaw d C hC N) = singularStarAmbientLaw d C hC N) :
    (f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy =
      (singularStarGaussianChartDensity d C hC starChart).entropy -
        (d : ℝ) / 2 * (singularEdgeGaussianChartDensity C hC edgeChart).entropy) ↔
      N = singularStarGaussian d C hC := by
  have hwhite := singularStarWhiteLaw_identitySecondMoments d C hC N hfinite hmom
  rw [← sub_eq_zero, singularFrameEntropy_whitening d C hC c starChart edgeChart N f g]
  exact (colored_star_entropy_equality_iff_standardVector d C.rank hd c hbulk
    (singularStarWhiteLaw d C hC N) hwhite (singularStarWhiteEntropyDensity d C hC starChart N f)
    (fun i => singularEdgeWhiteEntropyDensity d C hC c edgeChart N i (g i))
    (fun i => singularStarWhiteLaw_edge_reversal d C hC c N i (hrev i))
    (fun p => singularStarWhiteLaw_neighbor_permutation d C hC N p (hperm p))).trans
      (singularStarWhiteLaw_eq_standard_iff d C hC N)

end GaussianWave.BS
