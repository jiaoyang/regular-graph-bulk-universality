import GaussianWave.BS.SingularChannelUpperBound
import GaussianWave.BS.ColoredPhysicalUpperBound
import GaussianWave.BS.EmbeddedFrameUpperBound

/-!
# Singular channel covariance in actual physical star coordinates

The total full-column embedding is the actual tensor product of the channel
support factor and the physical Gaussian-wave star factor. All entropies are
computed on its genuine range and the genuine whole-edge ranges.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Kronecker
namespace GaussianWave.BS

def singularPhysicalL (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ) :
    Matrix (Fin k × Fin (d + 1)) (Fin C.rank × Fin d) ℝ :=
  Matrix.kronecker (covarianceRankL C hC) (physicalStarMatrix d c)

def singularPhysicalB (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ) :
    Matrix (Fin C.rank × Fin d) (Fin k × Fin (d + 1)) ℝ :=
  Matrix.kronecker (covarianceRankB C hC) (physicalStarInverseMatrix d c)

def singularPhysicalCovariance (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (c : ℝ) :
    Matrix (Fin k × Fin (d + 1)) (Fin k × Fin (d + 1)) ℝ :=
  Matrix.kronecker C (RegularEigenData.starWaveCovariance d ((d : ℝ) * c))

theorem singularPhysical_left_inverse
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (hc : |c| < 1) : singularPhysicalB d C hC c * singularPhysicalL d C hC c = 1 := by
  change (covarianceRankB C hC ⊗ₖ physicalStarInverseMatrix d c) *
    (covarianceRankL C hC ⊗ₖ physicalStarMatrix d c) = 1
  rw [← Matrix.mul_kronecker_mul,
    covarianceRankB_mul_L, physicalStarInverseMatrix_left_inverse d hd c hc, Matrix.one_kronecker_one]

theorem singularPhysical_gram
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (hc : |c| < 1) :
    singularPhysicalL d C hC c * (singularPhysicalL d C hC c).transpose = singularPhysicalCovariance d C c := by
  change (covarianceRankL C hC ⊗ₖ physicalStarMatrix d c) *
    (covarianceRankL C hC).transpose ⊗ₖ (physicalStarMatrix d c).transpose = _
  rw [← Matrix.mul_kronecker_mul, covarianceRankL_mul_transpose, physicalStarMatrix_gram d hd c hc]
  rfl

theorem singularPhysicalL_channel_composition
    (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ) :
    singularPhysicalL d C hC c = channelLift (covarianceRankL C hC) (Fin (d + 1)) *
      coloredPhysicalStarMatrix d C.rank c := by
  ext p q
  rcases p with ⟨a, i⟩
  rcases q with ⟨b, j⟩
  simp [singularPhysicalL, Matrix.mul_apply, channelLift, coloredPhysicalStarMatrix,
    channelLiftMatrix, Fintype.sum_prod_type, ite_mul, mul_ite]

theorem channelLift_physicalEdgeCoordinates
    (d k r : ℕ) (A : Matrix (Fin k) (Fin r) ℝ) (i : Fin d)
    (z : (Fin r × Fin (d + 1)) → ℝ) :
    coloredPhysicalEdgeCoordinates i ((channelLift A (Fin (d + 1))).mulVec z) =
      (endpointChannelLift A).mulVec (coloredPhysicalEdgeCoordinates i z) := by
  ext p
  rcases p with ⟨b, a⟩
  cases b <;> simp [coloredPhysicalEdgeCoordinates, physicalEdgeCoordinates,
    channelLift_mulVec, endpointChannelLift_mulVec]

def singularPhysicalEdgeL {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ) :
    Matrix (Bool × Fin k) (Bool × Fin C.rank) ℝ :=
  singularEdgeL C hC * coloredPhysicalEdgeMatrix C.rank c

def singularPhysicalEdgeB {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ) :
    Matrix (Bool × Fin C.rank) (Bool × Fin k) ℝ :=
  (coloredPhysicalEdgeMatrix C.rank c)⁻¹ * singularEdgeB C hC

theorem singularPhysicalEdge_left_inverse {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (hc : |c| < 1) : singularPhysicalEdgeB C hC c * singularPhysicalEdgeL C hC c = 1 := by
  calc
    _ = (coloredPhysicalEdgeMatrix C.rank c)⁻¹ * (singularEdgeB C hC * singularEdgeL C hC) *
        coloredPhysicalEdgeMatrix C.rank c := by simp only [singularPhysicalEdgeB, singularPhysicalEdgeL, Matrix.mul_assoc]
    _ = 1 := by
      rw [singularEdge_left_inverse, Matrix.mul_one,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (coloredPhysicalEdgeMatrix_det_ne_zero C.rank c hc))]

/-- Exact original physical endpoint observation of the total embedding. -/
theorem singularPhysicalL_edge
    (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (hc : |c| < 1) (i : Fin d) (y : (Fin C.rank × Fin d) → ℝ) :
    coloredPhysicalEdgeCoordinates i ((singularPhysicalL d C hC c).mulVec y) =
      (singularPhysicalEdgeL C hC c).mulVec ((coloredStarEdgeProjection d C.rank c i).mulVec y) := by
  rw [singularPhysicalL_channel_composition, ← Matrix.mulVec_mulVec,
    channelLift_physicalEdgeCoordinates]
  change (singularEdgeL C hC).mulVec (coloredPhysicalEdgeCoordinates i (coloredPhysicalStarMap d C.rank c y)) = _
  rw [coloredPhysicalStarMap_edge d C.rank c hc i, Matrix.mulVec_mulVec]
  rfl

theorem singularPhysicalEdgeL_flip {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (x : (Bool × Fin C.rank) → ℝ) :
    (singularPhysicalEdgeL C hC c).mulVec (edgeFlipLinear C.rank x) =
      edgeFlipLinear k ((singularPhysicalEdgeL C hC c).mulVec x) := by
  rw [singularPhysicalEdgeL, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    coloredPhysicalEdgeMatrix_commutes_edgeFlip]
  exact endpointChannelLift_edgeFlip C.rank k (covarianceRankL C hC) _

theorem channelLift_physicalPermutation
    (d k r : ℕ) (A : Matrix (Fin k) (Fin r) ℝ) (p : Equiv.Perm (Fin d))
    (z : (Fin r × Fin (d + 1)) → ℝ) :
    (channelLift A (Fin (d + 1))).mulVec (coloredPhysicalStarPermutation p z) =
      coloredPhysicalStarPermutation p ((channelLift A (Fin (d + 1))).mulVec z) := by
  ext q
  rcases q with ⟨a, j⟩
  refine Fin.cases ?_ (fun i => ?_) j <;>
    simp [channelLift_mulVec, coloredPhysicalStarPermutation, physicalStarPermutation]

theorem singularPhysicalL_permutation
    (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ)
    (p : Equiv.Perm (Fin d)) (y : (Fin C.rank × Fin d) → ℝ) :
    (singularPhysicalL d C hC c).mulVec (spatialPermutationMap p y) =
      coloredPhysicalStarPermutation p ((singularPhysicalL d C hC c).mulVec y) := by
  rw [singularPhysicalL_channel_composition, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change (channelLift (covarianceRankL C hC) (Fin (d + 1))).mulVec
      (coloredPhysicalStarMap d C.rank c (spatialPermutationMap p y)) = _
  have hp : coloredPhysicalStarMap d C.rank c (spatialPermutationMap p y) =
      coloredPhysicalStarPermutation p (coloredPhysicalStarMap d C.rank c y) :=
    coloredPhysicalStarMap_permutation c p y
  rw [hp, channelLift_physicalPermutation]
  rfl

theorem fullColumn_leftInverse_map
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1) (μ : Measure (J → ℝ)) :
    Measure.map (fun x => B.mulVec x) (Measure.map (fun y => L.mulVec y) μ) = μ := by
  rw [Measure.map_map (measurable_finiteMatrixAction B) (measurable_finiteMatrixAction L)]
  calc
    _ = Measure.map id μ := by
      congr 1
      funext y
      change B.mulVec (L.mulVec y) = y
      rw [Matrix.mulVec_mulVec, hBL, Matrix.one_mulVec]
    _ = μ := Measure.map_id

theorem fullColumn_map_injective
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1) :
    Function.Injective (Measure.map (fun y : J → ℝ => L.mulVec y)) := by
  intro μ ν h
  have he := congrArg (Measure.map (fun x => B.mulVec x)) h
  simpa only [fullColumn_leftInverse_map L B hBL] using he

theorem embedding_ambient_reconstruction
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1) (N : Measure (MatrixRange L)) :
    Measure.map (fun y => L.mulVec y) (embeddingWhiteLaw L B hBL N) =
      Measure.map (fun z : MatrixRange L => (z : I → ℝ)) N := by
  calc
    _ = Measure.map (fun z : MatrixRange L => (z : I → ℝ))
        (Measure.map (matrixRangeEquiv L B hBL) (embeddingWhiteLaw L B hBL N)) := by
      rw [Measure.map_map measurable_subtype_coe (matrixRangeEquiv L B hBL).continuous.measurable]
      rfl
    _ = _ := by rw [matrixRangeEquiv_map_embeddingWhiteLaw]

abbrev SingularPhysicalSupport (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ) :=
  MatrixRange (singularPhysicalL d C hC c)

def singularPhysicalAmbientLaw (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ)
    (N : Measure (SingularPhysicalSupport d C hC c)) : Measure ((Fin k × Fin (d + 1)) → ℝ) :=
  Measure.map (fun z : SingularPhysicalSupport d C hC c => (z : (Fin k × Fin (d + 1)) → ℝ)) N

def singularPhysicalWhiteLaw (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (hc : |c| < 1) (N : Measure (SingularPhysicalSupport d C hC c)) :=
  embeddingWhiteLaw (singularPhysicalL d C hC c) (singularPhysicalB d C hC c)
    (singularPhysical_left_inverse d hd C hC c hc) N

instance singularPhysicalWhiteLaw_isProbability
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (hc : |c| < 1) (N : Measure (SingularPhysicalSupport d C hC c)) [IsProbabilityMeasure N] :
    IsProbabilityMeasure (singularPhysicalWhiteLaw d hd C hC c hc N) := by
  unfold singularPhysicalWhiteLaw
  infer_instance

theorem singularPhysicalWhiteLaw_identitySecondMoments
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (hc : |c| < 1) (N : Measure (SingularPhysicalSupport d C hC c))
    (hfinite : Integrable (squareRadius (I := Fin k × Fin (d + 1))) (singularPhysicalAmbientLaw d C hC c N))
    (hmom : HasSecondMoments (singularPhysicalAmbientLaw d C hC c N) (singularPhysicalCovariance d C c)) :
    HasIdentitySecondMoments (singularPhysicalWhiteLaw d hd C hC c hc N) := by
  have hgram : HasSecondMoments (singularPhysicalAmbientLaw d C hC c N)
      (singularPhysicalL d C hC c * (singularPhysicalL d C hC c).transpose) := by
    rw [singularPhysical_gram d hd C hC c hc]
    exact hmom
  have h := identitySecondMoments_of_gram_leftInverse _ hfinite (singularPhysicalL d C hC c)
    (singularPhysicalB d C hC c) hgram (singularPhysical_left_inverse d hd C hC c hc)
  change HasIdentitySecondMoments (Measure.map (fun x => (singularPhysicalB d C hC c).mulVec x)
    (Measure.map (fun z : SingularPhysicalSupport d C hC c => (z : (Fin k × Fin (d + 1)) → ℝ)) N)) at h
  rw [← embeddingWhiteLaw_eq_ambient_leftInverse] at h
  exact h

def singularPhysicalOriginalEdgeLaw (d : ℕ) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (i : Fin d) (N : Measure (SingularPhysicalSupport d C hC c)) :=
  Measure.map (coloredPhysicalEdgeCoordinates i) (singularPhysicalAmbientLaw d C hC c N)

theorem singularPhysicalOriginalEdge_white_law
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (hc : |c| < 1) (i : Fin d) (N : Measure (SingularPhysicalSupport d C hC c)) :
    singularPhysicalOriginalEdgeLaw d C hC c i N =
      Measure.map (fun x => (singularPhysicalEdgeL C hC c).mulVec x)
        (Measure.map (fun y => (coloredStarEdgeProjection d C.rank c i).mulVec y)
          (singularPhysicalWhiteLaw d hd C hC c hc N)) := by
  unfold singularPhysicalOriginalEdgeLaw singularPhysicalAmbientLaw
  rw [← embedding_ambient_reconstruction (singularPhysicalL d C hC c) (singularPhysicalB d C hC c)
    (singularPhysical_left_inverse d hd C hC c hc) N,
    Measure.map_map (measurable_coloredPhysicalEdgeCoordinates i) (measurable_finiteMatrixAction _),
    Measure.map_map (measurable_finiteMatrixAction _) (measurable_finiteMatrixAction _)]
  congr 1
  funext y
  exact singularPhysicalL_edge d C hC c hc i y

theorem singularPhysicalWhiteLaw_edge_reversal
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (hc : |c| < 1) (i : Fin d) (N : Measure (SingularPhysicalSupport d C hC c))
    (hrev : Measure.map (edgeFlipLinear k) (singularPhysicalOriginalEdgeLaw d C hC c i N) =
      singularPhysicalOriginalEdgeLaw d C hC c i N) :
    Measure.map (edgeFlipLinear C.rank)
      (Measure.map (fun y => (coloredStarEdgeProjection d C.rank c i).mulVec y)
        (singularPhysicalWhiteLaw d hd C hC c hc N)) =
      Measure.map (fun y => (coloredStarEdgeProjection d C.rank c i).mulVec y)
        (singularPhysicalWhiteLaw d hd C hC c hc N) := by
  apply fullColumn_map_injective (singularPhysicalEdgeL C hC c) (singularPhysicalEdgeB C hC c)
    (singularPhysicalEdge_left_inverse C hC c hc)
  calc
    _ = Measure.map (edgeFlipLinear k)
        (Measure.map (fun x => (singularPhysicalEdgeL C hC c).mulVec x)
          (Measure.map (fun y => (coloredStarEdgeProjection d C.rank c i).mulVec y)
            (singularPhysicalWhiteLaw d hd C hC c hc N))) := by
      rw [Measure.map_map (measurable_finiteMatrixAction _) (edgeFlipLinear C.rank).continuous.measurable,
        Measure.map_map (edgeFlipLinear k).continuous.measurable (measurable_finiteMatrixAction _)]
      congr 1
      funext x
      exact singularPhysicalEdgeL_flip C hC c x
    _ = _ := by rw [← singularPhysicalOriginalEdge_white_law d hd C hC c hc i N, hrev]

theorem singularPhysicalWhiteLaw_neighbor_permutation
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (hc : |c| < 1) (N : Measure (SingularPhysicalSupport d C hC c)) (p : Equiv.Perm (Fin d))
    (hperm : Measure.map (coloredPhysicalStarPermutation p) (singularPhysicalAmbientLaw d C hC c N) =
      singularPhysicalAmbientLaw d C hC c N) :
    Measure.map (spatialPermutationMap p) (singularPhysicalWhiteLaw d hd C hC c hc N) =
      singularPhysicalWhiteLaw d hd C hC c hc N := by
  apply fullColumn_map_injective (singularPhysicalL d C hC c) (singularPhysicalB d C hC c)
    (singularPhysical_left_inverse d hd C hC c hc)
  calc
    _ = Measure.map (coloredPhysicalStarPermutation p)
        (Measure.map (fun y => (singularPhysicalL d C hC c).mulVec y)
          (singularPhysicalWhiteLaw d hd C hC c hc N)) := by
      rw [Measure.map_map (measurable_finiteMatrixAction _) (measurable_spatialPermutationMap _ _ p),
        Measure.map_map (measurable_coloredPhysicalStarPermutation p) (measurable_finiteMatrixAction _)]
      congr 1
      funext y
      exact singularPhysicalL_permutation d C hC c p y
    _ = _ := by
      change Measure.map (coloredPhysicalStarPermutation p)
        (Measure.map (fun y => (singularPhysicalL d C hC c).mulVec y)
          (embeddingWhiteLaw _ _ _ N)) = _
      rw [embedding_ambient_reconstruction]
      change Measure.map (coloredPhysicalStarPermutation p) (singularPhysicalAmbientLaw d C hC c N) = _
      rw [hperm]
      exact (embedding_ambient_reconstruction _ _ _ N).symm

abbrev SingularPhysicalEdgeSupport {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ) :=
  MatrixRange (singularPhysicalEdgeL C hC c)

def singularPhysicalSupportedEdge
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    SingularPhysicalSupport d C hC c →ₗ[ℝ] SingularPhysicalEdgeSupport C hC c :=
  embeddedColoredEdge d C.rank (singularPhysicalL d C hC c) (singularPhysicalB d C hC c)
    (singularPhysical_left_inverse d hd C hC c hc) (singularPhysicalEdgeL C hC c) (singularPhysicalEdgeB C hC c)
    (singularPhysicalEdge_left_inverse C hC c hc) c i

/-- The intrinsic supported edge is exactly the original physical endpoint
law after its natural inclusion in the ambient endpoint coordinates. -/
theorem singularPhysicalSupportedEdge_ambient_law
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (hc : |c| < 1) (i : Fin d) (N : Measure (SingularPhysicalSupport d C hC c)) :
    Measure.map (fun z : SingularPhysicalEdgeSupport C hC c => (z : (Bool × Fin k) → ℝ))
      (Measure.map (singularPhysicalSupportedEdge d hd C hC c hc i) N) =
        singularPhysicalOriginalEdgeLaw d C hC c i N := by
  exact embeddedColoredEdge_ambient_law d C.rank (singularPhysicalL d C hC c) (singularPhysicalB d C hC c)
    (singularPhysical_left_inverse d hd C hC c hc) (singularPhysicalEdgeL C hC c) (singularPhysicalEdgeB C hC c)
    (singularPhysicalEdge_left_inverse C hC c hc) c i (coloredPhysicalEdgeCoordinates i)
    (measurable_coloredPhysicalEdgeCoordinates i) (singularPhysicalL_edge d C hC c hc i) N

def singularPhysicalGaussian
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ) (hc : |c| < 1) :=
  embeddingGaussian (singularPhysicalL d C hC c) (singularPhysicalB d C hC c)
    (singularPhysical_left_inverse d hd C hC c hc)

def singularPhysicalStarGaussianChartDensity
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ) (hc : |c| < 1)
    (chart : SingularPhysicalSupport d C hC c ≃ₗ[ℝ] ((Fin C.rank × Fin d) → ℝ)) :=
  embeddingGaussianChartDensity (singularPhysicalL d C hC c) (singularPhysicalB d C hC c)
    (singularPhysical_left_inverse d hd C hC c hc) chart

def singularPhysicalEdgeGaussianChartDensity
    {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ) (hc : |c| < 1)
    (chart : SingularPhysicalEdgeSupport C hC c ≃ₗ[ℝ] ((Bool × Fin C.rank) → ℝ)) :=
  embeddingGaussianChartDensity (singularPhysicalEdgeL C hC c) (singularPhysicalEdgeB C hC c)
    (singularPhysicalEdge_left_inverse C hC c hc) chart

theorem singularPhysicalCovariance_posSemidef
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ) (hc : |c| < 1) :
    (singularPhysicalCovariance d C c).PosSemidef := by
  rw [← singularPhysical_gram d hd C hC c hc]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (singularPhysicalL d C hC c)

/-- The actual Gaussian reference has precisely the physical covariance
C tensor the canonical Gaussian-wave star covariance, including singular C. -/
theorem singularPhysicalGaussian_ambient_law
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (c : ℝ) (hc : |c| < 1) :
    singularPhysicalAmbientLaw d C hC c (singularPhysicalGaussian d hd C hC c hc) =
      gaussianCovarianceLaw (singularPhysicalCovariance d C c) (singularPhysicalCovariance_posSemidef d hd C hC c hc) := by
  rw [singularPhysicalAmbientLaw, singularPhysicalGaussian, embeddingGaussian_ambient_law]
  apply eq_gaussianCovarianceLaw
  intro t
  simpa only [singularPhysical_gram d hd C hC c hc] using
    linearImageGaussian_characteristic (singularPhysicalL d C hC c) t

theorem singularPhysicalSupportedEdge_gaussian_law
    (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    Measure.map (singularPhysicalSupportedEdge d hd C hC c hc i) (singularPhysicalGaussian d hd C hC c hc) =
      embeddingGaussian (singularPhysicalEdgeL C hC c) (singularPhysicalEdgeB C hC c)
        (singularPhysicalEdge_left_inverse C hC c hc) :=
  embeddedColoredEdge_gaussian_law d C.rank (singularPhysicalL d C hC c) (singularPhysicalB d C hC c)
    (singularPhysical_left_inverse d hd C hC c hc) (singularPhysicalEdgeL C hC c) (singularPhysicalEdgeB C hC c)
    (singularPhysicalEdge_left_inverse C hC c hc) hd c hc i

/-- The genuine physical entropy upper inequality for arbitrary positive
semidefinite channel covariance. Every entropy is computed on the actual
rank-dimensional physical support. The only symmetry needed here is
simultaneous reversal of each actual whole physical edge law. -/
theorem singular_physical_entropy_upper
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (starChart : SingularPhysicalSupport d C hC c ≃ₗ[ℝ] ((Fin C.rank × Fin d) → ℝ))
    (edgeChart : SingularPhysicalEdgeSupport C hC c ≃ₗ[ℝ] ((Bool × Fin C.rank) → ℝ))
    (N : Measure (SingularPhysicalSupport d C hC c)) [IsProbabilityMeasure N]
    (hfinite : Integrable (squareRadius (I := Fin k × Fin (d + 1))) (singularPhysicalAmbientLaw d C hC c N))
    (hmom : HasSecondMoments (singularPhysicalAmbientLaw d C hC c N) (singularPhysicalCovariance d C c))
    (f : FiniteEntropyDensity (Measure.map starChart N))
    (g : ∀ i, FiniteEntropyDensity (Measure.map edgeChart
      (Measure.map (singularPhysicalSupportedEdge d (by omega) C hC c (bulk_rho_lower d hd c hbulk).1 i) N)))
    (hrev : ∀ i, Measure.map (edgeFlipLinear k) (singularPhysicalOriginalEdgeLaw d C hC c i N) =
      singularPhysicalOriginalEdgeLaw d C hC c i N) :
    f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy ≤
      (singularPhysicalStarGaussianChartDensity d (by omega) C hC c (bulk_rho_lower d hd c hbulk).1 starChart).entropy -
        (d : ℝ) / 2 * (singularPhysicalEdgeGaussianChartDensity C hC c (bulk_rho_lower d hd c hbulk).1 edgeChart).entropy := by
  let hd2 : 2 ≤ d := by omega
  let hc := (bulk_rho_lower d hd c hbulk).1
  exact embedded_frame_entropy_upper d C.rank (singularPhysicalL d C hC c) (singularPhysicalB d C hC c)
    (singularPhysical_left_inverse d hd2 C hC c hc) (singularPhysicalEdgeL C hC c) (singularPhysicalEdgeB C hC c)
    (singularPhysicalEdge_left_inverse C hC c hc) hd c hbulk starChart edgeChart N f g
    (singularPhysicalWhiteLaw_identitySecondMoments d hd2 C hC c hc N hfinite hmom)
    (fun i => singularPhysicalWhiteLaw_edge_reversal d hd2 C hC c hc i N (hrev i))

/-- Full joint Gaussian equality classification for the actual singular
physical support. Rank zero and arbitrary dependence among the input
channels are included. All normalization and symmetry inputs are supplied
on the original physical laws, then proved for the reduced law. -/
theorem singular_physical_entropy_equality_iff_gaussian
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (starChart : SingularPhysicalSupport d C hC c ≃ₗ[ℝ] ((Fin C.rank × Fin d) → ℝ))
    (edgeChart : SingularPhysicalEdgeSupport C hC c ≃ₗ[ℝ] ((Bool × Fin C.rank) → ℝ))
    (N : Measure (SingularPhysicalSupport d C hC c)) [IsProbabilityMeasure N]
    (hfinite : Integrable (squareRadius (I := Fin k × Fin (d + 1))) (singularPhysicalAmbientLaw d C hC c N))
    (hmom : HasSecondMoments (singularPhysicalAmbientLaw d C hC c N) (singularPhysicalCovariance d C c))
    (f : FiniteEntropyDensity (Measure.map starChart N))
    (g : ∀ i, FiniteEntropyDensity (Measure.map edgeChart
      (Measure.map (singularPhysicalSupportedEdge d (by omega) C hC c (bulk_rho_lower d hd c hbulk).1 i) N)))
    (hrev : ∀ i, Measure.map (edgeFlipLinear k) (singularPhysicalOriginalEdgeLaw d C hC c i N) =
      singularPhysicalOriginalEdgeLaw d C hC c i N)
    (hperm : ∀ p : Equiv.Perm (Fin d), Measure.map (coloredPhysicalStarPermutation p)
      (singularPhysicalAmbientLaw d C hC c N) = singularPhysicalAmbientLaw d C hC c N) :
    (f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy =
      (singularPhysicalStarGaussianChartDensity d (by omega) C hC c (bulk_rho_lower d hd c hbulk).1 starChart).entropy -
        (d : ℝ) / 2 * (singularPhysicalEdgeGaussianChartDensity C hC c (bulk_rho_lower d hd c hbulk).1 edgeChart).entropy) ↔
      N = singularPhysicalGaussian d (by omega) C hC c (bulk_rho_lower d hd c hbulk).1 := by
  let hd2 : 2 ≤ d := by omega
  let hc := (bulk_rho_lower d hd c hbulk).1
  exact embedded_frame_entropy_equality_iff_gaussian d C.rank (singularPhysicalL d C hC c) (singularPhysicalB d C hC c)
    (singularPhysical_left_inverse d hd2 C hC c hc) (singularPhysicalEdgeL C hC c) (singularPhysicalEdgeB C hC c)
    (singularPhysicalEdge_left_inverse C hC c hc) hd c hbulk starChart edgeChart N f g
    (singularPhysicalWhiteLaw_identitySecondMoments d hd2 C hC c hc N hfinite hmom)
    (fun i => singularPhysicalWhiteLaw_edge_reversal d hd2 C hC c hc i N (hrev i))
    (fun p => singularPhysicalWhiteLaw_neighbor_permutation d hd2 C hC c hc N p (hperm p))

end GaussianWave.BS
