import GaussianWave.BS.EmbeddingEntropy
import GaussianWave.BS.ColoredGaussianStrictness
import GaussianWave.BS.SecondMomentTransport

/-!
# Intrinsic colored-frame entropy transport for full-column embeddings

The ambient star and edge embeddings may have singular covariance. All
density witnesses live in actual coordinates on their ranges. The proved
Jacobian cancellation transports the colored upper bound and joint Gaussian
equality theorem; the generic helpers expose ordinary white moment and
symmetry inputs for subsequent source-coordinate adapters.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

section EmbeddedFrame
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable (d r : ℕ)
variable (L : Matrix I (Fin r × Fin d) ℝ) (B : Matrix (Fin r × Fin d) I ℝ) (hBL : B * L = 1)
variable (G : Matrix J (Bool × Fin r) ℝ) (H : Matrix (Bool × Fin r) J ℝ) (hHG : H * G = 1)

/-- Actual intrinsic whole-edge observation on the embedded star range. -/
def embeddedColoredEdge (c : ℝ) (i : Fin d) : MatrixRange L →ₗ[ℝ] MatrixRange G :=
  (matrixRangeEquiv G H hHG).toLinearMap.comp
    ((coloredStarEdgeProjection d r c i).mulVecLin.comp
      (matrixRangeEquiv L B hBL).symm.toLinearMap)

@[simp] theorem embeddedColoredEdge_coe (c : ℝ) (i : Fin d) (z : MatrixRange L) :
    (embeddedColoredEdge d r L B hBL G H hHG c i z : J → ℝ) =
      G.mulVec ((coloredStarEdgeProjection d r c i).mulVec (B.mulVec z)) := rfl

/-- Any actual ambient edge map which intertwines with the embeddings agrees
with the intrinsic edge on the entire source range. -/
theorem embeddedColoredEdge_coe_of_intertwining (c : ℝ) (i : Fin d)
    (A : (I → ℝ) → (J → ℝ))
    (hA : ∀ y, A (L.mulVec y) = G.mulVec ((coloredStarEdgeProjection d r c i).mulVec y))
    (z : MatrixRange L) :
    (embeddedColoredEdge d r L B hBL G H hHG c i z : J → ℝ) = A z := by
  let E := matrixRangeEquiv L B hBL
  let y := E.symm z
  have hz : L.mulVec y = z := by
    change (E (E.symm z) : I → ℝ) = z
    rw [E.apply_symm_apply]
  change G.mulVec ((coloredStarEdgeProjection d r c i).mulVec y) = A z
  rw [← hA, hz]

/-- Actual ambient edge law, for a supplied source-coordinate observation. -/
theorem embeddedColoredEdge_ambient_law (c : ℝ) (i : Fin d)
    (A : (I → ℝ) → (J → ℝ)) (hAm : Measurable A)
    (hA : ∀ y, A (L.mulVec y) = G.mulVec ((coloredStarEdgeProjection d r c i).mulVec y))
    (N : Measure (MatrixRange L)) :
    Measure.map (fun z : MatrixRange G => (z : J → ℝ))
      (Measure.map (embeddedColoredEdge d r L B hBL G H hHG c i) N) =
      Measure.map A (Measure.map (fun z : MatrixRange L => (z : I → ℝ)) N) := by
  rw [Measure.map_map measurable_subtype_coe
      (embeddedColoredEdge d r L B hBL G H hHG c i).continuous_of_finiteDimensional.measurable,
    Measure.map_map hAm measurable_subtype_coe]
  congr 1
  funext z
  exact embeddedColoredEdge_coe_of_intertwining d r L B hBL G H hHG c i A hA z

/-- The exact actual white law of the embedded edge. -/
theorem embeddedColoredEdge_white_law (c : ℝ) (i : Fin d) (N : Measure (MatrixRange L)) :
    embeddingWhiteLaw G H hHG (Measure.map (embeddedColoredEdge d r L B hBL G H hHG c i) N) =
      Measure.map (fun y => (coloredStarEdgeProjection d r c i).mulVec y) (embeddingWhiteLaw L B hBL N) := by
  rw [embeddingWhiteLaw, Measure.map_map (matrixRangeEquiv G H hHG).symm.continuous.measurable
      (embeddedColoredEdge d r L B hBL G H hHG c i).continuous_of_finiteDimensional.measurable,
    embeddingWhiteLaw, Measure.map_map (measurable_finiteMatrixAction _)
      (matrixRangeEquiv L B hBL).symm.continuous.measurable]
  congr 1
  funext z
  change (matrixRangeEquiv G H hHG).symm ((matrixRangeEquiv G H hHG)
    ((coloredStarEdgeProjection d r c i).mulVec ((matrixRangeEquiv L B hBL).symm z))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- The actual embedded Gaussian star has the actual embedded Gaussian edge. -/
theorem embeddedColoredEdge_gaussian_law (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    Measure.map (embeddedColoredEdge d r L B hBL G H hHG c i) (embeddingGaussian L B hBL) =
      embeddingGaussian G H hHG := by
  let E := matrixRangeEquiv G H hHG
  apply MeasurableEquiv.map_measurableEquiv_injective E.symm.toHomeomorph.toMeasurableEquiv
  change embeddingWhiteLaw G H hHG
      (Measure.map (embeddedColoredEdge d r L B hBL G H hHG c i) (embeddingGaussian L B hBL)) =
    embeddingWhiteLaw G H hHG (embeddingGaussian G H hHG)
  rw [embeddedColoredEdge_white_law, embeddingWhiteLaw_embeddingGaussian,
    embeddingWhiteLaw_embeddingGaussian,
    standardVector_map_orthonormal_rows _ (coloredStarEdgeProjection_mul_transpose d r hd c hc i)]

/-- Ambient Gram second moments imply actual identity moments of the white
range law, before any entropy or Gaussianity argument. -/
theorem embeddedWhiteLaw_identitySecondMoments (N : Measure (MatrixRange L))
    (hfinite : Integrable (squareRadius (I := I))
      (Measure.map (fun z : MatrixRange L => (z : I → ℝ)) N))
    (hmom : HasSecondMoments (Measure.map (fun z : MatrixRange L => (z : I → ℝ)) N) (L * L.transpose)) :
    HasIdentitySecondMoments (embeddingWhiteLaw L B hBL N) := by
  rw [embeddingWhiteLaw_eq_ambient_leftInverse]
  exact identitySecondMoments_of_gram_leftInverse _ hfinite L B hmom hBL

/-- Constructed finite entropy of the actual white star law. -/
def embeddedStarWhiteEntropyDensity
    (starChart : MatrixRange L ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ))
    (N : Measure (MatrixRange L)) [IsProbabilityMeasure N]
    (f : FiniteEntropyDensity (Measure.map starChart N)) :
    FiniteEntropyDensity (embeddingWhiteLaw L B hBL N) := f.embeddingWhite L B hBL starChart N

/-- Constructed finite entropy of every actual white edge law. -/
def embeddedEdgeWhiteEntropyDensity (c : ℝ)
    (edgeChart : MatrixRange G ≃ₗ[ℝ] ((Bool × Fin r) → ℝ))
    (N : Measure (MatrixRange L)) [IsProbabilityMeasure N]
    (i : Fin d)
    (g : FiniteEntropyDensity (Measure.map edgeChart
      (Measure.map (embeddedColoredEdge d r L B hBL G H hHG c i) N))) :
    FiniteEntropyDensity (Measure.map (fun y => (coloredStarEdgeProjection d r c i).mulVec y)
      (embeddingWhiteLaw L B hBL N)) := by
  letI : IsProbabilityMeasure (Measure.map (embeddedColoredEdge d r L B hBL G H hHG c i) N) :=
    isProbabilityMeasure_map
      (embeddedColoredEdge d r L B hBL G H hHG c i).continuous_of_finiteDimensional.measurable.aemeasurable
  exact (g.embeddingWhite G H hHG edgeChart
    (Measure.map (embeddedColoredEdge d r L B hBL G H hHG c i) N)).cast
      (embeddedColoredEdge_white_law d r L B hBL G H hHG c i N).symm

/-- Exact Gaussian-relative intrinsic entropy cancellation for both full
column embeddings. This identity assumes no entropy inequality. -/
theorem embeddedFrameEntropy_whitening (c : ℝ)
    (starChart : MatrixRange L ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ))
    (edgeChart : MatrixRange G ≃ₗ[ℝ] ((Bool × Fin r) → ℝ))
    (N : Measure (MatrixRange L)) [IsProbabilityMeasure N]
    (f : FiniteEntropyDensity (Measure.map starChart N))
    (g : ∀ i, FiniteEntropyDensity (Measure.map edgeChart
      (Measure.map (embeddedColoredEdge d r L B hBL G H hHG c i) N))) :
    (f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy) -
      ((embeddingGaussianChartDensity L B hBL starChart).entropy -
        (d : ℝ) / 2 * (embeddingGaussianChartDensity G H hHG edgeChart).entropy) =
      initialFrameEntropy (embeddedStarWhiteEntropyDensity d r L B hBL starChart N f)
        (fun i => embeddedEdgeWhiteEntropyDensity d r L B hBL G H hHG c edgeChart N i (g i)) := by
  have hGauss : (standardVectorEntropyDensity (Fin r × Fin d)).entropy -
      (d : ℝ) / 2 * (standardVectorEntropyDensity (Bool × Fin r)).entropy = 0 := by
    rw [standardVectorEntropyDensity_entropy, standardVectorEntropyDensity_entropy]
    simp only [gaussianEntropyValue, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      Nat.cast_mul, Nat.cast_ofNat, NNReal.coe_one]
    ring
  have hstar := embeddingGaussian_relative_entropy_cancellation L B hBL starChart N f
  have hedge (i : Fin d) :
      (g i).entropy - (embeddingGaussianChartDensity G H hHG edgeChart).entropy =
        (embeddedEdgeWhiteEntropyDensity d r L B hBL G H hHG c edgeChart N i (g i)).entropy -
          (standardVectorEntropyDensity (Bool × Fin r)).entropy := by
    letI : IsProbabilityMeasure (Measure.map (embeddedColoredEdge d r L B hBL G H hHG c i) N) :=
      isProbabilityMeasure_map
        (embeddedColoredEdge d r L B hBL G H hHG c i).continuous_of_finiteDimensional.measurable.aemeasurable
    exact embeddingGaussian_relative_entropy_cancellation G H hHG edgeChart _ (g i)
  calc
    _ = (f.entropy - (embeddingGaussianChartDensity L B hBL starChart).entropy) -
        (1 / 2 : ℝ) * ∑ i, ((g i).entropy - (embeddingGaussianChartDensity G H hHG edgeChart).entropy) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = _ := by
      rw [hstar]
      simp_rw [hedge]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, initialFrameEntropy, embeddedStarWhiteEntropyDensity]
      linarith

/-- Equality of the actual white law and the standard Gaussian is equivalent
to equality of the actual source range law and its embedded Gaussian. -/
theorem embeddedWhiteLaw_eq_standard_iff (N : Measure (MatrixRange L)) :
    embeddingWhiteLaw L B hBL N = standardVector (Fin r × Fin d) ↔ N = embeddingGaussian L B hBL := by
  constructor
  · intro hwhite
    rw [← matrixRangeEquiv_map_embeddingWhiteLaw L B hBL N, hwhite]
    rfl
  · intro hN
    rw [hN]
    exact embeddingWhiteLaw_embeddingGaussian L B hBL

/-- Generic transport of the actual colored upper inequality. The exposed
white moment and symmetry conditions are ordinary intermediate data for a
source-coordinate adapter; no analytic inequality is an assumption. -/
theorem embedded_frame_entropy_upper (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (starChart : MatrixRange L ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ))
    (edgeChart : MatrixRange G ≃ₗ[ℝ] ((Bool × Fin r) → ℝ))
    (N : Measure (MatrixRange L)) [IsProbabilityMeasure N]
    (f : FiniteEntropyDensity (Measure.map starChart N))
    (g : ∀ i, FiniteEntropyDensity (Measure.map edgeChart
      (Measure.map (embeddedColoredEdge d r L B hBL G H hHG c i) N)))
    (hmom : HasIdentitySecondMoments (embeddingWhiteLaw L B hBL N))
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun y => (coloredStarEdgeProjection d r c i).mulVec y) (embeddingWhiteLaw L B hBL N)) =
        Measure.map (fun y => (coloredStarEdgeProjection d r c i).mulVec y) (embeddingWhiteLaw L B hBL N)) :
    f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy ≤
      (embeddingGaussianChartDensity L B hBL starChart).entropy -
        (d : ℝ) / 2 * (embeddingGaussianChartDensity G H hHG edgeChart).entropy := by
  have hu := colored_star_entropy_upper d r hd c hbulk (embeddingWhiteLaw L B hBL N)
    (integrable_squareRadius_of_identitySecondMoments _ hmom) hmom
    (embeddedStarWhiteEntropyDensity d r L B hBL starChart N f)
    (fun i => embeddedEdgeWhiteEntropyDensity d r L B hBL G H hHG c edgeChart N i (g i)) hrev
  have hr : initialFrameEntropy (embeddedStarWhiteEntropyDensity d r L B hBL starChart N f)
      (fun i => embeddedEdgeWhiteEntropyDensity d r L B hBL G H hHG c edgeChart N i (g i)) ≤ 0 :=
    sub_nonpos.mpr hu
  rw [← embeddedFrameEntropy_whitening d r L B hBL G H hHG c starChart edgeChart N f g] at hr
  exact sub_nonpos.mp hr

/-- Generic intrinsic Gaussian equality theorem, including r=0. The final
source-coordinate theorem derives the white moment and symmetry inputs. -/
theorem embedded_frame_entropy_equality_iff_gaussian (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (starChart : MatrixRange L ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ))
    (edgeChart : MatrixRange G ≃ₗ[ℝ] ((Bool × Fin r) → ℝ))
    (N : Measure (MatrixRange L)) [IsProbabilityMeasure N]
    (f : FiniteEntropyDensity (Measure.map starChart N))
    (g : ∀ i, FiniteEntropyDensity (Measure.map edgeChart
      (Measure.map (embeddedColoredEdge d r L B hBL G H hHG c i) N)))
    (hmom : HasIdentitySecondMoments (embeddingWhiteLaw L B hBL N))
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun y => (coloredStarEdgeProjection d r c i).mulVec y) (embeddingWhiteLaw L B hBL N)) =
        Measure.map (fun y => (coloredStarEdgeProjection d r c i).mulVec y) (embeddingWhiteLaw L B hBL N))
    (hperm : ∀ p : Equiv.Perm (Fin d),
      Measure.map (fun x : (Fin r × Fin d) → ℝ => fun q => x (q.1, p q.2))
        (embeddingWhiteLaw L B hBL N) = embeddingWhiteLaw L B hBL N) :
    (f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy =
      (embeddingGaussianChartDensity L B hBL starChart).entropy -
        (d : ℝ) / 2 * (embeddingGaussianChartDensity G H hHG edgeChart).entropy) ↔
      N = embeddingGaussian L B hBL := by
  rw [← sub_eq_zero, embeddedFrameEntropy_whitening d r L B hBL G H hHG c starChart edgeChart N f g]
  exact (colored_star_entropy_equality_iff_standardVector d r hd c hbulk
    (embeddingWhiteLaw L B hBL N) hmom
    (embeddedStarWhiteEntropyDensity d r L B hBL starChart N f)
    (fun i => embeddedEdgeWhiteEntropyDensity d r L B hBL G H hHG c edgeChart N i (g i)) hrev hperm).trans
      (embeddedWhiteLaw_eq_standard_iff d r L B hBL N)

end EmbeddedFrame
end GaussianWave.BS
