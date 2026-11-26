import GaussianWave.BS.GaussianDeterminantLimit

/-!
# Intrinsic Gaussian entropy on actual finite tree balls

The chart law and its finite-entropy density are actual linear pushforwards.
The determinant formula is derived from entropy change of variables; the
asymptotic is the proved finite-factor determinant limit.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace GaussianWave.BS

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

theorem factorChart_gram (M : Matrix V I ℝ) (O : Matrix I V ℝ)
    (hO : O.transpose * O * M = M) :
    (O * M).transpose * (O * M) = M.transpose * M := by
  rw [Matrix.transpose_mul]
  calc
    _ = M.transpose * (O.transpose * O * M) := by simp only [Matrix.mul_assoc]
    _ = M.transpose * M := by rw [hO]

theorem factorChart_det_ne_zero (M : Matrix V I ℝ) (O : Matrix I V ℝ)
    (hO : O.transpose * O * M = M) (hM : 0 < (M.transpose * M).det) : (O * M).det ≠ 0 := by
  intro hzero
  have h := congrArg Matrix.det (factorChart_gram M O hO)
  rw [Matrix.det_mul, Matrix.det_transpose, hzero, zero_mul] at h
  exact hM.ne' h.symm

theorem map_linearImageGaussian (M : Matrix V I ℝ) (O : Matrix I V ℝ) :
    Measure.map (fun x => O.mulVec x) (linearImageGaussian M) =
      Measure.map (fun z => (O * M).mulVec z) (standardVector I) := by
  rw [linearImageGaussian, Measure.map_map (measurable_finiteMatrixAction O)
    (measurable_finiteMatrixAction M)]
  congr 1
  exact funext (fun z => Matrix.mulVec_mulVec z O M)

def gaussianFactorChartDensity (M : Matrix V I ℝ) (O : Matrix I V ℝ)
    (hO : O.transpose * O * M = M) (hM : 0 < (M.transpose * M).det) :
    FiniteEntropyDensity (Measure.map (fun x => O.mulVec x) (linearImageGaussian M)) :=
  ((standardVectorEntropyDensity I).linearImage (O * M) (factorChart_det_ne_zero M O hO hM)).cast
    (map_linearImageGaussian M O)

theorem gaussianFactorChartDensity_entropy (M : Matrix V I ℝ) (O : Matrix I V ℝ)
    (hO : O.transpose * O * M = M) (hM : 0 < (M.transpose * M).det) :
    (gaussianFactorChartDensity M O hO hM).entropy =
      gaussianEntropyValue I 1 + (1 / 2 : ℝ) * Real.log (M.transpose * M).det := by
  unfold gaussianFactorChartDensity
  rw [FiniteEntropyDensity.cast_entropy, FiniteEntropyDensity.linearImage_entropy,
    standardVectorEntropyDensity_entropy]
  have hdet : (O * M).det ^ 2 = (M.transpose * M).det := by
    simpa only [pow_two, Matrix.det_mul, Matrix.det_transpose] using
      congrArg Matrix.det (factorChart_gram M O hO)
  have hlog : Real.log (M.transpose * M).det = 2 * Real.log |(O * M).det| := by
    rw [← hdet, Real.log_pow, Real.log_abs]
    norm_num
  rw [hlog]
  ring

theorem vertexGaussianBallLaw_eq_orthoFactor (m k : ℕ) (energy : ℝ) :
    vertexGaussianBallLaw m k energy = linearImageGaussian (vertexOrthoFactorMatrix m k energy) := by
  rw [← vertexOrthoGaussianLaw_eq, map_standardVector_eq_linearImage]
  rfl

theorem edgeGaussianBallLaw_eq_orthoFactor (m k : ℕ) (energy : ℝ) :
    edgeGaussianBallLaw m k energy = linearImageGaussian (edgeOrthoFactorMatrix m k energy) := by
  rw [← edgeOrthoGaussianLaw_eq, map_standardVector_eq_linearImage]
  rfl

def vertexGaussianBallChartDensity (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (O : Matrix (VertexBallInnovation (m + 2) k) (VertexBallVertex (m + 2) k) ℝ)
    (hO : O.transpose * O * vertexOrthoFactorMatrix m k energy = vertexOrthoFactorMatrix m k energy) :
    FiniteEntropyDensity (Measure.map (fun x => O.mulVec x) (vertexGaussianBallLaw m k energy)) :=
  (gaussianFactorChartDensity _ O hO (vertexOrthoFactorMatrix_gram_det_pos m k energy he)).cast
    (congrArg (Measure.map (fun x => O.mulVec x)) (vertexGaussianBallLaw_eq_orthoFactor m k energy))

def edgeGaussianBallChartDensity (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (O : Matrix (EdgeBallInnovation (m + 2) k) (EdgeBallVertex (m + 2) k) ℝ)
    (hO : O.transpose * O * edgeOrthoFactorMatrix m k energy = edgeOrthoFactorMatrix m k energy) :
    FiniteEntropyDensity (Measure.map (fun x => O.mulVec x) (edgeGaussianBallLaw m k energy)) :=
  (gaussianFactorChartDensity _ O hO (edgeOrthoFactorMatrix_gram_det_pos m k energy he)).cast
    (congrArg (Measure.map (fun x => O.mulVec x)) (edgeGaussianBallLaw_eq_orthoFactor m k energy))

theorem vertexGaussianBallChartDensity_entropy (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (O : Matrix (VertexBallInnovation (m + 2) k) (VertexBallVertex (m + 2) k) ℝ)
    (hO : O.transpose * O * vertexOrthoFactorMatrix m k energy = vertexOrthoFactorMatrix m k energy) :
    (vertexGaussianBallChartDensity m k energy he O hO).entropy =
      gaussianEntropyValue (VertexBallInnovation (m + 2) k) 1 +
        (1 / 2 : ℝ) * Real.log ((vertexOrthoFactorMatrix m k energy).transpose *
          vertexOrthoFactorMatrix m k energy).det :=
  gaussianFactorChartDensity_entropy _ O hO (vertexOrthoFactorMatrix_gram_det_pos m k energy he)

theorem edgeGaussianBallChartDensity_entropy (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (O : Matrix (EdgeBallInnovation (m + 2) k) (EdgeBallVertex (m + 2) k) ℝ)
    (hO : O.transpose * O * edgeOrthoFactorMatrix m k energy = edgeOrthoFactorMatrix m k energy) :
    (edgeGaussianBallChartDensity m k energy he O hO).entropy =
      gaussianEntropyValue (EdgeBallInnovation (m + 2) k) 1 +
        (1 / 2 : ℝ) * Real.log ((edgeOrthoFactorMatrix m k energy).transpose *
          edgeOrthoFactorMatrix m k energy).det :=
  gaussianFactorChartDensity_entropy _ O hO (edgeOrthoFactorMatrix_gram_det_pos m k energy he)

theorem gaussianBall_dimension_entropy_balance (m k : ℕ) :
    gaussianEntropyValue (VertexBallInnovation (m + 2) k) 1 -
      (m + 2 : ℝ) / 2 * gaussianEntropyValue (EdgeBallInnovation (m + 2) k) 1 = 0 := by
  unfold gaussianEntropyValue
  rw [card_vertexBallInnovation (m + 2) k (by omega), card_edgeBallInnovation (m + 2) k (by omega)]
  push_cast
  ring

/-- Source Theorem 9.1 for the actual constructed finite Gaussian laws in
arbitrary valid isometric charts, with actual finite-entropy densities. -/
theorem gaussian_ball_intrinsic_entropy_balance_tendsto_zero
    (m : ℕ) (hm : 0 < m) {x : ℝ} (hx : |x| < 1)
    (OC : ∀ k, Matrix (VertexBallInnovation (m + 2) k) (VertexBallVertex (m + 2) k) ℝ)
    (OE : ∀ k, Matrix (EdgeBallInnovation (m + 2) k) (EdgeBallVertex (m + 2) k) ℝ)
    (hOC : ∀ k, (OC k).transpose * OC k * vertexOrthoFactorMatrix m k (radialEnergy m x) =
      vertexOrthoFactorMatrix m k (radialEnergy m x))
    (hOE : ∀ k, (OE k).transpose * OE k * edgeOrthoFactorMatrix m k (radialEnergy m x) =
      edgeOrthoFactorMatrix m k (radialEnergy m x)) :
    Tendsto (fun k =>
      (vertexGaussianBallChartDensity m k _ (abs_radialEnergy_lt_degree m hx) (OC k) (hOC k)).entropy -
      (m + 2 : ℝ) / 2 *
        (edgeGaussianBallChartDensity m k _ (abs_radialEnergy_lt_degree m hx) (OE k) (hOE k)).entropy)
      atTop (𝓝 0) := by
  have h := (gaussian_ball_log_gram_det_balance_tendsto_zero m hm hx).const_mul (1 / 2 : ℝ)
  simp only [mul_zero] at h
  convert h using 1
  ext k
  rw [vertexGaussianBallChartDensity_entropy, edgeGaussianBallChartDensity_entropy]
  have hdim := gaussianBall_dimension_entropy_balance m k
  linarith

end GaussianWave.BS
