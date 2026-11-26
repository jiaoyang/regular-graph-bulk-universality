import GaussianWave.BS.GaussianBallEntropy
import GaussianWave.BS.FactorChart

/-!
# Unconditional scalar Gaussian reference entropy asymptotic

The finite Gaussian laws, their intrinsic isometric charts, the actual
finite-entropy density witnesses, and the limiting entropy balance are all
constructed.  No covariance formula, determinant limit, or chart-existence
premise is imposed on the final theorem.
-/
noncomputable section
open Filter
open scoped Topology
namespace GaussianWave.BS

def vertexGaussianIsometricChart (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    Matrix (VertexBallInnovation (m + 2) k) (VertexBallVertex (m + 2) k) ℝ :=
  Classical.choose (exists_isometric_factor_chart (vertexOrthoFactorMatrix m k energy)
    (vertexOrthoFactorMatrix_gram_det_pos m k energy he).ne')

def edgeGaussianIsometricChart (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    Matrix (EdgeBallInnovation (m + 2) k) (EdgeBallVertex (m + 2) k) ℝ :=
  Classical.choose (exists_isometric_factor_chart (edgeOrthoFactorMatrix m k energy)
    (edgeOrthoFactorMatrix_gram_det_pos m k energy he).ne')

theorem vertexGaussianIsometricChart_rows (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    vertexGaussianIsometricChart m k energy he * (vertexGaussianIsometricChart m k energy he).transpose = 1 :=
  (Classical.choose_spec (exists_isometric_factor_chart (vertexOrthoFactorMatrix m k energy)
    (vertexOrthoFactorMatrix_gram_det_pos m k energy he).ne')).1

theorem edgeGaussianIsometricChart_rows (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    edgeGaussianIsometricChart m k energy he * (edgeGaussianIsometricChart m k energy he).transpose = 1 :=
  (Classical.choose_spec (exists_isometric_factor_chart (edgeOrthoFactorMatrix m k energy)
    (edgeOrthoFactorMatrix_gram_det_pos m k energy he).ne')).1

theorem vertexGaussianIsometricChart_projection (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    (vertexGaussianIsometricChart m k energy he).transpose * vertexGaussianIsometricChart m k energy he *
      vertexOrthoFactorMatrix m k energy = vertexOrthoFactorMatrix m k energy :=
  (Classical.choose_spec (exists_isometric_factor_chart (vertexOrthoFactorMatrix m k energy)
    (vertexOrthoFactorMatrix_gram_det_pos m k energy he).ne')).2

theorem edgeGaussianIsometricChart_projection (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    (edgeGaussianIsometricChart m k energy he).transpose * edgeGaussianIsometricChart m k energy he *
      edgeOrthoFactorMatrix m k energy = edgeOrthoFactorMatrix m k energy :=
  (Classical.choose_spec (exists_isometric_factor_chart (edgeOrthoFactorMatrix m k energy)
    (edgeOrthoFactorMatrix_gram_det_pos m k energy he).ne')).2

def vertexGaussianIntrinsicDensity (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :=
  vertexGaussianBallChartDensity m k energy he (vertexGaussianIsometricChart m k energy he)
    (vertexGaussianIsometricChart_projection m k energy he)

def edgeGaussianIntrinsicDensity (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :=
  edgeGaussianBallChartDensity m k energy he (edgeGaussianIsometricChart m k energy he)
    (edgeGaussianIsometricChart_projection m k energy he)

def vertexGaussianIntrinsicEntropy (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) : ℝ :=
  (vertexGaussianIntrinsicDensity m k energy he).entropy

def edgeGaussianIntrinsicEntropy (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) : ℝ :=
  (edgeGaussianIntrinsicDensity m k energy he).entropy

/-- The Gaussian benchmark entropy balance, for genuine isometric intrinsic
volume, tends to zero at every fixed strict-bulk parameter. -/
theorem gaussian_ball_reference_entropy_tendsto_zero (m : ℕ) (hm : 0 < m)
    {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun k => vertexGaussianIntrinsicEntropy m k (radialEnergy m x) (abs_radialEnergy_lt_degree m hx) -
      (m + 2 : ℝ) / 2 * edgeGaussianIntrinsicEntropy m k (radialEnergy m x) (abs_radialEnergy_lt_degree m hx))
      atTop (𝓝 0) :=
  gaussian_ball_intrinsic_entropy_balance_tendsto_zero m hm hx
    (fun k => vertexGaussianIsometricChart m k (radialEnergy m x) (abs_radialEnergy_lt_degree m hx))
    (fun k => edgeGaussianIsometricChart m k (radialEnergy m x) (abs_radialEnergy_lt_degree m hx))
    (fun k => vertexGaussianIsometricChart_projection m k (radialEnergy m x) (abs_radialEnergy_lt_degree m hx))
    (fun k => edgeGaussianIsometricChart_projection m k (radialEnergy m x) (abs_radialEnergy_lt_degree m hx))

theorem abs_energy_lt_degree_of_strict_bulk (m : ℕ) (energy : ℝ)
    (hbulk : |energy| < 2 * Real.sqrt (m + 1)) : |energy| < (m + 2 : ℝ) := by
  have hs : 0 < 2 * Real.sqrt (m + 1 : ℝ) := by positivity
  have hx : |energy / (2 * Real.sqrt (m + 1 : ℝ))| < 1 := by
    rw [abs_div, abs_of_pos hs]
    exact (div_lt_one hs).mpr hbulk
  have hE : radialEnergy m (energy / (2 * Real.sqrt (m + 1))) = energy := by
    unfold radialEnergy
    field_simp
  simpa only [hE] using abs_radialEnergy_lt_degree m hx

/-- Source Theorem 9.1 in the original energy variable, with `d=m+2≥3`.
The proof has no Gaussian-reference entropy or determinant assumption. -/
theorem gaussian_ball_reference_entropy_tendsto_zero_energy (m : ℕ) (hm : 0 < m) (energy : ℝ)
    (hbulk : |energy| < 2 * Real.sqrt (m + 1)) :
    Tendsto (fun k => vertexGaussianIntrinsicEntropy m k energy (abs_energy_lt_degree_of_strict_bulk m energy hbulk) -
      (m + 2 : ℝ) / 2 * edgeGaussianIntrinsicEntropy m k energy (abs_energy_lt_degree_of_strict_bulk m energy hbulk))
      atTop (𝓝 0) := by
  have hs : 0 < 2 * Real.sqrt (m + 1 : ℝ) := by positivity
  have hx : |energy / (2 * Real.sqrt (m + 1 : ℝ))| < 1 := by
    rw [abs_div, abs_of_pos hs]
    exact (div_lt_one hs).mpr hbulk
  have hE : radialEnergy m (energy / (2 * Real.sqrt (m + 1))) = energy := by
    unfold radialEnergy
    field_simp
  simpa only [hE] using gaussian_ball_reference_entropy_tendsto_zero m hm hx

end GaussianWave.BS
