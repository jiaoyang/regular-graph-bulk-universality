import GaussianWave.BS.GaussianGainAsymptotic

/-!
# Gaussian finite-ball determinant cancellation and its strict-bulk limit

These determinants are the actual column Grams of the constructed
nonredundant Gaussian factors.  Positivity and the disappearance of the
descendant terms are proved before applying the scalar radial limit.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace GaussianWave.BS

theorem branchMeanEnergy_ge_root_sq (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (root parent : ℝ) :
    root ^ 2 ≤ branchMeanEnergy (m + 1) energy k root parent := by
  rw [branchMeanEnergy_eq_profile_sum m k energy he]
  have hs := Finset.single_le_sum
    (f := fun n => (m + 1 : ℝ) ^ n *
      (branchMeanA (m + 1) energy n * root + branchMeanB (m + 1) energy n * parent) ^ 2)
    (s := Finset.range (k + 1)) (a := 0)
    (fun n _ => mul_nonneg (pow_nonneg (by positivity) n) (sq_nonneg _)) (by simp)
  simpa only [pow_zero, branchMeanA, branchMeanB, one_mul, zero_mul, add_zero] using hs

theorem vertexRadialGain_pos (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    0 < vertexRadialGain m k energy := by
  have hQ := branchMeanEnergy_ge_root_sq m k energy he (energy / (m + 2)) 1
  have hn : 0 ≤ branchMeanEnergy (m + 1) energy k (energy / (m + 2)) 1 :=
    (sq_nonneg _).trans hQ
  have hmul := mul_nonneg (show (0 : ℝ) ≤ m + 2 by positivity) hn
  have hid : vertexRadialGain m k energy = 1 + (m + 2 : ℝ) *
      branchMeanEnergy (m + 1) energy k (energy / (m + 2)) 1 := by
    unfold vertexRadialGain branchMeanEnergy
    ring
  rw [hid]
  linarith

theorem edgePlusGain_pos (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    0 < edgePlusGain m k energy := by
  have hc : |energy / (m + 2 : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < m + 2)]
    exact (div_lt_one (by positivity)).mpr he
  have hQ := branchMeanEnergy_ge_root_sq m k energy he 1 1
  have hid : edgePlusGain m k energy = (1 + energy / (m + 2)) *
      branchMeanEnergy (m + 1) energy k 1 1 := by unfold edgePlusGain branchMeanEnergy; ring
  rw [hid]
  exact mul_pos (by linarith [(abs_lt.mp hc).1]) (by norm_num at hQ; linarith)

theorem edgeMinusGain_pos (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    0 < edgeMinusGain m k energy := by
  have hc : |energy / (m + 2 : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < m + 2)]
    exact (div_lt_one (by positivity)).mpr he
  have hQ := branchMeanEnergy_ge_root_sq m k energy he 1 (-1)
  have hid : edgeMinusGain m k energy = (1 - energy / (m + 2)) *
      branchMeanEnergy (m + 1) energy k 1 (-1) := by unfold edgeMinusGain branchMeanEnergy; ring
  rw [hid]
  exact mul_pos (by linarith [(abs_lt.mp hc).2]) (by norm_num at hQ; linarith)

theorem vertexOrthoFactorMatrix_gram_det_pos (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    0 < ((vertexOrthoFactorMatrix m k energy).transpose * vertexOrthoFactorMatrix m k energy).det := by
  rw [vertexOrthoFactorMatrix_gram_det m k energy he]
  exact mul_pos (mul_pos (vertexRadialGain_pos m k energy he)
    (pow_pos (vertexContrastGain_pos m k energy he) _))
    (pow_pos (branchNoiseDeterminant_pos m k energy he) _)

theorem edgeOrthoFactorMatrix_gram_det_pos (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    0 < ((edgeOrthoFactorMatrix m k energy).transpose * edgeOrthoFactorMatrix m k energy).det := by
  rw [edgeOrthoFactorMatrix_gram_det m k energy he]
  exact mul_pos (mul_pos (edgePlusGain_pos m k energy he) (edgeMinusGain_pos m k energy he))
    (pow_pos (branchNoiseDeterminant_pos m k energy he) _)

theorem vertexOrthoFactorMatrix_log_gram_det (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    Real.log ((vertexOrthoFactorMatrix m k energy).transpose * vertexOrthoFactorMatrix m k energy).det =
      Real.log (vertexRadialGain m k energy) + (m + 1 : ℝ) * Real.log (vertexContrastGain m k energy) +
        (m + 2 : ℝ) * Real.log (branchNoiseDeterminant m k energy) := by
  have h1 := (vertexRadialGain_pos m k energy he).ne'
  have h2 := (vertexContrastGain_pos m k energy he).ne'
  have hD := (branchNoiseDeterminant_pos m k energy he).ne'
  rw [vertexOrthoFactorMatrix_gram_det m k energy he,
    Real.log_mul (mul_ne_zero h1 (pow_ne_zero _ h2)) (pow_ne_zero _ hD),
    Real.log_mul h1 (pow_ne_zero _ h2), Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]

theorem edgeOrthoFactorMatrix_log_gram_det (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    Real.log ((edgeOrthoFactorMatrix m k energy).transpose * edgeOrthoFactorMatrix m k energy).det =
      Real.log (edgePlusGain m k energy) + Real.log (edgeMinusGain m k energy) +
        2 * Real.log (branchNoiseDeterminant m k energy) := by
  have hp := (edgePlusGain_pos m k energy he).ne'
  have hm := (edgeMinusGain_pos m k energy he).ne'
  have hD := (branchNoiseDeterminant_pos m k energy he).ne'
  rw [edgeOrthoFactorMatrix_gram_det m k energy he,
    Real.log_mul (mul_ne_zero hp hm) (pow_ne_zero _ hD), Real.log_mul hp hm, Real.log_pow]
  norm_num

/-- The actual finite-factor log determinant balance from source Theorem 9.1. -/
theorem gaussian_ball_log_gram_det_balance_tendsto_zero (m : ℕ) (hm : 0 < m)
    {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun k =>
      Real.log ((vertexOrthoFactorMatrix m k (radialEnergy m x)).transpose *
        vertexOrthoFactorMatrix m k (radialEnergy m x)).det -
      (m + 2 : ℝ) / 2 * Real.log ((edgeOrthoFactorMatrix m k (radialEnergy m x)).transpose *
        edgeOrthoFactorMatrix m k (radialEnergy m x)).det) atTop (𝓝 0) := by
  convert exceptional_gain_log_balance_tendsto_zero m hm hx using 1
  ext k
  rw [vertexOrthoFactorMatrix_log_gram_det m k _ (abs_radialEnergy_lt_degree m hx),
    edgeOrthoFactorMatrix_log_gram_det m k _ (abs_radialEnergy_lt_degree m hx)]
  ring

end GaussianWave.BS
