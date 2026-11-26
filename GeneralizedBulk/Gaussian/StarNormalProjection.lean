import GeneralizedBulk.Graph.StarNormalCovariance
import GeneralizedBulk.Entropy.PhysicalStarFrame
import GeneralizedBulk.Matrix.ProjectionRescale

/-! The literal normalized star normal and the kernel of the Gaussian-wave covariance. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Gaussian
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.External.RegularSpectralData GeneralizedBulk.Covariance

def normalizedStarNormal (d : ℕ) (E : ℝ) (j : Fin (d+1)) : ℝ :=
  entropyStarNormal E j / Real.sqrt ((d : ℝ) + E ^ 2)

theorem normalizedStarNormal_sq_sum (d : ℕ) (hd : 0 < d) (E : ℝ) :
    (∑ j, normalizedStarNormal d E j ^ 2) = 1 := by
  have hn : 0 < (d : ℝ) + E ^ 2 := add_pos_of_pos_of_nonneg (Nat.cast_pos.mpr hd) (sq_nonneg E)
  simp only [normalizedStarNormal, div_pow, ← Finset.sum_div]
  rw [entropyStarNormal_sq_sum, Real.sq_sqrt hn.le, div_self hn.ne']

theorem starRow_normal_pairing_zero (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (x : WhiteStar d) :
    (∑ j : Fin (d+1), entropyStarNormal E j * @inner ℝ (WhiteStar d) _ (starRow d hd E j) x) = 0 := by
  have hh := physical_star_constraint d hd (E / d) (starRho d E) x
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have he : (d : ℝ) * (E / d) = E := by field_simp
  rw [Fin.sum_univ_succ]
  simp only [entropyStarNormal, Fin.cases_zero, Fin.cases_succ, one_mul,
    starRow_inner_root, starRow_inner_leaf]
  simp only [physicalLinearMap_leaf, physicalLinearMap_root, he] at hh
  linarith

theorem normalizedStarNormal_covariance_left (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d)
    (j : Fin (d+1)) : (∑ i, normalizedStarNormal d E i * starWaveCovariance d E i j) = 0 := by
  simp only [normalizedStarNormal, div_mul_eq_mul_div, ← Finset.sum_div]
  have hh := starRow_normal_pairing_zero d hd E (starRow d hd E j)
  simp_rw [starRow_gram d hd E hE] at hh
  rw [hh, zero_div]

theorem starWaveCovariance_transpose (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    (starWaveCovariance d E).transpose = starWaveCovariance d E := by
  rw [← starCoefficients_gram d hd E hE, Matrix.transpose_mul, Matrix.transpose_transpose]

def starNormalProjection (d : ℕ) (E : ℝ) : Matrix (Fin (d+1)) (Fin (d+1)) ℝ :=
  unitNormalProjection (normalizedStarNormal d E)

theorem starNormalProjection_idempotent (d : ℕ) (hd : 0 < d) (E : ℝ) :
    starNormalProjection d E * starNormalProjection d E = starNormalProjection d E :=
  unitNormalProjection_idempotent _ (normalizedStarNormal_sq_sum d hd E)

theorem starNormalProjection_wave_left (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    starNormalProjection d E * starWaveCovariance d E = 0 := by
  ext i j
  simp only [Matrix.mul_apply, starNormalProjection, unitNormalProjection, Matrix.zero_apply]
  calc
    _ = normalizedStarNormal d E i * ∑ k, normalizedStarNormal d E k * starWaveCovariance d E k j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = 0 := by rw [normalizedStarNormal_covariance_left d hd E hE, mul_zero]

theorem starNormalProjection_transpose (d : ℕ) (E : ℝ) : (starNormalProjection d E).transpose = starNormalProjection d E := by
  ext i j
  exact mul_comm _ _

theorem starNormalProjection_wave_right (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    starWaveCovariance d E * starNormalProjection d E = 0 := by
  have h := congrArg Matrix.transpose (starNormalProjection_wave_left d hd E hE)
  simpa only [Matrix.transpose_mul, starWaveCovariance_transpose d hd E hE, starNormalProjection_transpose,
    Matrix.transpose_zero] using h

end GeneralizedBulk.Gaussian
