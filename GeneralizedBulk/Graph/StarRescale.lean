import GeneralizedBulk.Gaussian.StarNormalProjection
import GeneralizedBulk.Matrix.NormalProjectionAlgebra

/-! Exact normal rescaling of the actual restricted resolvent covariance. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Covariance
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def localEntropyStarCovariance (o : Fin (N n)) (E eta sigma : ℝ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℝ :=
  (D.resolventCovariance n ω E eta sigma).submatrix (D.entropyStarVertex n ω o) (D.entropyStarVertex n ω o)

def starNormalVarianceScale (d : ℕ) (E eta sigma : ℝ) : ℝ := eta / (sigma * ((d : ℝ) + E ^ 2))
def starNormalRescaleFactor (d : ℕ) (E eta sigma : ℝ) : ℝ := Real.sqrt (sigma * ((d : ℝ) + E ^ 2) / eta)

theorem normalizedStarNormal_eq_smul (E : ℝ) :
    normalizedStarNormal d E = (Real.sqrt ((d : ℝ)+E^2))⁻¹ • entropyStarNormal (d := d) E := by
  funext j
  simp only [normalizedStarNormal, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem normalizedStarNormal_cross_covariance (o : Fin (N n)) (E eta sigma : ℝ) (heta : 0 < eta)
    (j : Fin (d+1)) :
    (∑ i, normalizedStarNormal d E i * D.localEntropyStarCovariance n ω o E eta sigma i j) =
      (eta / sigma / Real.sqrt ((d : ℝ)+E^2)) *
        (D.resolvent n ω (⟨E,eta⟩ : ℂ) o (D.entropyStarVertex n ω o j)).re := by
  simp only [normalizedStarNormal, localEntropyStarCovariance, Matrix.submatrix_apply,
    div_mul_eq_mul_div, ← Finset.sum_div]
  rw [D.entropyStarNormal_cross_covariance n ω o _ E eta sigma heta]
  ring

theorem normalizedStarNormal_quadratic_covariance (hd : 0 < d) (o : Fin (N n))
    (E eta sigma : ℝ) (heta : 0 < eta) :
    dotProduct (normalizedStarNormal d E)
      ((D.localEntropyStarCovariance n ω o E eta sigma).mulVec (normalizedStarNormal d E)) =
      starNormalVarianceScale d E eta sigma -
        eta ^ 2 * D.resolventCovariance n ω E eta sigma o o / ((d : ℝ)+E^2) := by
  have hb : 0 < (d : ℝ)+E^2 := add_pos_of_pos_of_nonneg (Nat.cast_pos.mpr hd) (sq_nonneg E)
  rw [normalizedStarNormal_eq_smul, quadratic_smul]
  change (Real.sqrt ((d : ℝ)+E^2))⁻¹ ^ 2 *
    dotProduct (entropyStarNormal E) ((D.localEntropyStarCovariance n ω o E eta sigma).mulVec (entropyStarNormal E)) = _
  rw [show dotProduct (entropyStarNormal E) ((D.localEntropyStarCovariance n ω o E eta sigma).mulVec (entropyStarNormal E)) =
      eta / sigma - eta ^ 2 * D.resolventCovariance n ω E eta sigma o o from
        D.entropyStarNormal_quadratic_covariance n ω o E eta sigma heta,
    inv_pow, Real.sq_sqrt hb.le]
  unfold starNormalVarianceScale
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem starNormalProjection_local_covariance (hd : 0 < d) (o : Fin (N n))
    (E eta sigma : ℝ) (heta : 0 < eta) :
    starNormalProjection d E * D.localEntropyStarCovariance n ω o E eta sigma * starNormalProjection d E =
      starNormalVarianceScale d E eta sigma • starNormalProjection d E +
        (-eta ^ 2 * D.resolventCovariance n ω E eta sigma o o / ((d : ℝ)+E^2)) • starNormalProjection d E := by
  rw [starNormalProjection, unitNormalProjection_covariance,
    D.normalizedStarNormal_quadratic_covariance n ω hd o E eta sigma heta]
  rw [sub_smul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem starNormalRescaleFactor_sq_scale (hd : 0 < d) (E eta sigma : ℝ)
    (heta : 0 < eta) (hsigma : 0 < sigma) :
    starNormalRescaleFactor d E eta sigma ^ 2 * starNormalVarianceScale d E eta sigma = 1 := by
  have hb : 0 < (d : ℝ)+E^2 := add_pos_of_pos_of_nonneg (Nat.cast_pos.mpr hd) (sq_nonneg E)
  unfold starNormalRescaleFactor starNormalVarianceScale
  rw [Real.sq_sqrt (by positivity : 0 ≤ sigma * ((d : ℝ)+E^2) / eta)]
  field_simp

end GeneralizedBulk.External.RegularSpectralData
