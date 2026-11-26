import GeneralizedBulk.Graph.ResolventCovariance
import GeneralizedBulk.Graph.EigenvalueBound
import GeneralizedBulk.Matrix.CovarianceBounds

/-! Actual lower and upper covariance bounds for graph resolvent noise. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Covariance
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem resolventCovarianceWeight_bounds (E eta sigma : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma)
    (a : Fin (N n)) :
    (eta / sigma) / (((d : ℝ) + |E|) ^ 2 + eta ^ 2) ≤ D.resolventCovarianceWeight n ω E eta sigma a ∧
    D.resolventCovarianceWeight n ω E eta sigma a ≤ 1 / (sigma * eta) := by
  have hd := D.resolventDenominator_pos n ω E eta heta a
  have hnum := (div_pos heta hsigma).le
  have hbase : 0 < ((d : ℝ) + |E|) ^ 2 + eta ^ 2 := by positivity
  have hbound : D.resolventDenominator n ω E eta a ≤ ((d : ℝ) + |E|) ^ 2 + eta ^ 2 := by
    have hh : |D.eigenvalue n ω a - E| ≤ (d : ℝ) + |E| :=
      (abs_sub _ _).trans (add_le_add_right (D.eigenvalue_abs_le_degree n ω a) _)
    have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : (0 : ℝ) ≤ d + |E|)).mpr hh
    dsimp [resolventDenominator]
    nlinarith [sq_abs (D.eigenvalue n ω a - E)]
  constructor
  · exact div_le_div_of_nonneg_left hnum hd hbound
  · have hh : D.resolventCovarianceWeight n ω E eta sigma a ≤ (eta / sigma) / eta ^ 2 :=
      div_le_div_of_nonneg_left hnum (sq_pos_of_pos heta) (by
        dsimp [resolventDenominator]; nlinarith [sq_nonneg (D.eigenvalue n ω a - E)])
    convert hh using 1
    field_simp
    <;> ring

theorem resolventCovariance_quadratic_bounds (E eta sigma : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma)
    (x : Fin (N n) → ℝ) :
    ((eta / sigma) / (((d : ℝ) + |E|) ^ 2 + eta ^ 2)) * (∑ i, x i ^ 2) ≤
      dotProduct x (D.resolventCovariance n ω E eta sigma *ᵥ x) ∧
    dotProduct x (D.resolventCovariance n ω E eta sigma *ᵥ x) ≤
      (1 / (sigma * eta)) * ∑ i, x i ^ 2 :=
  spectralCovariance_quadratic_bounds _ (D.realEigenvectorMatrix_transpose_mul n ω) _ _ _
    (D.resolventCovarianceWeight_bounds n ω E eta sigma heta hsigma) x

/-- Actual star/edge covariance compressions inherit the global bounds as soon
as their coordinate-selection rows are orthonormal. -/
theorem resolventCovariance_compression_bounds {J : Type*} [Fintype J] [DecidableEq J]
    (B : Matrix J (Fin (N n)) ℝ) (hB : B * B.transpose = 1)
    (E eta sigma : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma) (x : J → ℝ) :
    ((eta / sigma) / (((d : ℝ) + |E|) ^ 2 + eta ^ 2)) * (∑ i, x i ^ 2) ≤
      dotProduct x ((B * D.resolventCovariance n ω E eta sigma * B.transpose) *ᵥ x) ∧
    dotProduct x ((B * D.resolventCovariance n ω E eta sigma * B.transpose) *ᵥ x) ≤
      (1 / (sigma * eta)) * ∑ i, x i ^ 2 :=
  compression_quadratic_bounds _ B hB _ _
    (D.resolventCovariance_quadratic_bounds n ω E eta sigma heta hsigma) x

end GeneralizedBulk.External.RegularSpectralData
