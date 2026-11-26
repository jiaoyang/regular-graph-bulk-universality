import GeneralizedBulk.Graph.StarRescaleBounds
import GeneralizedBulk.Gaussian.StarReferenceUniform
import GeneralizedBulk.Matrix.ProjectionRescalePositive

/-! Actual nonsingular full-star covariance after normal rescaling, with its precise error. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Covariance GeneralizedBulk.Gaussian GeneralizedBulk.Entropy
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def rescaledLocalStarCovariance (o : Fin (N n)) (E eta sigma : ℝ) : Matrix (Fin (d+1)) (Fin (d+1)) ℝ :=
  projectionRescale (starNormalProjection d E) (starNormalRescaleFactor d E eta sigma) *
    D.localEntropyStarCovariance n ω o E eta sigma *
      projectionRescale (starNormalProjection d E) (starNormalRescaleFactor d E eta sigma)

theorem starNormalRescaleFactor_pos (hd : 0 < d) (E eta sigma : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma) :
    0 < starNormalRescaleFactor d E eta sigma := by
  apply Real.sqrt_pos.mpr
  exact div_pos (mul_pos hsigma (add_pos_of_pos_of_nonneg (Nat.cast_pos.mpr hd) (sq_nonneg E))) heta

theorem rescaledLocalStarCovariance_posDef (hd : 0 < d) (o : Fin (N n))
    (E eta sigma : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma) :
    (D.rescaledLocalStarCovariance n ω o E eta sigma).PosDef :=
  projectionRescale_congruence_posDef _ _ (starNormalProjection_idempotent d hd E)
    (starNormalProjection_transpose d E) (D.localEntropyStarCovariance_posDef n ω o E eta sigma heta hsigma) _
    (starNormalRescaleFactor_pos hd E eta sigma heta hsigma).ne'

theorem starNormalRescale_det (hd : 0 < d) (E eta sigma : ℝ) :
    (projectionRescale (starNormalProjection d E) (starNormalRescaleFactor d E eta sigma)).det =
      starNormalRescaleFactor d E eta sigma :=
  projectionRescale_unitNormal_det _ (normalizedStarNormal_sq_sum d hd E) _

theorem rescaledLocalStarCovariance_error_bound (hd : 2 ≤ d) (o : Fin (N n))
    (E eta sigma : ℝ) (hE : |E| < d) (heta : 0 < eta) (hsigma : 0 < sigma) :
    let P := starNormalProjection d E
    let Q := D.localEntropyStarCovariance n ω o E eta sigma
    let t := starNormalRescaleFactor d E eta sigma
    matrixEntryL1 (D.rescaledLocalStarCovariance n ω o E eta sigma - starReferenceCovariance d E) ≤
      matrixEntryL1 (1-P)^2 * matrixEntryL1 (Q-starWaveCovariance d E) +
        2*|t| *matrixEntryL1 (1-P)*matrixEntryL1 (P*Q) +
          sigma*eta*|D.resolventCovariance n ω E eta sigma o o| *matrixEntryL1 P := by
  let P := starNormalProjection d E
  let Q := D.localEntropyStarCovariance n ω o E eta sigma
  let t := starNormalRescaleFactor d E eta sigma
  let Err := (-eta^2*D.resolventCovariance n ω E eta sigma o o/((d : ℝ)+E^2)) • P
  have hdpos : 0 < d := by omega
  have hb : 0 < (d : ℝ)+E^2 := add_pos_of_pos_of_nonneg (Nat.cast_pos.mpr hdpos) (sq_nonneg E)
  have hnormal : P*Q*P=starNormalVarianceScale d E eta sigma • P+Err :=
    D.starNormalProjection_local_covariance n ω hdpos o E eta sigma heta
  have htq := starNormalRescaleFactor_sq_scale (d := d) hdpos E eta sigma heta hsigma
  have hg := projectionRescale_covariance_error_bound P Q (starWaveCovariance d E) Err t
    (starNormalVarianceScale d E eta sigma) (starNormalProjection_wave_left d hd E hE)
    (starNormalProjection_wave_right d hd E hE) hnormal htq
  have hc := projection_cross_matrixEntryL1_bound P Q (starNormalProjection_transpose d E)
    (D.localEntropyStarCovariance_transpose n ω o E eta sigma heta hsigma)
  have hvar : t^2*matrixEntryL1 Err = sigma*eta*|D.resolventCovariance n ω E eta sigma o o| *matrixEntryL1 P := by
    dsimp [Err]
    rw [matrixEntryL1_smul]
    have ha : |(-eta^2*D.resolventCovariance n ω E eta sigma o o/((d : ℝ)+E^2))| =
        eta^2*|D.resolventCovariance n ω E eta sigma o o|/((d : ℝ)+E^2) := by
      rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg eta), abs_of_pos hb]
    rw [ha]
    have ht : t^2 = sigma*((d : ℝ)+E^2)/eta := Real.sq_sqrt (by positivity)
    rw [ht]
    field_simp
    <;> ring
  have hm := mul_le_mul_of_nonneg_left hc (abs_nonneg t)
  rw [hvar] at hg
  change matrixEntryL1 (D.rescaledLocalStarCovariance n ω o E eta sigma-starReferenceCovariance d E) ≤ _ at hg
  exact hg.trans (by nlinarith [hm])

end GeneralizedBulk.External.RegularSpectralData
