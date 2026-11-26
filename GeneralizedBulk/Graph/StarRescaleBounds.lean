import GeneralizedBulk.Graph.StarCompression
import GeneralizedBulk.Entropy.ProjectionRescaleBounds

/-! The literal normal rescaling converts local resolvent bounds to a nonsingular covariance comparison. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Covariance GeneralizedBulk.Gaussian GeneralizedBulk.Entropy
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem localEntropyStarCovariance_transpose (o : Fin (N n)) (E eta sigma : ℝ)
    (heta : 0 < eta) (hsigma : 0 < sigma) :
    (D.localEntropyStarCovariance n ω o E eta sigma).transpose = D.localEntropyStarCovariance n ω o E eta sigma := by
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (D.localEntropyStarCovariance_posDef n ω o E eta sigma heta hsigma).isHermitian

theorem abs_normalizedStarNormal_le_one (hd : 0 < d) (E : ℝ) (i : Fin (d+1)) :
    |normalizedStarNormal d E i| ≤ 1 := by
  have hh : normalizedStarNormal d E i ^ 2 ≤ 1 := by
    rw [← normalizedStarNormal_sq_sum d hd E]
    exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  exact (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).mp (by simpa only [sq_abs, one_pow] using hh)

theorem normalProjection_local_covariance_entry_bound (hd : 0 < d) (o : Fin (N n))
    (E eta sigma M : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma) (hM : 0 ≤ M)
    (hG : ∀ j : Fin (d+1), |(D.resolvent n ω (⟨E,eta⟩ : ℂ) o (D.entropyStarVertex n ω o j)).re| ≤ M)
    (i j : Fin (d+1)) :
    |(starNormalProjection d E * D.localEntropyStarCovariance n ω o E eta sigma) i j| ≤
      (eta / sigma / Real.sqrt ((d : ℝ)+E^2)) * M := by
  rw [starNormalProjection, unitNormalProjection_mul_entry,
    D.normalizedStarNormal_cross_covariance n ω o E eta sigma heta j, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ eta / sigma / Real.sqrt ((d : ℝ)+E^2))]
  have hh := mul_le_mul (abs_normalizedStarNormal_le_one hd E i) (hG j) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ eta / sigma / Real.sqrt ((d : ℝ)+E^2))
  nlinarith

theorem normalProjection_local_covariance_L1_bound (hd : 0 < d) (o : Fin (N n))
    (E eta sigma M : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma) (hM : 0 ≤ M)
    (hG : ∀ j : Fin (d+1), |(D.resolvent n ω (⟨E,eta⟩ : ℂ) o (D.entropyStarVertex n ω o j)).re| ≤ M) :
    matrixEntryL1 (starNormalProjection d E * D.localEntropyStarCovariance n ω o E eta sigma) ≤
      ((d+1 : ℕ) : ℝ) ^ 2 * (eta / sigma / Real.sqrt ((d : ℝ)+E^2)) * M := by
  calc
    _ ≤ ∑ _i : Fin (d+1), ∑ _j : Fin (d+1), (eta / sigma / Real.sqrt ((d : ℝ)+E^2)) * M :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        D.normalProjection_local_covariance_entry_bound n ω hd o E eta sigma M heta hsigma hM hG i j))
    _ = _ := by simp; ring

end GeneralizedBulk.External.RegularSpectralData
