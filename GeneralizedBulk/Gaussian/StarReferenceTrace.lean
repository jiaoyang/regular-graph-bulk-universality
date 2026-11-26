import GeneralizedBulk.Gaussian.StarReferenceUniform
import GeneralizedBulk.Entropy.CovarianceFactorUniformBounds

/-! Exact finite-dimensional trace and uniform conditioning of the full star reference. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Gaussian
open GeneralizedBulk.External.RegularSpectralData GeneralizedBulk.Covariance GeneralizedBulk.Entropy

theorem starWaveCovariance_trace (d : ℕ) (E : ℝ) : Matrix.trace (starWaveCovariance d E)=d+1 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_succ, starWaveCovariance]
  ring

theorem starNormalProjection_trace (d : ℕ) (hd : 0 < d) (E : ℝ) : Matrix.trace (starNormalProjection d E)=1 := by
  change (∑ i, normalizedStarNormal d E i * normalizedStarNormal d E i)=1
  simpa only [pow_two] using normalizedStarNormal_sq_sum d hd E

theorem starReferenceCovariance_trace (d : ℕ) (hd : 0 < d) (E : ℝ) : Matrix.trace (starReferenceCovariance d E)=d+2 := by
  rw [starReferenceCovariance, Matrix.trace_add, starWaveCovariance_trace, starNormalProjection_trace d hd]
  ring

theorem starReference_uniform_factor_bounds (d : ℕ) (hd : 2 ≤ d) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K, |E| < d) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ E ∈ K, ∀ M : Matrix (Fin (d+1)) (Fin (d+1)) ℝ,
      M*M.transpose=starReferenceCovariance d E → M.det ≠ 0 →
      matrixSquareEnergy M ≤ d+2 ∧ matrixSquareEnergy M⁻¹ ≤ (d+1)/kappa ∧
      matrixEntryL1 M ≤ ((d+1 : ℕ) : ℝ)^2*Real.sqrt (d+2) ∧
      matrixEntryL1 M⁻¹ ≤ ((d+1 : ℕ) : ℝ)^2*Real.sqrt ((d+1)/kappa) ∧
      normalizationLoss M 1 ≤ ((d+1 : ℕ) : ℝ)^2/kappa := by
  obtain ⟨k,hk,hfloor⟩ := starReference_uniform_positive_floor d hd K hK hbulk
  refine ⟨k,hk,fun E hE M hM hdet => ?_⟩
  have hf (x : Fin (d+1) → ℝ) : k*(∑ i, x i^2) ≤ dotProduct x ((M*M.transpose).mulVec x) := by
    rw [hM]
    exact hfloor E hE x
  have ht : Matrix.trace (M*M.transpose) ≤ (d : ℝ)+2 := by
    rw [hM, starReferenceCovariance_trace d (by omega : 0 < d)]
  have hh := covariance_reference_uniform_bounds M hdet k ((d : ℝ)+2) hk (by positivity) hf ht
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hh

end GeneralizedBulk.Gaussian
