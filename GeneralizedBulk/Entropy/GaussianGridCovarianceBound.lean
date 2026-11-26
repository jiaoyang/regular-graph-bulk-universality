import GeneralizedBulk.Entropy.GaussianGridEntropy
import GeneralizedBulk.Matrix.InverseEnergy

/-! The grid error is uniform under the actual covariance lower bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Covariance
variable {S : Type*} [Fintype S]

theorem gaussianMixture_grid_error_of_covariance_lower {m : ℕ}
    (weight : S → ℝ) (mean : S → Fin m → ℝ) (M : S → Matrix (Fin m) (Fin m) ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hM : ∀ s, (M s).det ≠ 0)
    (lo : ℝ) (hlo : 0 < lo)
    (hcov : ∀ s (x : Fin m → ℝ), lo * (∑ i, x i ^ 2) ≤
      dotProduct x ((M s * (M s).transpose).mulVec x)) (a : ℝ) (ha : 0 < a) :
    0 ≤ countableEntropy (gridMass a (gaussianMixturePDF weight mean M)) + (m : ℝ) * Real.log a -
      differentialEntropy (gaussianMixturePDF weight mean M) ∧
    countableEntropy (gridMass a (gaussianMixturePDF weight mean M)) + (m : ℝ) * Real.log a -
      differentialEntropy (gaussianMixturePDF weight mean M) ≤ ((2 : ℝ) ^ m / 2) * (m / lo) * m * a ^ 2 := by
  have hg := gaussianMixture_unclipped_grid_entropy weight mean M hw hnorm hM a ha
  have henergy : mixtureInverseEnergy weight M ≤ (m : ℝ) / lo := by
    calc
      _ ≤ ∑ s, weight s * ((m : ℝ) / lo) := by
        apply Finset.sum_le_sum
        intro s hs
        have hs' := inverse_frobenius_energy_le (M s) (hM s) lo hlo (hcov s)
        simp only [Fintype.card_fin] at hs'
        exact mul_le_mul_of_nonneg_left hs' (hw s)
      _ = _ := by rw [← Finset.sum_mul, hnorm, one_mul]
  refine ⟨hg.1, hg.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left henergy (by positivity)) (Nat.cast_nonneg m)) (sq_nonneg a)

end GeneralizedBulk.Entropy
