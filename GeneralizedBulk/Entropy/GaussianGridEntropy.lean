import GeneralizedBulk.Entropy.GridEntropyError
import GeneralizedBulk.Entropy.GridMoments
import GeneralizedBulk.Entropy.GaussianMixtureLaw

/-! The unbounded-grid entropy approximation for actual Gaussian mixtures. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

theorem continuous_affineGaussianPDF (mean : I → ℝ) (M : Matrix I I ℝ) : Continuous (affineGaussianPDF mean M) := by
  unfold affineGaussianPDF linearGaussianPDF standardGaussianPDF gaussianPDFReal
  fun_prop

theorem continuous_gaussianMixturePDF (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ) :
    Continuous (gaussianMixturePDF weight mean M) :=
  continuous_finset_sum _ (fun s _ => continuous_const.mul (continuous_affineGaussianPDF _ _))

def mixtureInverseEnergy (weight : S → ℝ) (M : S → Matrix I I ℝ) : ℝ :=
  ∑ s, weight s * ∑ i, ∑ j, (M s)⁻¹ i j ^ 2

theorem mixtureInverseEnergy_nonneg (weight : S → ℝ) (M : S → Matrix I I ℝ) (hw : ∀ s, 0 ≤ weight s) :
    0 ≤ mixtureInverseEnergy weight M :=
  Finset.sum_nonneg (fun s _ => mul_nonneg (hw s)
    (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))))

theorem inverse_action_energy_le (M : Matrix I I ℝ) (x : I → ℝ) :
    (∑ i, (M⁻¹.mulVec x i) ^ 2) ≤ (∑ i, ∑ j, M⁻¹ i j ^ 2) * ∑ j, x j ^ 2 := by
  calc
    _ ≤ ∑ i, (∑ j, M⁻¹ i j ^ 2) * ∑ j, x j ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (M⁻¹ i) x
    _ = _ := by rw [Finset.sum_mul]

theorem gaussianMixture_translation_energy (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hM : ∀ s, (M s).det ≠ 0) (h : I → ℝ) :
    Integrable (fun x => symmetrizedDensityPair (gaussianMixturePDF weight mean M) (x,x+h)) ∧
    (∫ x, symmetrizedDensityPair (gaussianMixturePDF weight mean M) (x,x+h)) ≤
      mixtureInverseEnergy weight M * ∑ i, h i ^ 2 := by
  have hp (x) := gaussianMixturePDF_pos weight mean M hw hnorm hM x
  have he (x) : symmetrizedDensityPair (gaussianMixturePDF weight mean M) (x,x+h) =
      (gaussianMixturePDF weight mean M x - gaussianMixturePDF weight mean M (x+h)) *
        Real.log (gaussianMixturePDF weight mean M x / gaussianMixturePDF weight mean M (x+h)) := by
    rw [Real.log_div (hp x).ne' (hp (x+h)).ne']
    rfl
  simp_rw [he]
  have hh := gaussianMixture_translation_symmetric_kl weight mean M hw hnorm hM h
  refine ⟨hh.1, hh.2.trans ?_⟩
  unfold mixtureInverseEnergy
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s hs
  have ha := mul_le_mul_of_nonneg_left (inverse_action_energy_le (M s) h) (hw s)
  simpa only [mul_assoc] using ha

theorem gaussianMixture_unclipped_grid_entropy {m : ℕ}
    (weight : S → ℝ) (mean : S → Fin m → ℝ) (M : S → Matrix (Fin m) (Fin m) ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hM : ∀ s, (M s).det ≠ 0)
    (a : ℝ) (ha : 0 < a) :
    0 ≤ countableEntropy (gridMass a (gaussianMixturePDF weight mean M)) + (m : ℝ) * Real.log a -
      differentialEntropy (gaussianMixturePDF weight mean M) ∧
    countableEntropy (gridMass a (gaussianMixturePDF weight mean M)) + (m : ℝ) * Real.log a -
      differentialEntropy (gaussianMixturePDF weight mean M) ≤
        ((2 : ℝ) ^ m / 2) * mixtureInverseEnergy weight M * m * a ^ 2 := by
  let f := gaussianMixturePDF weight mean M
  have hp (x) : 0 < f x := gaussianMixturePDF_pos weight mean M hw hnorm hM x
  have hi := integrable_gaussianMixturePDF weight mean M hM
  have hnormf := integral_gaussianMixturePDF weight mean M hnorm hM
  have hL1 := integrable_gaussianMixturePDF_mul_coordinateL1 weight mean M hM
  have hH := summable_grid_entropy a ha f (measurable_gaussianMixturePDF weight mean M)
    (fun x => (hp x).le) hi hnormf hL1
  have hg := grid_entropy_error_bound a ha f (continuous_gaussianMixturePDF weight mean M) hp hi
    (integrable_gaussianMixturePDF_mul_log weight mean M hw hnorm hM) hnormf hH
    (mixtureInverseEnergy weight M) (mixtureInverseEnergy_nonneg weight M hw)
    (fun h => (gaussianMixture_translation_energy weight mean M hw hnorm hM h).1)
    (fun h => (gaussianMixture_translation_energy weight mean M hw hnorm hM h).2)
  simp only [Fintype.card_fin] at hg
  have he : (2 * a ^ m)⁻¹ * (mixtureInverseEnergy weight M * m * a ^ 2) * (2 * a) ^ m =
      ((2 : ℝ) ^ m / 2) * mixtureInverseEnergy weight M * m * a ^ 2 := by
    rw [mul_pow]
    field_simp
    <;> ring
  rw [he] at hg
  simpa only [differentialEntropy, sub_neg_eq_add] using hg

end GeneralizedBulk.Entropy
