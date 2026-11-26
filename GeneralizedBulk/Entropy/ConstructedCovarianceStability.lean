import GeneralizedBulk.Entropy.GaussianMixtureStability
import GeneralizedBulk.Entropy.MatrixEntryAlgebra
import GeneralizedBulk.Matrix.RelativeNormalization
import GeneralizedBulk.Matrix.RelativeFactorBounds

/-! Actual covariance local laws construct the noise factors and every entropy stability input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Covariance GeneralizedBulk.Entropy.Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

def matrixSquareEnergy (M : Matrix I I ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

theorem matrixSquareEnergy_nonneg (M : Matrix I I ℝ) : 0 ≤ matrixSquareEnergy M :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

def covarianceFactorError (M : Matrix I I ℝ) (e : ℝ) : ℝ :=
  (Fintype.card I : ℝ)^2 * (Real.sqrt (matrixSquareEnergy M) * e)

def covarianceInverseFactorError (M : Matrix I I ℝ) (e : ℝ) : ℝ :=
  (Fintype.card I : ℝ)^2 * ((2*e) * Real.sqrt (matrixSquareEnergy M⁻¹))

theorem relativeFactor_entry_errors (M A : Matrix I I ℝ) (hM : M.det ≠ 0) (hA : A.PosDef)
    (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/2)
    (hc : ∀ x : I → ℝ, (1-e)*(∑ i, x i^2) ≤ dotProduct x (A.mulVec x) ∧
      dotProduct x (A.mulVec x) ≤ (1+e)*(∑ i, x i^2)) :
    matrixEntryL1 (referenceFactor M A hA-M) ≤ covarianceFactorError M e ∧
    matrixEntryL1 ((referenceFactor M A hA)⁻¹-M⁻¹) ≤ covarianceInverseFactorError M e := by
  constructor
  · apply matrixEntryL1_le_of_action_energy _ (Real.sqrt (matrixSquareEnergy M)*e) (by positivity)
    intro x
    have hh := referenceFactor_coupling_bound M A hA e he (by linarith) hc x
    rw [mul_pow, Real.sq_sqrt (matrixSquareEnergy_nonneg M)]
    exact hh
  · apply matrixEntryL1_le_of_action_energy _ ((2*e)*Real.sqrt (matrixSquareEnergy M⁻¹)) (by positivity)
    intro x
    have hh := referenceFactor_inv_coupling_bound M A hA e he he' hc x
    rw [mul_pow, Real.sq_sqrt (matrixSquareEnergy_nonneg M⁻¹)]
    exact hh

theorem exists_gaussianMixture_entropy_stable_factors
    (weight : S → ℝ) (mean : S → I → ℝ) (Q : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hQ : ∀ s, (Q s).PosDef)
    (M : Matrix I I ℝ) (hM : M.det ≠ 0) (B e : ℝ) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hsignal : ∀ s, coordinateL1 (mean s) ≤ B)
    (hclose : ∀ s i j, |(Q s-M*M.transpose) i j| ≤ e)
    (hsmall : normalizationLoss M e ≤ 1/2) :
    ∃ A : S → Matrix I I ℝ,
      (∀ s, A s*(A s).transpose=Q s ∧ (A s).det ≠ 0) ∧
      |differentialEntropy (gaussianMixturePDF weight mean A) -
        differentialEntropy (gaussianMixturePDF weight mean (fun _ => M))| ≤
      mixtureStabilityCoefficient B
        (matrixEntryL1 M+covarianceFactorError M (normalizationLoss M e))
        (matrixEntryL1 M⁻¹+covarianceInverseFactorError M (normalizationLoss M e))
        (Fintype.card I * normalizationLoss M e)
        (covarianceInverseFactorError M (normalizationLoss M e))
        (covarianceFactorError M (normalizationLoss M e)) * (1+(Fintype.card I : ℝ)^2) := by
  let C := fun s => normalizedCovariance M (Q s)
  have hC (s : S) : (C s).PosDef := normalizedCovariance_posDef M (Q s) hM (hQ s)
  let A := fun s => referenceFactor M (C s) (hC s)
  let eps := normalizationLoss M e
  have heps : 0 ≤ eps := by dsimp [eps,normalizationLoss]; positivity
  have hc (s : S) (x : I → ℝ) : (1-eps)*(∑ i, x i^2) ≤ dotProduct x ((C s).mulVec x) ∧
      dotProduct x ((C s).mulVec x) ≤ (1+eps)*(∑ i, x i^2) :=
    normalizedCovariance_quadratic_closeness M (Q s) hM e he (hclose s) x
  have hA (s : S) : A s*(A s).transpose=Q s ∧ (A s).det ≠ 0 := by
    refine ⟨?_,referenceFactor_det_ne_zero M (C s) hM (hC s)⟩
    rw [referenceFactor_covariance, normalizedCovariance_reconstruct M (Q s) hM]
  have herror (s : S) := relativeFactor_entry_errors M (C s) hM (hC s) eps heps hsmall (hc s)
  have hfac : 0 ≤ covarianceFactorError M eps := by unfold covarianceFactorError; positivity
  have hinv : 0 ≤ covarianceInverseFactorError M eps := by unfold covarianceInverseFactorError; positivity
  have hT (s : S) : matrixEntryL1 (A s) ≤ matrixEntryL1 M+covarianceFactorError M eps := by
    have hh := (matrixEntryL1_add_le M (A s-M)).trans (add_le_add_left (herror s).1 _)
    simpa only [add_sub_cancel] using hh
  have hL (s : S) : matrixEntryL1 (A s)⁻¹ ≤ matrixEntryL1 M⁻¹+covarianceInverseFactorError M eps := by
    have hh := (matrixEntryL1_add_le M⁻¹ ((A s)⁻¹-M⁻¹)).trans (add_le_add_left (herror s).2 _)
    simpa only [add_sub_cancel] using hh
  refine ⟨A,hA,?_⟩
  exact gaussianMixture_entropy_stability weight mean A (fun _ => M) hw hnorm
    (fun s => (hA s).2) (fun _ => hM) B
    (matrixEntryL1 M+covarianceFactorError M eps)
    (matrixEntryL1 M⁻¹+covarianceInverseFactorError M eps)
    (Fintype.card I*eps) (covarianceInverseFactorError M eps) (covarianceFactorError M eps)
    hB (add_nonneg (matrixEntryL1_nonneg _) hfac) (add_nonneg (matrixEntryL1_nonneg _) hinv)
    (by positivity) hinv hfac hsignal hT (fun _ => le_add_of_nonneg_right hfac) hL
    (fun _ => le_add_of_nonneg_right hinv)
    (fun s => referenceFactor_logabsdet_bound M (C s) hM (hC s) eps heps hsmall (hc s))
    (fun s => (herror s).2) (fun s => (herror s).1)

end GeneralizedBulk.Entropy
