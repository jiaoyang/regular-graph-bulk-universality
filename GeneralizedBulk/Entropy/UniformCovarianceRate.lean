import GeneralizedBulk.Entropy.ConstructedCovarianceRate
import GeneralizedBulk.Entropy.CovarianceFactorUniformBounds

/-! Uniform actual Gaussian-mixture entropy stability from covariance floor and trace bounds. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Covariance GeneralizedBulk.Entropy.Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

def uniformCovarianceEntropyRateConstant (I : Type*) [Fintype I] (kappa U : ℝ) : ℝ :=
  let m : ℝ := Fintype.card I
  let c := m^2/kappa
  let f := m^2*Real.sqrt U*c
  let invf := m^2*(2*c)*Real.sqrt (m/kappa)
  stabilityRateConstant (m^2*Real.sqrt U+f) (m^2*Real.sqrt (m/kappa)+invf) (m*c) invf f * (1+m^2)

set_option maxHeartbeats 800000 in
theorem covarianceEntropyRateConstant_le_uniform (M : Matrix I I ℝ) (hM : M.det ≠ 0)
    (kappa U : ℝ) (hkappa : 0 < kappa) (hU : 0 ≤ U)
    (hfloor : ∀ x : I → ℝ, kappa*(∑ i, x i^2) ≤ dotProduct x ((M*M.transpose).mulVec x))
    (htrace : Matrix.trace (M*M.transpose) ≤ U) :
    covarianceEntropyRateConstant M ≤ uniformCovarianceEntropyRateConstant I kappa U := by
  have hb := covariance_reference_uniform_bounds M hM kappa U hkappa hU hfloor htrace
  let c := normalizationLoss M 1
  let cb : ℝ := (Fintype.card I : ℝ)^2/kappa
  have hc0 : 0 ≤ c := by dsimp [c,normalizationLoss]; positivity
  have hcb0 : 0 ≤ cb := by dsimp [cb]; positivity
  have hc : c ≤ cb := hb.2.2.2.2
  have hf : covarianceFactorError M c ≤ (Fintype.card I : ℝ)^2*Real.sqrt U*cb := by
    unfold covarianceFactorError
    have hh := mul_le_mul (Real.sqrt_le_sqrt hb.1) hc hc0 (Real.sqrt_nonneg U)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (sq_nonneg (Fintype.card I : ℝ))
  have hi : covarianceInverseFactorError M c ≤ (Fintype.card I : ℝ)^2*(2*cb)*Real.sqrt (Fintype.card I/kappa) := by
    unfold covarianceInverseFactorError
    have hh := mul_le_mul (show 2*c ≤ 2*cb by linarith) (Real.sqrt_le_sqrt hb.2.1)
      (Real.sqrt_nonneg _) (by positivity : 0 ≤ 2*cb)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (sq_nonneg (Fintype.card I : ℝ))
  have hT := add_le_add hb.2.2.1 hf
  have hL := add_le_add hb.2.2.2.1 hi
  have hd := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (Fintype.card I))
  unfold covarianceEntropyRateConstant uniformCovarianceEntropyRateConstant
  dsimp only
  change stabilityRateConstant (matrixEntryL1 M+covarianceFactorError M c)
    (matrixEntryL1 M⁻¹+covarianceInverseFactorError M c) (Fintype.card I*c)
    (covarianceInverseFactorError M c) (covarianceFactorError M c)*(1+(Fintype.card I : ℝ)^2) ≤ _
  unfold stabilityRateConstant
  have hf0 : 0 ≤ covarianceFactorError M c := by unfold covarianceFactorError; positivity
  have hi0 : 0 ≤ covarianceInverseFactorError M c := by unfold covarianceInverseFactorError; positivity
  have hT0 := matrixEntryL1_nonneg M
  have hL0 := matrixEntryL1_nonneg M⁻¹
  gcongr

theorem exists_uniform_gaussianMixture_entropy_linear_rate
    (weight : S → ℝ) (mean : S → I → ℝ) (Q : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hQ : ∀ s, (Q s).PosDef)
    (M : Matrix I I ℝ) (hM : M.det ≠ 0) (kappa U : ℝ) (hkappa : 0 < kappa) (hU : 0 ≤ U)
    (hfloor : ∀ x : I → ℝ, kappa*(∑ i, x i^2) ≤ dotProduct x ((M*M.transpose).mulVec x))
    (htrace : Matrix.trace (M*M.transpose) ≤ U)
    (B e : ℝ) (hB : 0 ≤ B) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hsignal : ∀ s, coordinateL1 (mean s) ≤ B) (hclose : ∀ s i j, |(Q s-M*M.transpose) i j| ≤ e)
    (hsmall : ((Fintype.card I : ℝ)^2/kappa)*e ≤ 1/2) :
    ∃ A : S → Matrix I I ℝ,
      (∀ s, A s*(A s).transpose=Q s ∧ (A s).det ≠ 0) ∧
      |differentialEntropy (gaussianMixturePDF weight mean A) -
        differentialEntropy (gaussianMixturePDF weight mean (fun _ => M))| ≤
      uniformCovarianceEntropyRateConstant I kappa U*(1+B^2)*e := by
  have hb := covariance_reference_uniform_bounds M hM kappa U hkappa hU hfloor htrace
  have hs : normalizationLoss M e ≤ 1/2 := by
    have heq : normalizationLoss M e=normalizationLoss M 1*e := by unfold normalizationLoss; ring
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hb.2.2.2.2 he).trans hsmall
  obtain ⟨A,hA,hEnt⟩ := exists_gaussianMixture_entropy_linear_rate weight mean Q hw hnorm hQ M hM B e hB he he1 hsignal hclose hs
  refine ⟨A,hA,hEnt.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (covarianceEntropyRateConstant_le_uniform M hM kappa U hkappa hU hfloor htrace) (by positivity)) he

end GeneralizedBulk.Entropy
