import GeneralizedBulk.Gaussian.Marks

/-! # Independent centered quadratic Gaussian marks in complex L² -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate

namespace GeneralizedBulk.Gaussian

private theorem covarianceMatrix_ofReal (p : ℝ) (i j : Fin 4) :
    ((covarianceMatrix p i j : ℝ) : ℂ) = covarianceMatrix (p : ℂ) i j := by
  rw [covarianceMatrix_eq, covarianceMatrix_eq]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

def quadraticFamily (p : ℝ) {I : Type*} (n : I) (i j : Fin 4)
    (ω : I → (Fin 4 → ℝ)) : ℝ := centeredQuadratic p i j (ω n)

theorem measurable_quadraticFamily (p : ℝ) {I : Type*} (n : I) (i j : Fin 4) :
    Measurable (quadraticFamily p n i j) :=
  (measurable_centeredQuadratic p i j).comp (measurable_pi_apply n)

theorem quadraticFamily_memLp_two (p : ℝ) {I : Type*} (n : I) (i j : Fin 4) :
    MemLp (quadraticFamily p n i j) 2 (iidLaw standardFour I) :=
  (centeredQuadratic_memLp_two p i j).comp_measurePreserving
    (iidLaw_eval_measurePreserving standardFour I n)

theorem integrable_quadraticFamily_pow (p : ℝ) {I : Type*} (n : I) (i j : Fin 4) (q : ℕ) :
    Integrable (fun ω => quadraticFamily p n i j ω ^ q) (iidLaw standardFour I) := by
  exact ((iidLaw_eval_measurePreserving standardFour I n).integrable_comp
    (integrable_centeredQuadratic_pow p i j q).aestronglyMeasurable).2
      (integrable_centeredQuadratic_pow p i j q)

theorem quadraticFamily_mean_zero (p : ℝ) (hp : |p| < 1)
    {I : Type*} (n : I) (i j : Fin 4) :
    (∫ ω, quadraticFamily p n i j ω ∂iidLaw standardFour I) = 0 := by
  rw [show (fun ω => quadraticFamily p n i j ω) =
    (fun ω => centeredQuadratic p i j (ω n)) from rfl,
    integral_iid_eval standardFour I n _
      (measurable_centeredQuadratic p i j).aestronglyMeasurable]
  exact centeredQuadratic_mean_zero p hp i j

theorem quadraticFamily_iIndepFun (p : ℝ) (I : Type*) (i j : Fin 4) :
    iIndepFun (fun n : I => quadraticFamily p n i j) (iidLaw standardFour I) :=
  (iidLaw_eval_iIndepFun standardFour I).comp (fun _ => centeredQuadratic p i j)
    (fun _ => measurable_centeredQuadratic p i j)

theorem quadraticFamily_off_covariance (p : ℝ) (hp : |p| < 1)
    {I : Type*} {n m : I} (hnm : n ≠ m) (i j a b : Fin 4) :
    (∫ ω, quadraticFamily p n i j ω * quadraticFamily p m a b ω
      ∂iidLaw standardFour I) = 0 := by
  have hind := ((iidLaw_eval_iIndepFun standardFour I).indepFun hnm).comp
    (measurable_centeredQuadratic p i j) (measurable_centeredQuadratic p a b)
  have hi : Integrable (quadraticFamily p n i j) (iidLaw standardFour I) := by
    simpa using integrable_quadraticFamily_pow p n i j 1
  have hj : Integrable (quadraticFamily p m a b) (iidLaw standardFour I) := by
    simpa using integrable_quadraticFamily_pow p m a b 1
  have hmul : (∫ ω, quadraticFamily p n i j ω * quadraticFamily p m a b ω
      ∂iidLaw standardFour I) =
      (∫ ω, quadraticFamily p n i j ω ∂iidLaw standardFour I) *
      (∫ ω, quadraticFamily p m a b ω ∂iidLaw standardFour I) := by
    simpa only [quadraticFamily, Function.comp_def, Pi.mul_apply] using
      hind.integral_mul_of_integrable hi hj
  rw [hmul]
  simp only [quadraticFamily_mean_zero p hp, zero_mul]

theorem quadraticFamily_diagonal_covariance (p : ℝ) (hp : |p| < 1)
    {I : Type*} (n : I) (i j a b : Fin 4) :
    (∫ ω, quadraticFamily p n i j ω * quadraticFamily p n a b ω
      ∂iidLaw standardFour I) =
      covarianceMatrix p i a * covarianceMatrix p j b +
      covarianceMatrix p i b * covarianceMatrix p j a := by
  change (∫ ω, (fun x => centeredQuadratic p i j x * centeredQuadratic p a b x) (ω n)
    ∂iidLaw standardFour I) = _
  rw [integral_iid_eval standardFour I n _
    (integrable_centeredQuadratic_product p i j a b).aestronglyMeasurable]
  exact centeredQuadratic_covariance p hp i j a b

def quadraticLp (p : ℝ) {I : Type*} (n : I) (i j : Fin 4) :
    Lp ℂ 2 (iidLaw standardFour I) :=
  ((quadraticFamily_memLp_two p n i j).ofReal (K := ℂ)).toLp
    (fun ω => (quadraticFamily p n i j ω : ℂ))

theorem quadraticLp_ae (p : ℝ) {I : Type*} (n : I) (i j : Fin 4) :
    (quadraticLp p n i j : (I → (Fin 4 → ℝ)) → ℂ) =ᵐ[iidLaw standardFour I]
      (fun ω => (quadraticFamily p n i j ω : ℂ)) :=
  MemLp.coeFn_toLp _

theorem quadraticLp_mean_zero (p : ℝ) (hp : |p| < 1)
    {I : Type*} (n : I) (i j : Fin 4) :
    (∫ ω, quadraticLp p n i j ω ∂iidLaw standardFour I) = 0 := by
  rw [integral_congr_ae (quadraticLp_ae p n i j), integral_complex_ofReal]
  simp [quadraticFamily_mean_zero p hp]

theorem quadraticLp_off_covariance (p : ℝ) (hp : |p| < 1)
    {I : Type*} {n m : I} (hnm : n ≠ m) (i j a b : Fin 4) :
    (∫ ω, quadraticLp p n i j ω * quadraticLp p m a b ω
      ∂iidLaw standardFour I) = 0 := by
  have heq : (fun ω => quadraticLp p n i j ω * quadraticLp p m a b ω) =ᵐ[iidLaw standardFour I]
      (fun ω => ((quadraticFamily p n i j ω * quadraticFamily p m a b ω : ℝ) : ℂ)) := by
    filter_upwards [quadraticLp_ae p n i j, quadraticLp_ae p m a b] with ω hi hj
    simp only [hi, hj, Complex.ofReal_mul]
  rw [integral_congr_ae heq, integral_complex_ofReal, quadraticFamily_off_covariance p hp hnm]
  rfl

theorem quadraticLp_diagonal_covariance (p : ℝ) (hp : |p| < 1)
    {I : Type*} (n : I) (i j a b : Fin 4) :
    (∫ ω, quadraticLp p n i j ω * quadraticLp p n a b ω
      ∂iidLaw standardFour I) =
      covarianceMatrix (p : ℂ) i a * covarianceMatrix (p : ℂ) j b +
      covarianceMatrix (p : ℂ) i b * covarianceMatrix (p : ℂ) j a := by
  have heq : (fun ω => quadraticLp p n i j ω * quadraticLp p n a b ω) =ᵐ[iidLaw standardFour I]
      (fun ω => ((quadraticFamily p n i j ω * quadraticFamily p n a b ω : ℝ) : ℂ)) := by
    filter_upwards [quadraticLp_ae p n i j, quadraticLp_ae p n a b] with ω hi hj
    simp only [hi, hj, Complex.ofReal_mul]
  rw [integral_congr_ae heq, integral_complex_ofReal, quadraticFamily_diagonal_covariance p hp]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, covarianceMatrix_ofReal]

end GeneralizedBulk.Gaussian
