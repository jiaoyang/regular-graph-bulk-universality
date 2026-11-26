import GeneralizedBulk.Gaussian.Marks
import GeneralizedBulk.Gaussian.CharacteristicUniqueness

/-! # Characteristic functions of the constructed Gaussian endpoint law -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GeneralizedBulk.Gaussian

theorem scalar_characteristic (t : ℝ) :
    (∫ x : ℝ, Complex.exp ((↑(t * x) : ℂ) * Complex.I) ∂standardNormal) =
      Complex.exp (-((t : ℂ) ^ 2) / 2) := by
  calc
    _ = complexMGF id standardNormal ((t : ℂ) * Complex.I) := by
      unfold complexMGF
      apply integral_congr_ae
      filter_upwards with x
      congr 1
      simp only [id_eq]
      push_cast
      ring
    _ = _ := by
      rw [standardNormal, complexMGF_id_gaussianReal]
      congr 1
      norm_num [mul_pow, Complex.I_sq]

theorem standardFour_characteristic (c : Fin 4 → ℝ) :
    (∫ x, Complex.exp ((linearForm c x : ℂ) * Complex.I) ∂standardFour) =
      Complex.exp (-(1 / 2 : ℂ) * (↑(∑ i, c i ^ 2) : ℂ)) := by
  have hprod : (fun x : Fin 4 → ℝ => Complex.exp ((linearForm c x : ℂ) * Complex.I)) =
      (fun x => ∏ i, Complex.exp ((↑(c i * x i) : ℂ) * Complex.I)) := by
    funext x
    simp only [linearForm, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  rw [hprod]
  have hfub : (∫ x, ∏ i, Complex.exp ((↑(c i * x i) : ℂ) * Complex.I) ∂standardFour) =
      ∏ i, ∫ t : ℝ, Complex.exp ((↑(c i * t) : ℂ) * Complex.I) ∂standardNormal := by
    letI : MeasureSpace ℝ := ⟨standardNormal⟩
    letI : IsProbabilityMeasure (volume : Measure ℝ) :=
      (inferInstance : IsProbabilityMeasure standardNormal)
    simpa only [standardFour, volume_pi] using
      integral_fintype_prod_eq_prod (Fin 4)
        (fun i : Fin 4 => fun t : ℝ => Complex.exp ((↑(c i * t) : ℂ) * Complex.I))
  rw [hfub]
  simp_rw [scalar_characteristic]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def covarianceQuadratic (p : ℝ) (t : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, t i * covarianceMatrix p i j * t j

def dualCoefficients (p : ℝ) (t : Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  ∑ i, t i * markCoefficients p i k

theorem linearForm_mark (p : ℝ) (t x : Fin 4 → ℝ) :
    linearForm t (mark p x) = linearForm (dualCoefficients p t) x := by
  simp only [linearForm, mark, dualCoefficients, Fin.sum_univ_four]
  ring

set_option maxHeartbeats 2000000 in
theorem dualCoefficients_norm (p : ℝ) (hp : |p| < 1) (t : Fin 4 → ℝ) :
    (∑ k, dualCoefficients p t k ^ 2) = covarianceQuadratic p t := by
  calc
    _ = ∑ i, ∑ j, t i * (∑ k, markCoefficients p i k * markCoefficients p j k) * t j := by
      simp only [dualCoefficients, Fin.sum_univ_four]
      ring
    _ = _ := by simp only [mark_covariance_coefficients p hp, covarianceQuadratic]

theorem mark_characteristic (p : ℝ) (hp : |p| < 1) (t : Fin 4 → ℝ) :
    (∫ x, Complex.exp ((linearForm t (mark p x) : ℂ) * Complex.I) ∂standardFour) =
      Complex.exp (-(1 / 2 : ℂ) * (covarianceQuadratic p t : ℂ)) := by
  simp_rw [linearForm_mark]
  rw [standardFour_characteristic, dualCoefficients_norm p hp]

theorem markLaw_characteristic (p : ℝ) (hp : |p| < 1) (t : Fin 4 → ℝ) :
    (∫ y, Complex.exp ((linearForm t y : ℂ) * Complex.I) ∂markLaw p) =
      Complex.exp (-(1 / 2 : ℂ) * (covarianceQuadratic p t : ℂ)) := by
  rw [markLaw, integral_map (measurable_mark p).aemeasurable]
  · exact mark_characteristic p hp t
  · apply Measurable.aestronglyMeasurable
    change Measurable (fun y : Fin 4 → ℝ => Complex.exp ((↑(∑ i, t i * y i) : ℂ) * Complex.I))
    fun_prop

def dualMatrix (O : Matrix (Fin 4) (Fin 4) ℝ) (t : Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  ∑ i, t i * O i k

theorem measurable_matrixAction (O : Matrix (Fin 4) (Fin 4) ℝ) :
    Measurable (fun x : Fin 4 → ℝ => O.mulVec x) := by
  apply measurable_pi_lambda
  intro i
  change Measurable (fun x : Fin 4 → ℝ => ∑ j : Fin 4, O i j * x j)
  exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j))

theorem linearForm_matrixAction (O : Matrix (Fin 4) (Fin 4) ℝ) (t x : Fin 4 → ℝ) :
    linearForm t (O.mulVec x) = linearForm (dualMatrix O t) x := by
  simp only [linearForm, dualMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

set_option maxHeartbeats 3000000 in
theorem covarianceQuadratic_matrixAction (p : ℝ) (O : Matrix (Fin 4) (Fin 4) ℝ)
    (hO : O * covarianceMatrix p * O.transpose = covarianceMatrix p)
    (t : Fin 4 → ℝ) :
    covarianceQuadratic p (dualMatrix O t) = covarianceQuadratic p t := by
  calc
    _ = ∑ i, ∑ j, t i * (O * covarianceMatrix p * O.transpose) i j * t j := by
      simp only [covarianceQuadratic, dualMatrix, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_four]
      ring
    _ = _ := by rw [hO]; rfl

/-- Every real covariance-preserving linear action preserves the actual
Gaussian endpoint probability law. This is deduced from characteristic
functions, with no invariance premise about the probability law. -/
theorem markLaw_matrixAction_invariant (p : ℝ) (hp : |p| < 1)
    (O : Matrix (Fin 4) (Fin 4) ℝ)
    (hO : O * covarianceMatrix p * O.transpose = covarianceMatrix p) :
    Measure.map (fun x : Fin 4 → ℝ => O.mulVec x) (markLaw p) = markLaw p := by
  letI : IsProbabilityMeasure (Measure.map (fun x : Fin 4 → ℝ => O.mulVec x) (markLaw p)) :=
    MeasureTheory.isProbabilityMeasure_map (measurable_matrixAction O).aemeasurable
  apply measure_eq_of_linear_characteristic
  intro t
  change (∫ x, Complex.exp ((linearForm t x : ℂ) * Complex.I)
    ∂Measure.map (fun x : Fin 4 → ℝ => O.mulVec x) (markLaw p)) =
      (∫ x, Complex.exp ((linearForm t x : ℂ) * Complex.I) ∂markLaw p)
  rw [integral_map (measurable_matrixAction O).aemeasurable]
  · simp_rw [linearForm_matrixAction]
    rw [markLaw_characteristic p hp, covarianceQuadratic_matrixAction p O hO,
      markLaw_characteristic p hp]
  · apply Measurable.aestronglyMeasurable
    change Measurable (fun y : Fin 4 → ℝ => Complex.exp ((↑(∑ i, t i * y i) : ℂ) * Complex.I))
    fun_prop

end GeneralizedBulk.Gaussian
