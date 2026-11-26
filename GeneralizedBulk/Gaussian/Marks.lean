import GeneralizedBulk.Gaussian.LinearMoments
import GeneralizedBulk.Gaussian.IID
import GeneralizedBulk.RealGeometry

/-!
# Gaussian endpoint marks and their actual Wick moments

The marks are an explicit linear image of four independent standard real
Gaussian coordinates. Moment identities below are proved from that measure,
not supplied as fields of a covariance certificate.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Gaussian

def markCoefficients (p : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     p, Real.sqrt (1 - p ^ 2), 0, 0;
     0, 0, 1, 0;
     0, 0, p, Real.sqrt (1 - p ^ 2)]

def mark (p : ℝ) (x : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  linearForm (markCoefficients p i) x

theorem measurable_mark (p : ℝ) : Measurable (mark p) := by
  apply measurable_pi_lambda
  intro i
  change Measurable (fun x : Fin 4 → ℝ => ∑ j : Fin 4, markCoefficients p i j * x j)
  exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j))

def markLaw (p : ℝ) : Measure (Fin 4 → ℝ) := Measure.map (mark p) standardFour

instance (p : ℝ) : IsProbabilityMeasure (markLaw p) :=
  MeasureTheory.isProbabilityMeasure_map (measurable_mark p).aemeasurable

theorem mark_covariance_coefficients (p : ℝ) (hp : |p| < 1) (i j : Fin 4) :
    (∑ k, markCoefficients p i k * markCoefficients p j k) = covarianceMatrix p i j := by
  have hs : Real.sqrt (1 - p ^ 2) ^ 2 = 1 - p ^ 2 :=
    Real.sq_sqrt (sub_nonneg.mpr ((sq_lt_one_iff_abs_lt_one p).2 hp).le)
  rw [covarianceMatrix_eq]
  fin_cases i <;> fin_cases j <;>
    simp [markCoefficients, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> nlinarith [hs]

theorem integrable_mark_pow (p : ℝ) (i : Fin 4) (n : ℕ) :
    Integrable (fun x => mark p x i ^ n) standardFour :=
  integrable_linearForm_pow (markCoefficients p i) n

theorem integrable_mark (p : ℝ) (i : Fin 4) :
    Integrable (fun x => mark p x i) standardFour :=
  integrable_linearForm (markCoefficients p i)

theorem mark_mean_zero (p : ℝ) (i : Fin 4) :
    (∫ x, mark p x i ∂standardFour) = 0 :=
  integral_linearForm (markCoefficients p i)

theorem integrable_mark_pair (p : ℝ) (i j : Fin 4) :
    Integrable (fun x => mark p x i * mark p x j) standardFour :=
  integrable_linear_pair _ _

theorem mark_covariance (p : ℝ) (hp : |p| < 1) (i j : Fin 4) :
    (∫ x, mark p x i * mark p x j ∂standardFour) = covarianceMatrix p i j := by
  rw [show (fun x => mark p x i * mark p x j) =
    (fun x => linearForm (markCoefficients p i) x * linearForm (markCoefficients p j) x) from rfl]
  rw [integral_linear_pair, mark_covariance_coefficients p hp]

theorem integrable_mark_four (p : ℝ) (i j a b : Fin 4) :
    Integrable (fun x => mark p x i * mark p x j * mark p x a * mark p x b) standardFour :=
  integrable_linear_four _ _ _ _

theorem mark_fourth_moment (p : ℝ) (hp : |p| < 1) (i j a b : Fin 4) :
    (∫ x, mark p x i * mark p x j * mark p x a * mark p x b ∂standardFour) =
      covarianceMatrix p i j * covarianceMatrix p a b +
      covarianceMatrix p i a * covarianceMatrix p j b +
      covarianceMatrix p i b * covarianceMatrix p j a := by
  change (∫ x, linearForm _ x * linearForm _ x * linearForm _ x * linearForm _ x
    ∂standardFour) = _
  rw [integral_linear_four]
  simp_rw [mark_covariance_coefficients p hp]

def centeredQuadratic (p : ℝ) (i j : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  mark p x i * mark p x j - covarianceMatrix p i j

def quadraticPolynomial (p : ℝ) (i j : Fin 4) : MvPolynomial (Fin 4) ℝ :=
  linearPolynomial (markCoefficients p i) * linearPolynomial (markCoefficients p j) -
    MvPolynomial.C (covarianceMatrix p i j)

@[simp] theorem eval_quadraticPolynomial (p : ℝ) (i j : Fin 4) (x : Fin 4 → ℝ) :
    MvPolynomial.eval x (quadraticPolynomial p i j) = centeredQuadratic p i j x := by
  simp [quadraticPolynomial, centeredQuadratic, mark]

theorem measurable_centeredQuadratic (p : ℝ) (i j : Fin 4) :
    Measurable (centeredQuadratic p i j) := by
  exact (((measurable_pi_apply i).comp (measurable_mark p)).mul
    ((measurable_pi_apply j).comp (measurable_mark p))).sub_const _

theorem integrable_centeredQuadratic_pow (p : ℝ) (i j : Fin 4) (n : ℕ) :
    Integrable (fun x => centeredQuadratic p i j x ^ n) standardFour := by
  simpa only [map_pow, eval_quadraticPolynomial] using
    integrable_polynomial (quadraticPolynomial p i j ^ n)

theorem integrable_centeredQuadratic (p : ℝ) (i j : Fin 4) :
    Integrable (centeredQuadratic p i j) standardFour := by
  simpa using integrable_centeredQuadratic_pow p i j 1

theorem centeredQuadratic_memLp_two (p : ℝ) (i j : Fin 4) :
    MemLp (centeredQuadratic p i j) 2 standardFour := by
  exact (memLp_two_iff_integrable_sq
    (measurable_centeredQuadratic p i j).aestronglyMeasurable).2
      (integrable_centeredQuadratic_pow p i j 2)

theorem centeredQuadratic_mean_zero (p : ℝ) (hp : |p| < 1) (i j : Fin 4) :
    (∫ x, centeredQuadratic p i j x ∂standardFour) = 0 := by
  change (∫ x, mark p x i * mark p x j - covarianceMatrix p i j ∂standardFour) = 0
  rw [integral_sub (integrable_mark_pair p i j) (integrable_const _)]
  simp [mark_covariance p hp]

theorem integrable_centeredQuadratic_product (p : ℝ) (i j a b : Fin 4) :
    Integrable (fun x => centeredQuadratic p i j x * centeredQuadratic p a b x)
      standardFour := by
  simpa only [map_mul, eval_quadraticPolynomial] using
    integrable_polynomial (quadraticPolynomial p i j * quadraticPolynomial p a b)

/-- Wick covariance of centered quadratic marks under the constructed Gaussian law. -/
theorem centeredQuadratic_covariance (p : ℝ) (hp : |p| < 1) (i j a b : Fin 4) :
    (∫ x, centeredQuadratic p i j x * centeredQuadratic p a b x ∂standardFour) =
      covarianceMatrix p i a * covarianceMatrix p j b +
      covarianceMatrix p i b * covarianceMatrix p j a := by
  let U : (Fin 4 → ℝ) → ℝ := fun x => mark p x i * mark p x j * mark p x a * mark p x b
  let V : (Fin 4 → ℝ) → ℝ := fun x => covarianceMatrix p a b * (mark p x i * mark p x j)
  let W : (Fin 4 → ℝ) → ℝ := fun x => covarianceMatrix p i j * (mark p x a * mark p x b)
  let K : (Fin 4 → ℝ) → ℝ := fun _ => covarianceMatrix p i j * covarianceMatrix p a b
  have hU : Integrable U standardFour := integrable_mark_four p i j a b
  have hV : Integrable V standardFour := (integrable_mark_pair p i j).const_mul _
  have hW : Integrable W standardFour := (integrable_mark_pair p a b).const_mul _
  have hK : Integrable K standardFour := integrable_const _
  have heq : (fun x => centeredQuadratic p i j x * centeredQuadratic p a b x) =
      (U - V - W) + K := by
    funext x
    simp only [U, V, W, K, Pi.add_apply, Pi.sub_apply, centeredQuadratic]
    ring
  rw [heq]
  change (∫ x, (U - V - W) x + K x ∂standardFour) = _
  rw [integral_add ((hU.sub hV).sub hW) hK]
  change (∫ x, (U - V) x - W x ∂standardFour) + (∫ x, K x ∂standardFour) = _
  rw [integral_sub (hU.sub hV) hW]
  change ((∫ x, U x - V x ∂standardFour) - (∫ x, W x ∂standardFour)) +
    (∫ x, K x ∂standardFour) = _
  rw [integral_sub hU hV]
  simp only [U, V, W, K, integral_const_mul, mark_fourth_moment p hp,
    mark_covariance p hp, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  ring

end GeneralizedBulk.Gaussian
