import GeneralizedBulk.Gaussian.StandardVector

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Gaussian

/-- Every polynomial in the four actual independent normals is integrable. -/
theorem integrable_polynomial (P : MvPolynomial (Fin 4) ℝ) :
    Integrable (fun x : Fin 4 → ℝ => MvPolynomial.eval x P) standardFour := by
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
    simp only [MvPolynomial.eval_monomial]
    convert (integrable_monomial e).const_mul c using 1
    funext x
    congr 1
    exact Finsupp.prod_fintype e _ (fun i => pow_zero (x i))
  | add P Q hP hQ =>
    simpa only [MvPolynomial.eval_add] using hP.add hQ

def linearForm (c : Fin 4 → ℝ) (x : Fin 4 → ℝ) : ℝ := ∑ i, c i * x i

def linearPolynomial (c : Fin 4 → ℝ) : MvPolynomial (Fin 4) ℝ :=
  ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i

@[simp] theorem eval_linearPolynomial (c x : Fin 4 → ℝ) :
    MvPolynomial.eval x (linearPolynomial c) = linearForm c x := by
  simp [linearPolynomial, linearForm]

theorem integrable_linearForm_pow (c : Fin 4 → ℝ) (n : ℕ) :
    Integrable (fun x => linearForm c x ^ n) standardFour := by
  simpa only [map_pow, eval_linearPolynomial] using integrable_polynomial (linearPolynomial c ^ n)

theorem integrable_linearProduct {n : ℕ} (c : Fin n → Fin 4 → ℝ) :
    Integrable (fun x => ∏ j, linearForm (c j) x) standardFour := by
  simpa only [map_prod, eval_linearPolynomial] using
    integrable_polynomial (∏ j, linearPolynomial (c j))

theorem integrable_linearForm (c : Fin 4 → ℝ) :
    Integrable (linearForm c) standardFour := by
  simpa using integrable_linearForm_pow c 1

theorem integrable_coord (i : Fin 4) :
    Integrable (fun x : Fin 4 → ℝ => x i) standardFour := by
  simpa using integrable_polynomial (MvPolynomial.X i)

theorem integral_coord (i : Fin 4) :
    (∫ x : Fin 4 → ℝ, x i ∂standardFour) = 0 := by
  let e : Fin 4 → ℕ := fun j => if j = i then 1 else 0
  have heq : (fun x : Fin 4 → ℝ => monomial e x) = (fun x => x i) := by
    funext x
    fin_cases i <;> simp +decide [monomial, e, Fin.prod_univ_four]
  rw [← heq, integral_monomial]
  fin_cases i <;> simp +decide [e, Fin.prod_univ_four, standardNormal_moment_zero,
    standardNormal_moment_one]

theorem integral_linearForm (c : Fin 4 → ℝ) :
    (∫ x, linearForm c x ∂standardFour) = 0 := by
  unfold linearForm
  rw [integral_finset_sum _ (fun i _ => (integrable_coord i).const_mul _)]
  simp_rw [integral_const_mul, integral_coord]
  simp

theorem integrable_linear_pair (c d : Fin 4 → ℝ) :
    Integrable (fun x => linearForm c x * linearForm d x) standardFour := by
  simpa [Fin.prod_univ_two] using integrable_linearProduct ![c, d]

theorem integrable_linear_four (c d e f : Fin 4 → ℝ) :
    Integrable (fun x => linearForm c x * linearForm d x * linearForm e x * linearForm f x)
      standardFour := by
  convert integrable_linearProduct ![c, d, e, f] using 1
  funext x
  simp [Fin.prod_univ_four]

end GeneralizedBulk.Gaussian
