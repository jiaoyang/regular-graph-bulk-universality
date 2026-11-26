import GeneralizedBulk.Gaussian.Scalar

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Gaussian

def standardFour : Measure (Fin 4 → ℝ) := Measure.pi (fun _ => standardNormal)

instance : IsProbabilityMeasure standardFour := by
  unfold standardFour
  infer_instance

def monomial (e : Fin 4 → ℕ) (x : Fin 4 → ℝ) : ℝ := ∏ i, x i ^ e i

theorem integrable_monomial (e : Fin 4 → ℕ) : Integrable (monomial e) standardFour := by
  letI : MeasureSpace ℝ := ⟨standardNormal⟩
  letI : IsProbabilityMeasure (volume : Measure ℝ) := (inferInstance : IsProbabilityMeasure standardNormal)
  have h := Integrable.fintype_prod (fun i : Fin 4 => standardNormal_integrable_pow (e i))
  simpa only [monomial, standardFour, volume_pi] using h

theorem integral_monomial (e : Fin 4 → ℕ) :
    (∫ x, monomial e x ∂standardFour) = ∏ i, ∫ t : ℝ, t ^ e i ∂standardNormal := by
  letI : MeasureSpace ℝ := ⟨standardNormal⟩
  letI : IsProbabilityMeasure (volume : Measure ℝ) := (inferInstance : IsProbabilityMeasure standardNormal)
  simpa only [monomial, standardFour, volume_pi] using
    integral_fintype_prod_eq_prod (Fin 4) (fun i : Fin 4 => fun t : ℝ => t ^ e i)

private def exponent2 (i j : Fin 4) (k : Fin 4) : ℕ :=
  (if k = i then 1 else 0) + (if k = j then 1 else 0)

private def exponent4 (i j a b : Fin 4) (k : Fin 4) : ℕ :=
  (if k = i then 1 else 0) + (if k = j then 1 else 0) +
    (if k = a then 1 else 0) + (if k = b then 1 else 0)

private theorem monomial_exponent2 (i j : Fin 4) (x : Fin 4 → ℝ) :
    monomial (exponent2 i j) x = x i * x j := by
  fin_cases i <;> fin_cases j <;>
    simp +decide [monomial, exponent2, Fin.prod_univ_four] <;> ring <;> simp

set_option maxHeartbeats 2000000 in
private theorem monomial_exponent4 (i j a b : Fin 4) (x : Fin 4 → ℝ) :
    monomial (exponent4 i j a b) x = x i * x j * x a * x b := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp +decide [monomial, exponent4, Fin.prod_univ_four] <;> ring <;> simp

theorem integrable_coord_pair (i j : Fin 4) :
    Integrable (fun x : Fin 4 → ℝ => x i * x j) standardFour := by
  rw [← show (fun x : Fin 4 → ℝ => monomial (exponent2 i j) x) =
    (fun x => x i * x j) from funext (monomial_exponent2 i j)]
  exact integrable_monomial (exponent2 i j)

theorem integrable_coord_four (i j a b : Fin 4) :
    Integrable (fun x : Fin 4 → ℝ => x i * x j * x a * x b) standardFour := by
  rw [← show (fun x : Fin 4 → ℝ => monomial (exponent4 i j a b) x) =
    (fun x => x i * x j * x a * x b) from funext (monomial_exponent4 i j a b)]
  exact integrable_monomial (exponent4 i j a b)

theorem integral_coord_pair (i j : Fin 4) :
    (∫ x : Fin 4 → ℝ, x i * x j ∂standardFour) = if i = j then 1 else 0 := by
  rw [← show (fun x : Fin 4 → ℝ => monomial (exponent2 i j) x) =
      (fun x => x i * x j) from funext (monomial_exponent2 i j), integral_monomial]
  fin_cases i <;> fin_cases j <;>
    simp +decide [exponent2, Fin.prod_univ_four, standardNormal_moment_zero,
      standardNormal_moment_one, standardNormal_moment_two]

set_option maxHeartbeats 2000000 in
theorem integral_coord_four (i j a b : Fin 4) :
    (∫ x : Fin 4 → ℝ, x i * x j * x a * x b ∂standardFour) =
      (if i = j then 1 else 0) * (if a = b then 1 else 0) +
      (if i = a then 1 else 0) * (if j = b then 1 else 0) +
      (if i = b then 1 else 0) * (if j = a then 1 else 0) := by
  rw [← show (fun x : Fin 4 → ℝ => monomial (exponent4 i j a b) x) =
      (fun x => x i * x j * x a * x b) from funext (monomial_exponent4 i j a b),
    integral_monomial]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp +decide [exponent4, Fin.prod_univ_four, standardNormal_moment_zero,
      standardNormal_moment_one, standardNormal_moment_two, standardNormal_moment_three,
      standardNormal_moment_four] <;> norm_num

end GeneralizedBulk.Gaussian
