import GeneralizedBulk.Gaussian.FiniteVector

/-! Exact joint characteristic function of finitely many independent endpoint marks. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Gaussian

def flattenMarks {α : Type*} (y : α → Fin 4 → ℝ) (aj : α × Fin 4) : ℝ := y aj.1 aj.2

theorem measurable_flattenMarks {α : Type*} : Measurable (flattenMarks (α := α)) := by
  apply measurable_pi_lambda
  intro aj
  exact (measurable_pi_apply aj.2).comp (measurable_pi_apply aj.1)

def finiteMarkLaw (p : ℝ) (k : ℕ) : Measure ((Fin k × Fin 4) → ℝ) :=
  Measure.map flattenMarks (Measure.pi (fun _ : Fin k => markLaw p))

instance (p : ℝ) (k : ℕ) : IsProbabilityMeasure (finiteMarkLaw p k) := by
  letI : ∀ _ : Fin k, IsProbabilityMeasure (markLaw p) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin k => markLaw p)) :=
    Measure.pi.instIsProbabilityMeasure _
  unfold finiteMarkLaw
  exact MeasureTheory.isProbabilityMeasure_map (μ := Measure.pi (fun _ : Fin k => markLaw p))
    measurable_flattenMarks.aemeasurable

def finiteMarkCovariance (p : ℝ) (k : ℕ) : Matrix (Fin k × Fin 4) (Fin k × Fin 4) ℝ :=
  fun ai bj => (if ai.1 = bj.1 then 1 else 0) * covarianceMatrix p ai.2 bj.2

theorem finiteMarkCovariance_quadratic (p : ℝ) (k : ℕ) (t : (Fin k × Fin 4) → ℝ) :
    finiteCovarianceQuadratic (finiteMarkCovariance p k) t =
      ∑ a : Fin k, finiteCovarianceQuadratic (covarianceMatrix p) (fun i => t (a, i)) := by
  simp [finiteCovarianceQuadratic, finiteMarkCovariance, Fintype.sum_prod_type,
    mul_ite, ite_mul, Finset.sum_ite_irrel]

theorem finiteMarkLaw_characteristic (p : ℝ) (hp : |p| < 1) (k : ℕ)
    (t : (Fin k × Fin 4) → ℝ) :
    (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂finiteMarkLaw p k) =
      Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic (finiteMarkCovariance p k) t) : ℂ) := by
  have hm : AEStronglyMeasurable
      (fun x => Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I)) (finiteMarkLaw p k) := by
    apply Measurable.aestronglyMeasurable
    exact Complex.continuous_exp.measurable.comp
      ((continuous_finiteLinearForm t).measurable.complex_ofReal.mul measurable_const)
  rw [finiteMarkLaw, integral_map measurable_flattenMarks.aemeasurable hm]
  have hprod : (fun y : Fin k → Fin 4 → ℝ =>
      Complex.exp ((↑(finiteLinearForm t (flattenMarks y)) : ℂ) * Complex.I)) =
      (fun y => ∏ a : Fin k, Complex.exp ((↑(finiteLinearForm (fun i => t (a, i)) (y a)) : ℂ) * Complex.I)) := by
    funext y
    simp only [finiteLinearForm, flattenMarks, Fintype.sum_prod_type, Complex.ofReal_sum,
      Finset.sum_mul, Complex.exp_sum]
  rw [hprod]
  have hfub : (∫ y, ∏ a : Fin k,
      Complex.exp ((↑(finiteLinearForm (fun i => t (a, i)) (y a)) : ℂ) * Complex.I)
        ∂Measure.pi (fun _ : Fin k => markLaw p)) =
      ∏ a : Fin k, ∫ y, Complex.exp ((↑(finiteLinearForm (fun i => t (a, i)) y) : ℂ) * Complex.I) ∂markLaw p := by
    letI : MeasureSpace (Fin 4 → ℝ) := ⟨markLaw p⟩
    letI : IsProbabilityMeasure (volume : Measure (Fin 4 → ℝ)) :=
      (inferInstance : IsProbabilityMeasure (markLaw p))
    simpa only [volume_pi] using integral_fintype_prod_eq_prod (Fin k)
      (fun a : Fin k => fun y : Fin 4 → ℝ =>
        Complex.exp ((↑(finiteLinearForm (fun i => t (a, i)) y) : ℂ) * Complex.I))
  rw [hfub]
  have ha (a : Fin k) : (∫ y, Complex.exp ((↑(finiteLinearForm (fun i => t (a, i)) y) : ℂ) * Complex.I) ∂markLaw p) =
      Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic (covarianceMatrix p) (fun i => t (a, i))) : ℂ) := by
    convert markLaw_characteristic p hp (fun i => t (a, i)) using 1
    congr 1
    push_cast
    dsimp [finiteCovarianceQuadratic, covarianceQuadratic]
  simp_rw [ha]
  rw [← Complex.exp_sum, finiteMarkCovariance_quadratic]
  congr 1
  push_cast
  rw [Finset.mul_sum]

end GeneralizedBulk.Gaussian
