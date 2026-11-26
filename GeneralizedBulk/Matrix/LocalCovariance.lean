import GeneralizedBulk.Matrix.CovarianceBounds

/-! Entrywise local laws give actual relative quadratic and log-determinant
bounds in finite dimension. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.Covariance
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A finite matrix entry error controls its quadratic form, with the exact
cardinality loss. Symmetry is not needed for this elementary estimate. -/
theorem abs_quadratic_le_of_entrywise (A : Matrix I I ℝ) (e : ℝ) (he : 0 ≤ e)
    (hA : ∀ i j, |A i j| ≤ e) (x : I → ℝ) :
    |dotProduct x (A *ᵥ x)| ≤ (Fintype.card I : ℝ) * e * (∑ i, x i ^ 2) := by
  have hCS : (∑ i, |x i|) ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, x i ^ 2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |x i|) (fun _ : I => (1 : ℝ))
    simpa only [mul_one, sq_abs, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, mul_comm] using hh
  calc
    |dotProduct x (A *ᵥ x)| = |∑ i, ∑ j, x i * A i j * x j| := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ i, ∑ j, |x i * A i j * x j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i, ∑ j, |x i| * e * |x j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA i j) (abs_nonneg _)) (abs_nonneg _)
    _ = e * (∑ i, |x i|) ^ 2 := by
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ e * ((Fintype.card I : ℝ) * ∑ i, x i ^ 2) := mul_le_mul_of_nonneg_left hCS he
    _ = _ := by ring

theorem quadratic_identity_closeness (A : Matrix I I ℝ) (e : ℝ) (he : 0 ≤ e)
    (hA : ∀ i j, |(A - 1) i j| ≤ e) (x : I → ℝ) :
    (1 - Fintype.card I * e) * (∑ i, x i ^ 2) ≤ dotProduct x (A *ᵥ x) ∧
    dotProduct x (A *ᵥ x) ≤ (1 + Fintype.card I * e) * (∑ i, x i ^ 2) := by
  have hh := abs_quadratic_le_of_entrywise (A - 1) e he hA x
  have hid : dotProduct x ((A - 1) *ᵥ x) = dotProduct x (A *ᵥ x) - ∑ i, x i ^ 2 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
    simp only [dotProduct, pow_two]
  rw [hid] at hh
  constructor <;> nlinarith [(abs_le.mp hh).1, (abs_le.mp hh).2]

theorem logdet_stability_of_entrywise (A : Matrix I I ℝ) (hA : A.PosDef)
    (e : ℝ) (he : 0 ≤ e) (he' : (Fintype.card I : ℝ) * e ≤ 1 / 2)
    (hclose : ∀ i j, |(A - 1) i j| ≤ e) :
    |Real.log A.det| ≤ 2 * (Fintype.card I : ℝ) ^ 2 * e := by
  have hh := logdet_stability_of_quadratic A hA ((Fintype.card I : ℝ) * e) (by positivity) he'
    (quadratic_identity_closeness A e he hclose)
  convert hh using 1 <;> ring

end GeneralizedBulk.Covariance
