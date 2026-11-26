import BourgadeHuang.CMS.ComplexMatrixCoefficients

/-! Uniform estimates and strict filtration for actual bounded matrix fields. -/
noncomputable section
open scoped Topology BoundedContinuousFunction BigOperators
namespace BourgadeHuang.CMS
variable {X J K : Type*} [TopologicalSpace X] [Fintype J] [Fintype K]

/-- A pointwise matrix formula gives the actual supremum operator norm bound. -/
theorem norm_boundedMatrixField_le
    (A : X →ᵇ ((K → ℂ) →L[ℂ] (J → ℂ))) (a : X → J → K → ℂ)
    (hA : ∀x v i,A x v i=∑j,a x i j*v j) {B : ℝ} (hB : 0≤B)
    (ha : ∀x i j,‖a x i j‖≤B) : ‖A‖≤(Fintype.card K:ℝ)*B := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (Nat.cast_nonneg _) hB)).mpr
  intro x
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hB)
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [hA]
  calc
    _≤∑j,‖a x i j*v j‖ := norm_sum_le _ _
    _≤∑_j : K,B*‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (ha x i j) (norm_le_pi_norm v j) (norm_nonneg _) hB
    _=(Fintype.card K:ℝ)*B*‖v‖ := by simp [mul_assoc]

/-- Strict lowering in the actual matrix entries raises the vanishing
filtration on bounded continuous functions. -/
theorem raisesDegree_boundedMatrixField (degree : J → ℕ)
    (A : X →ᵇ ((J → ℂ) →L[ℂ] (J → ℂ))) (a : X → J → J → ℂ)
    (hA : ∀x v i,A x v i=∑j,a x i j*v j)
    (ha : ∀x i j,¬degree j<degree i → a x i j=0) :
    RaisesDegree degree (complexBoundedCoefficientOperator A) := by
  intro k f hf x i hi
  rw [complexBoundedCoefficientOperator_apply,hA]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hji : degree j<degree i
  · rw [hf x j (by omega),mul_zero]
  · rw [ha x i j hji,zero_mul]

end BourgadeHuang.CMS
