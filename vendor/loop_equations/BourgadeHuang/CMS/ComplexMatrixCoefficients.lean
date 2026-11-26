import BourgadeHuang.CMS.FreeDiagonalVolterra

/-! Actual complex matrix coefficient operators and finite triangular
elimination for the radial Volterra equation. -/
noncomputable section
open scoped Topology BoundedContinuousFunction BigOperators
open Filter
namespace BourgadeHuang.CMS
variable {X J K : Type*} [TopologicalSpace X] [Fintype J] [Fintype K]
  [DecidableEq J]

/-- A single matrix entry as a rank-one complex operator. -/
def complexMatrixUnit (i : J) (j : K) : (K → ℂ) →L[ℂ] (J → ℂ) :=
  (ContinuousLinearMap.single ℂ (fun _ : J => ℂ) i).comp (ContinuousLinearMap.proj j)

/-- Assembly of bounded scalar entries into an actual bounded operator field. -/
def complexBoundedMatrix (A : J → K → (X →ᵇ ℂ)) :
    X →ᵇ ((K → ℂ) →L[ℂ] (J → ℂ)) :=
  ∑i,∑j,((ContinuousLinearMap.id ℂ ℂ).smulRight (complexMatrixUnit i j)).compLeftContinuousBounded X (A i j)

@[simp] theorem complexBoundedMatrix_apply (A : J → K → (X →ᵇ ℂ))
    (x : X) (v : K → ℂ) (i : J) : complexBoundedMatrix A x v i=∑j,A i j x*v j := by
  simp [complexBoundedMatrix,complexMatrixUnit,ContinuousLinearMap.sum_apply,
    Finset.sum_apply,Pi.single_apply,Finset.sum_ite_irrel]

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
theorem analyticAt_complexBoundedMatrix
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {A : J → K → P → (X →ᵇ ℂ)} {p : P} (hA : ∀i j,AnalyticAt ℂ (A i j) p) :
    AnalyticAt ℂ (fun q => complexBoundedMatrix (fun i j => A i j q)) p := by
  unfold complexBoundedMatrix
  apply Finset.univ.analyticAt_sum
  intro i hi
  apply Finset.univ.analyticAt_sum
  intro j hj
  let L : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ((K → ℂ) →L[ℂ] (J → ℂ))) :=
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (complexMatrixUnit i j)).compLeftContinuousBounded X
  have hL : AnalyticAt ℂ (fun f => L f) (A i j p) := ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := X →ᵇ ℂ) (F := X →ᵇ ((K → ℂ) →L[ℂ] (J → ℂ))) L (A i j p)
  exact hL.comp (f := A i j) (hA i j)

theorem norm_complexBoundedMatrix_le (A : J → K → (X →ᵇ ℂ)) {B : ℝ}
    (hB : 0≤B) (hA : ∀i j,‖A i j‖≤B) :
    ‖complexBoundedMatrix A‖≤(Fintype.card K:ℝ)*B := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (Nat.cast_nonneg _) hB)).mpr
  intro x
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hB)
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [complexBoundedMatrix_apply]
  calc
    _≤∑j,‖A i j x*v j‖ := norm_sum_le _ _
    _≤∑_j : K,B*‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul ((A i j).norm_coe_le_norm x |>.trans (hA i j))
        (norm_le_pi_norm v j) (norm_nonneg _) hB
    _=(Fintype.card K:ℝ)*B*‖v‖ := by simp [mul_assoc]

/-- A strictly degree-lowering matrix raises the component vanishing filtration. -/
theorem raisesDegree_complexBoundedMatrix {degree : J → ℕ}
    (A : J → J → (X →ᵇ ℂ))
    (hA : ∀i j,¬degree j<degree i → ∀x,A i j x=0) :
    RaisesDegree degree (complexBoundedCoefficientOperator (complexBoundedMatrix A)) := by
  intro k f hf x i hi
  rw [complexBoundedCoefficientOperator_apply,complexBoundedMatrix_apply]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hji : degree j<degree i
  · rw [hf x j (by omega),mul_zero]
  · rw [hA i j hji x,zero_mul]

/-- The actual free-diagonal convolution followed by a triangular coefficient
is nilpotent, despite being an integral operator on an infinite half-line. -/
theorem freeForcing_matrix_pow_eq_zero {R a : ℝ} (hR : 0<R) (ha : 0<a)
    (lam : J → ℂ) (hlam : ∀i,a≤(lam i).re) (degree : J → ℕ)
    (A : J → J → (Tail R →ᵇ ℂ))
    (hA : ∀i j,¬degree j<degree i → ∀t,A i j t=0)
    {H : ℕ} (hH : ∀i,degree i<H) :
    (freeForcingOperator hR ha lam hlam*
      complexBoundedCoefficientOperator (complexBoundedMatrix A))^H=0 := by
  apply pow_eq_zero_of_raisesDegree (degree:=degree) _ hH
  intro k f hf
  exact freeForcingOperator_vanishesBelow hR ha lam hlam
    (raisesDegree_complexBoundedMatrix A hA k f hf)

end BourgadeHuang.CMS
