import GeneralizedBulk.MatrixGeometry

/-!
# The explicit endpoint rotation

The trigonometric rotation is constructed explicitly. Its group law,
orthogonality, derivative and covariance-preserving conjugate are proved
rather than postulated as flow identities.
-/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Exterior

abbrev Mat := Matrix (Fin 4) (Fin 4) ℂ

instance : MeasurableSpace Mat := borel Mat
instance : BorelSpace Mat := ⟨rfl⟩
instance : SecondCountableTopology Mat :=
  inferInstanceAs (SecondCountableTopology (Fin 4 → Fin 4 → ℂ))

/-- The complex-analytic rotation whose real restriction generates the flow. -/
def rotation (z : ℂ) : Mat :=
  !![Complex.cos z, -Complex.sin z, 0, 0;
     Complex.sin z, Complex.cos z, 0, 0;
     0, 0, Complex.cos z, Complex.sin z;
     0, 0, -Complex.sin z, Complex.cos z]

private theorem identity_eq : (1 : Mat) =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem rotation_zero : rotation 0 = 1 := by
  rw [identity_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation]

theorem rotation_transpose (z : ℂ) : (rotation z).transpose = rotation (-z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation]

set_option maxHeartbeats 1000000 in
theorem rotation_add (z u : ℂ) : rotation (z + u) = rotation z * rotation u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_succ, Complex.cos_add, Complex.sin_add] <;> ring

@[simp] theorem rotation_mul_transpose (z : ℂ) : rotation z * (rotation z).transpose = 1 := by
  rw [rotation_transpose, ← rotation_add]
  simp

@[simp] theorem rotation_transpose_mul (z : ℂ) : (rotation z).transpose * rotation z = 1 := by
  rw [rotation_transpose, ← rotation_add]
  simp

/-- The derivative is the infinitesimal generator multiplied on the left. -/
theorem hasDerivAt_rotation (z : ℂ) :
    HasDerivAt rotation (rotationGenerator * rotation z) z := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [rotation, rotationGenerator, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals first
    | simpa using Complex.hasDerivAt_cos z
    | simpa using Complex.hasDerivAt_sin z
    | simpa using (Complex.hasDerivAt_sin z).neg
    | simpa using hasDerivAt_const z (0 : ℂ)

/-- Continuity is proved entrywise, with no matrix-norm convention. -/
theorem continuous_rotation : Continuous rotation := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_iff_continuousAt.mpr
  intro z
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp (hasDerivAt_rotation z) i)) j).continuousAt

/-- The matrix rotation has real entries at real angles. -/
theorem rotation_conjTranspose (t : ℝ) : (rotation t).conjTranspose = (rotation t).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.conjTranspose_apply, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- Real-angle orthogonality is also unitarity over the complex endpoint space. -/
theorem rotation_conjTranspose_mul (t : ℝ) : (rotation t).conjTranspose * rotation t = 1 := by
  rw [rotation_conjTranspose, rotation_transpose_mul]

/-- The covariance-preserving rotation before conjugation by the switch. -/
def ordinaryRotation (z : ℂ) : Mat :=
  GeneralizedSwitching.endpointPermutation * rotation z * GeneralizedSwitching.endpointPermutation

set_option maxHeartbeats 1000000 in
theorem ordinaryRotation_commutes_edge (z : ℂ) :
    ordinaryRotation z * GeneralizedSwitching.edgeMatrix =
      GeneralizedSwitching.edgeMatrix * ordinaryRotation z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ordinaryRotation, rotation, GeneralizedSwitching.edgeMatrix,
      GeneralizedSwitching.endpointPermutation, Matrix.mul_apply, Fin.sum_univ_succ]

theorem ordinaryRotation_mul_transpose (z : ℂ) :
    ordinaryRotation z * (ordinaryRotation z).transpose = 1 := by
  simp only [ordinaryRotation, Matrix.transpose_mul, endpointPermutation_transpose]
  calc
    _ = GeneralizedSwitching.endpointPermutation *
      (rotation z * (GeneralizedSwitching.endpointPermutation *
        GeneralizedSwitching.endpointPermutation) * (rotation z).transpose) *
      GeneralizedSwitching.endpointPermutation := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [endpointPermutation_sq, mul_one, rotation_mul_transpose, mul_one, endpointPermutation_sq]

/-- The ordinary rotation preserves the endpoint Gaussian covariance. -/
theorem ordinaryRotation_preserves_covariance (z p : ℂ) :
    ordinaryRotation z * covarianceMatrix p * (ordinaryRotation z).transpose = covarianceMatrix p := by
  simp only [covarianceMatrix, Matrix.mul_add, Matrix.add_mul, mul_one, Matrix.mul_smul,
    Matrix.smul_mul, ordinaryRotation_mul_transpose]
  rw [ordinaryRotation_commutes_edge]
  simp only [Matrix.mul_assoc, ordinaryRotation_mul_transpose, mul_one]

end GeneralizedBulk.Exterior
