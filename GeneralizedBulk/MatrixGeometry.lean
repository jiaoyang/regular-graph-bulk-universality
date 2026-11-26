import GeneralizedBulk.Algebra

/-!
# Four-endpoint geometry for the marked switching criterion

All statements in this file are finite matrix identities over a commutative
ring.  No probabilistic stationarity, Gaussian integration, or limiting result
is assumed or asserted here.
-/

namespace GeneralizedBulk

open GeneralizedSwitching
open scoped BigOperators

section Matrices

variable {R : Type*} [CommRing R]

/-- The skew generator producing the stationary response after conjugating
an ordinary covariance-preserving rotation by the endpoint switch. -/
def rotationGenerator : Matrix (Fin 4) (Fin 4) R :=
  !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

/-- The diagonal matrix defining the centered observable `trace (D M)`. -/
def signMatrix : Matrix (Fin 4) (Fin 4) R :=
  !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- The endpoint covariance for the two independent sampled edges. -/
def covarianceMatrix (p : R) : Matrix (Fin 4) (Fin 4) R :=
  1 + p • edgeMatrix

private theorem identityMatrix_eq : (1 : Matrix (Fin 4) (Fin 4) R) =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem edgeMatrix_sq : (edgeMatrix : Matrix (Fin 4) (Fin 4) R) * edgeMatrix = 1 := by
  rw [identityMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [edgeMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem endpointPermutation_sq :
    (endpointPermutation : Matrix (Fin 4) (Fin 4) R) * endpointPermutation = 1 := by
  rw [identityMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [endpointPermutation, Matrix.mul_apply, Fin.sum_univ_succ]

theorem endpointPermutation_transpose :
    (endpointPermutation : Matrix (Fin 4) (Fin 4) R).transpose = endpointPermutation := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem rotationGenerator_transpose :
    (rotationGenerator : Matrix (Fin 4) (Fin 4) R).transpose = -rotationGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rotationGenerator]

theorem signMatrix_sq : (signMatrix : Matrix (Fin 4) (Fin 4) R) * signMatrix = 1 := by
  rw [identityMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [signMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem sign_edge_anticommute :
    (signMatrix : Matrix (Fin 4) (Fin 4) R) * edgeMatrix = -(edgeMatrix * signMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [signMatrix, edgeMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem rotation_edge_commutator :
    (rotationGenerator : Matrix (Fin 4) (Fin 4) R) * edgeMatrix -
        edgeMatrix * rotationGenerator = (2 : R) • signMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotationGenerator, edgeMatrix, signMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem sign_rotation_commutator :
    (signMatrix : Matrix (Fin 4) (Fin 4) R) * rotationGenerator -
        rotationGenerator * signMatrix = (2 : R) • edgeMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotationGenerator, edgeMatrix, signMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- Before switching conjugation, this generator commutes with the edge
matrix and hence preserves every covariance `I + p J`. -/
theorem conjugated_generator_commutes_edge :
    ((endpointPermutation : Matrix (Fin 4) (Fin 4) R) * rotationGenerator *
        endpointPermutation) * edgeMatrix =
      edgeMatrix * (endpointPermutation * rotationGenerator * endpointPermutation) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotationGenerator, edgeMatrix, endpointPermutation,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem covarianceMatrix_eq (p : R) : covarianceMatrix p =
    !![1, p, 0, 0; p, 1, 0, 0; 0, 0, 1, p; 0, 0, p, 1] := by
  rw [covarianceMatrix, identityMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [edgeMatrix]

theorem trace_sign_covariance (p : R) :
    Matrix.trace (signMatrix * covarianceMatrix p) = 0 := by
  rw [covarianceMatrix_eq]
  norm_num [Matrix.trace, signMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
/-- The Wick contraction coefficient is a scalar matrix. -/
theorem sign_covariance_product (p : R) :
    signMatrix * covarianceMatrix p * signMatrix * covarianceMatrix p =
      (1 - p ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) := by
  rw [covarianceMatrix_eq, identityMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [signMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem trace_sign_covariance_product (p : R) :
    Matrix.trace (signMatrix * covarianceMatrix p * signMatrix * covarianceMatrix p) =
      4 * (1 - p ^ 2) := by
  rw [sign_covariance_product, Matrix.trace_smul]
  simp [Matrix.trace_one, smul_eq_mul, mul_comm]

/-- The deterministic coefficient in the covariance of two sign-trace
observables when the entries satisfy the bilinear Wick identity. -/
theorem diagonal_wick_coefficient (p : R) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      (signMatrix : Matrix (Fin 4) (Fin 4) R) i i * signMatrix j j *
        (covarianceMatrix p i j * covarianceMatrix p i j +
          covarianceMatrix p i j * covarianceMatrix p i j)) = 8 * (1 - p ^ 2) := by
  rw [covarianceMatrix_eq]
  norm_num [signMatrix, Fin.sum_univ_succ]
  ring

/-- The deterministic Wick coefficient in the trace of `D X D X`. -/
theorem quadratic_trace_wick_coefficient (p : R) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      (signMatrix : Matrix (Fin 4) (Fin 4) R) i i * signMatrix j j *
        (covarianceMatrix p i j * covarianceMatrix p j i +
          covarianceMatrix p i i * covarianceMatrix p j j)) = 4 * (1 - p ^ 2) := by
  rw [covarianceMatrix_eq]
  norm_num [signMatrix, Fin.sum_univ_succ]
  ring

theorem trace_sign_apply (M : Matrix (Fin 4) (Fin 4) R) :
    Matrix.trace (signMatrix * M) = -M 0 0 + M 1 1 + M 2 2 - M 3 3 := by
  simp [Matrix.trace, signMatrix, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_succ]
  ring

theorem trace_sign_mean (g b : R) :
    Matrix.trace (signMatrix * meanMatrix g b 0) = 0 := by
  norm_num [Matrix.trace, signMatrix, meanMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem meanMatrix_from_covariance (p g r : R) :
    g • covarianceMatrix p + r • edgeMatrix = meanMatrix g (p * g + r) 0 := by
  rw [covarianceMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [edgeMatrix, meanMatrix] <;> ring

theorem sign_mean_conjugation (g b : R) :
    signMatrix * meanMatrix g b 0 * signMatrix = meanMatrix g (-b) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [signMatrix, meanMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem trace_edge_mean (g b : R) :
    Matrix.trace (edgeMatrix * meanMatrix g b 0) = 4 * b := by
  norm_num [Matrix.trace, edgeMatrix, meanMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 2000000 in
theorem trace_sign_mean_product (g b : R) :
    Matrix.trace (signMatrix * meanMatrix g b 0 * signMatrix * meanMatrix g b 0) =
      4 * (g ^ 2 - b ^ 2) := by
  norm_num [Matrix.trace, signMatrix, meanMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- The polynomial matrix response used by the stationary-flow calculation. -/
def matrixResponse (M : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 4) (Fin 4) R :=
  rotationGenerator * M - M * rotationGenerator + (2 : R) • (M * signMatrix * M)

set_option maxHeartbeats 2000000 in
/-- Taking the sign trace of the matrix response gives the drift observable.
This finite identity is independent of any existence/stationarity of a flow. -/
theorem trace_matrixResponse (M : Matrix (Fin 4) (Fin 4) R) :
    Matrix.trace (signMatrix * matrixResponse M) =
      2 * Matrix.trace (edgeMatrix * M) +
        2 * Matrix.trace (signMatrix * M * signMatrix * M) := by
  have hcycle : Matrix.trace (signMatrix * (M * rotationGenerator)) =
      Matrix.trace ((rotationGenerator * signMatrix) * M) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  calc
    _ = Matrix.trace ((signMatrix * rotationGenerator - rotationGenerator * signMatrix) * M) +
        2 * Matrix.trace (signMatrix * M * signMatrix * M) := by
      simp only [matrixResponse, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
        Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
        Matrix.sub_mul]
      rw [← Matrix.mul_assoc signMatrix rotationGenerator M, hcycle]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [sign_rotation_commutator, Matrix.smul_mul, Matrix.trace_smul]
      simp only [smul_eq_mul]

theorem mean_drift (g b : R) :
    Matrix.trace (signMatrix * matrixResponse (meanMatrix g b 0)) =
      8 * (g ^ 2 - b ^ 2 + b) := by
  rw [trace_matrixResponse, trace_edge_mean, trace_sign_mean_product]
  ring

end Matrices

end GeneralizedBulk
