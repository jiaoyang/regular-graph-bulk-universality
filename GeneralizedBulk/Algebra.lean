import Mathlib

/-!
Finite algebra for an ensemble-free version of the four-endpoint argument.

This file proves only the algebraic seed. It does not claim a Lean proof of
point-process convergence or of the conditional Gaussian marked-limit criterion.
The calibration hypotheses are ordinary equations, not opaque model assumptions.
-/

namespace GeneralizedSwitching

section Scalar

variable {R : Type*} [CommRing R]

/-- Calibration centers the switching polynomial at the roots `±i`.
The identity is valid over any commutative ring, including `ℂ`. -/
theorem calibrated_scalar_polynomial
    (p r a sigma v : R)
    (hcenter : 2 * (1 - p ^ 2) * a + p * (1 - 2 * r) = 0)
    (hscale : (1 - p ^ 2) * (a ^ 2 + sigma ^ 2) = r * (1 - r)) :
    (a + sigma * v) ^ 2 - (p * (a + sigma * v) + r) ^ 2 +
        (p * (a + sigma * v) + r) =
      sigma ^ 2 * (1 - p ^ 2) * (v ^ 2 + 1) := by
  linear_combination (a + sigma * v) * hcenter - hscale

end Scalar

/-- The normalization factor used to divide the stationary identity is positive. -/
theorem contraction_coefficient_pos (p sigma : ℝ)
    (hsigma : 0 < sigma) (hp : |p| < 1) :
    0 < 8 * sigma ^ 2 * (1 - p ^ 2) := by
  have hp2 : p ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one p).2 hp
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hsigma)) (sub_pos.mpr hp2)

section Matrices

variable {R : Type*} [CommRing R]

def edgeMatrix : Matrix (Fin 4) (Fin 4) R :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

def endpointPermutation : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0]

def switchIncrement : Matrix (Fin 4) (Fin 4) R :=
  endpointPermutation * edgeMatrix * endpointPermutation - edgeMatrix

theorem switchIncrement_eq : (switchIncrement : Matrix (Fin 4) (Fin 4) R) =
    !![0, -1, 0, 1; -1, 0, 1, 0; 0, 1, 0, -1; 1, 0, -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [switchIncrement, endpointPermutation, edgeMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]

def meanMatrix (g b q : R) : Matrix (Fin 4) (Fin 4) R :=
  !![g + q, b + q, q, q;
     b + q, g + q, q, q;
     q, q, g + q, b + q;
     q, q, b + q, g + q]

set_option maxHeartbeats 2000000 in
/-- The shared matrix polynomial, including the rank-one background `q 11ᵀ`. -/
theorem common_switching_polynomial (g b q : R) :
    (1 + meanMatrix g b q * switchIncrement) * endpointPermutation *
        meanMatrix g b q * endpointPermutation - meanMatrix g b q =
      (g ^ 2 - b ^ 2 + b) • (switchIncrement : Matrix (Fin 4) (Fin 4) R) := by
  have hid : (1 : Matrix (Fin 4) (Fin 4) R) =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [switchIncrement_eq, hid]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [meanMatrix, endpointPermutation,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end Matrices

end GeneralizedSwitching
