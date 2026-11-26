import Mathlib

/-!
# Finite Schur exterior coordinates and scalar trace cancellation

All inverses below are genuine at nonreal parameters of a Hermitian matrix.
The exterior trace identity is a finite block calculation, independent of BS
or HY and retaining the scalar channel together with the boundary matrix.
-/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace GeneralizedBulk.Graph

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Every finite Hermitian matrix has a genuine inverse off the real axis,
including every principal minor of the finite graph adjacency. -/
theorem hermitian_shift_isUnit (H : Matrix m m ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) : IsUnit (H - z • (1 : Matrix m m ℂ)) := by
  let U : Matrix m m ℂ := hH.eigenvectorUnitary
  let L : m → ℝ := hH.eigenvalues
  have hU : U * star U = 1 := unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hUt : star U * U = 1 := unitary.coe_star_mul_self hH.eigenvectorUnitary
  have he : H = U * Matrix.diagonal (fun a => (L a : ℂ)) * star U := hH.spectral_theorem
  have hdiag : Matrix.diagonal (fun a => (L a : ℂ) - z) =
      Matrix.diagonal (fun a => (L a : ℂ)) - z • (1 : Matrix m m ℂ) := by
    ext a b
    by_cases hab : a = b
    · subst b; simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hab]
  have hs : H - z • (1 : Matrix m m ℂ) =
      U * Matrix.diagonal (fun a => (L a : ℂ) - z) * star U := by
    rw [hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, mul_one, hU, ← he]
  have hp (a : m) : (L a : ℂ) - z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub, neg_eq_zero] at hi
    exact hz hi
  let R := U * Matrix.diagonal (fun a => ((L a : ℂ) - z)⁻¹) * star U
  have hright : (H - z • (1 : Matrix m m ℂ)) * R = 1 := by
    rw [hs]
    calc
      _ = U * (Matrix.diagonal (fun a => (L a : ℂ) - z) * (star U * U) *
          Matrix.diagonal (fun a => ((L a : ℂ) - z)⁻¹)) * star U := by
        simp only [R, Matrix.mul_assoc]
      _ = 1 := by
        rw [hUt, mul_one, Matrix.diagonal_mul_diagonal]
        simp only [mul_inv_cancel₀ (hp _), Matrix.diagonal_one, mul_one, hU]
  exact ⟨⟨H - z • (1 : Matrix m m ℂ), R, hright, Matrix.mul_eq_one_comm.mpr hright⟩, rfl⟩

/-- The Schur complement of the exterior minor. -/
def schurComplement (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ) : Matrix m m ℂ := A - B * D⁻¹ * C

/-- The inverse boundary block of a genuinely invertible block matrix. -/
theorem inverse_fromBlocks (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hD : IsUnit D) (hS : IsUnit (schurComplement A B C D)) :
    (Matrix.fromBlocks A B C D)⁻¹ =
      Matrix.fromBlocks ((schurComplement A B C D)⁻¹)
        (-((schurComplement A B C D)⁻¹ * B * D⁻¹))
        (-(D⁻¹ * C * (schurComplement A B C D)⁻¹))
        (D⁻¹ + D⁻¹ * C * (schurComplement A B C D)⁻¹ * B * D⁻¹) := by
  cases hD.nonempty_invertible
  have hS' : IsUnit (A - B * ⅟ D * C) := by
    simpa only [Matrix.invOf_eq_nonsing_inv] using hS
  cases hS'.nonempty_invertible
  letI := Matrix.fromBlocks₂₂Invertible A B C D
  simpa only [Matrix.invOf_eq_nonsing_inv, schurComplement] using
    Matrix.invOf_fromBlocks₂₂_eq A B C D

/-- Invertibility of the full matrix and exterior minor makes the boundary
Schur complement a unit as well. -/
theorem schurComplement_isUnit (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hD : IsUnit D) (hFull : IsUnit (Matrix.fromBlocks A B C D)) :
    IsUnit (schurComplement A B C D) := by
  cases hD.nonempty_invertible
  have h := (Matrix.isUnit_fromBlocks_iff_of_invertible₂₂).mp hFull
  simpa only [Matrix.invOf_eq_nonsing_inv, schurComplement] using h

/-- Trace of a finite block matrix is the sum of the two diagonal traces. -/
theorem trace_fromBlocks (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- The boundary resolvent squared block, which is the spectral derivative
of that block, expressed entirely by the Schur inverse and exterior minor. -/
theorem inverse_square_boundary (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hD : IsUnit D) (hS : IsUnit (schurComplement A B C D)) :
    (((Matrix.fromBlocks A B C D)⁻¹ * (Matrix.fromBlocks A B C D)⁻¹).submatrix
      Sum.inl Sum.inl) =
      (schurComplement A B C D)⁻¹ * (schurComplement A B C D)⁻¹ +
        (schurComplement A B C D)⁻¹ * B * D⁻¹ * D⁻¹ * C * (schurComplement A B C D)⁻¹ := by
  rw [inverse_fromBlocks A B C D hD hS, Matrix.fromBlocks_multiply]
  ext a b
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.submatrix_apply, Matrix.neg_mul,
    Matrix.mul_neg, neg_neg]
  congr 1
  simp only [Matrix.mul_assoc]

/-- The scalar exterior coordinate is exactly the trace of the exterior
minor. Thus it belongs to the same exterior object as the Schur self-energy. -/
theorem exterior_trace_identity (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hD : IsUnit D) (hS : IsUnit (schurComplement A B C D)) :
    Matrix.trace ((Matrix.fromBlocks A B C D)⁻¹) -
      Matrix.trace ((schurComplement A B C D) *
        (((Matrix.fromBlocks A B C D)⁻¹ * (Matrix.fromBlocks A B C D)⁻¹).submatrix
          Sum.inl Sum.inl)) = Matrix.trace D⁻¹ := by
  have hSinv : schurComplement A B C D * (schurComplement A B C D)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS)
  rw [inverse_square_boundary A B C D hD hS]
  have hproduct : schurComplement A B C D *
      ((schurComplement A B C D)⁻¹ * (schurComplement A B C D)⁻¹ +
        (schurComplement A B C D)⁻¹ * B * D⁻¹ * D⁻¹ * C * (schurComplement A B C D)⁻¹) =
      (schurComplement A B C D)⁻¹ + B * D⁻¹ * D⁻¹ * C * (schurComplement A B C D)⁻¹ := by
    simp only [Matrix.mul_add]
    have hcancel (R : Matrix m m ℂ) : schurComplement A B C D *
        ((schurComplement A B C D)⁻¹ * R) = R := by rw [← Matrix.mul_assoc, hSinv, one_mul]
    simpa only [Matrix.mul_assoc] using congrArg₂ (fun X Y => X + Y)
      (hcancel ((schurComplement A B C D)⁻¹))
      (hcancel (B * D⁻¹ * D⁻¹ * C * (schurComplement A B C D)⁻¹))
  rw [hproduct, inverse_fromBlocks A B C D hD hS, trace_fromBlocks,
    Matrix.trace_add, Matrix.trace_add]
  have hcycle : Matrix.trace (D⁻¹ * C * (schurComplement A B C D)⁻¹ * B * D⁻¹) =
      Matrix.trace (B * D⁻¹ * D⁻¹ * C * (schurComplement A B C D)⁻¹) := by
    have h := Matrix.trace_mul_comm (D⁻¹ * C * (schurComplement A B C D)⁻¹) (B * D⁻¹)
    simpa only [Matrix.mul_assoc] using h
  rw [hcycle]
  ring

/-- The literal upper-left block of the inverse is the inverse Schur
complement. -/
theorem inverse_boundary_eq_schurInverse (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hD : IsUnit D) (hS : IsUnit (schurComplement A B C D)) :
    ((Matrix.fromBlocks A B C D)⁻¹).submatrix Sum.inl Sum.inl =
      (schurComplement A B C D)⁻¹ := by
  rw [inverse_fromBlocks A B C D hD hS]
  rfl

/-- The inverse of the actual boundary block is the genuine Schur complement. -/
theorem inverse_boundary_inverse (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hD : IsUnit D) (hS : IsUnit (schurComplement A B C D)) :
    (((Matrix.fromBlocks A B C D)⁻¹).submatrix Sum.inl Sum.inl)⁻¹ =
      schurComplement A B C D := by
  rw [inverse_boundary_eq_schurInverse A B C D hD hS]
  exact Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS)

/-- Explicit exterior self-energy from the finite outside minor. -/
theorem exterior_selfEnergy_identity (J A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hD : IsUnit D) (hS : IsUnit (schurComplement A B C D)) :
    J - (((Matrix.fromBlocks A B C D)⁻¹).submatrix Sum.inl Sum.inl)⁻¹ =
      J - A + B * D⁻¹ * C := by
  rw [inverse_boundary_inverse A B C D hD hS, schurComplement]
  abel

/-- The trace identity expressed directly in the literal boundary resolvent
and its true squared-resolvent derivative block. -/
theorem exterior_trace_identity_boundary (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hD : IsUnit D) (hS : IsUnit (schurComplement A B C D)) :
    Matrix.trace ((Matrix.fromBlocks A B C D)⁻¹) -
      Matrix.trace ((((Matrix.fromBlocks A B C D)⁻¹).submatrix Sum.inl Sum.inl)⁻¹ *
        (((Matrix.fromBlocks A B C D)⁻¹ * (Matrix.fromBlocks A B C D)⁻¹).submatrix
          Sum.inl Sum.inl)) = Matrix.trace D⁻¹ := by
  rw [inverse_boundary_inverse A B C D hD hS]
  exact exterior_trace_identity A B C D hD hS

/-- A scalar spectral shift keeps the off-diagonal coupling blocks fixed. -/
theorem fromBlocks_shift (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ) (z : ℂ) :
    Matrix.fromBlocks (A - z • 1) B C (D - z • 1) =
      Matrix.fromBlocks A B C D - z • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) := by
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

/-- The Schur complement used at a nonreal parameter is automatically a unit
for a Hermitian finite matrix; it is not a separate analytic assumption. -/
theorem shifted_schurComplement_isUnit (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hH : (Matrix.fromBlocks A B C D).IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    IsUnit (schurComplement (A - z • 1) B C (D - z • 1)) := by
  have hD : D.IsHermitian := by
    have h := hH.submatrix Sum.inr
    simpa only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂] using h
  apply schurComplement_isUnit
  · exact hermitian_shift_isUnit D hD z hz
  · rw [fromBlocks_shift]
    exact hermitian_shift_isUnit _ hH z hz

/-- The finite scalar exterior trace formula now uses only a Hermitian
matrix and a nonreal parameter, with every inverse condition discharged. -/
theorem shifted_exterior_trace_identity (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hH : (Matrix.fromBlocks A B C D).IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    Matrix.trace ((Matrix.fromBlocks (A - z • 1) B C (D - z • 1))⁻¹) -
      Matrix.trace ((((Matrix.fromBlocks (A - z • 1) B C (D - z • 1))⁻¹).submatrix Sum.inl Sum.inl)⁻¹ *
        (((Matrix.fromBlocks (A - z • 1) B C (D - z • 1))⁻¹ *
          (Matrix.fromBlocks (A - z • 1) B C (D - z • 1))⁻¹).submatrix Sum.inl Sum.inl)) =
      Matrix.trace (D - z • 1)⁻¹ := by
  have hD : D.IsHermitian := by
    have h := hH.submatrix Sum.inr
    simpa only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂] using h
  exact exterior_trace_identity_boundary (A - z • 1) B C (D - z • 1)
    (hermitian_shift_isUnit D hD z hz) (shifted_schurComplement_isUnit A B C D hH z hz)

end GeneralizedBulk.Graph
