import GeneralizedBulk.Exterior.Flow
import GeneralizedBulk.Exterior.Reconstruction

/-!
# Exterior coordinates constructed from raw resolvent jets

The coordinate transformation is explicit, its reconstruction identities are
proved, and positive imaginary part transfers through inversion. Thus the
flow can be started from the marked endpoint field without adding a new
positivity or reconstruction assumption.
-/
noncomputable section
open scoped ComplexOrder
namespace GeneralizedBulk.Exterior

/-- Exterior self-energy, with the harmless real energy shift omitted. -/
def rawExterior (M : Mat) : Mat := GeneralizedSwitching.edgeMatrix - M⁻¹

def rawExteriorDerivative (M L : Mat) : Mat := M⁻¹ * L * M⁻¹

def rawExteriorScalar (s : ℂ) (M L : Mat) : ℂ := s - Matrix.trace (M⁻¹ * L)

/-- Strict imaginary positivity implies invertibility of the raw field. -/
theorem isUnit_of_imaginary_posDef (M : Mat) (hM : (imaginaryPart M).PosDef) : IsUnit M := by
  have h0 : (0 : Mat).IsHermitian := by simp [Matrix.IsHermitian]
  have h := isUnit_hermitian_sub_of_imaginary_posDef 0 M h0 hM
  have hn : IsUnit (-M) := by simpa only [zero_sub] using h
  simpa only [neg_neg] using hn.neg

/-- The imaginary part of the exterior inverse has the usual positive
congruence formula. -/
theorem imaginaryPart_hermitian_sub_inverse (H M : Mat)
    (hH : H.IsHermitian) (hM : IsUnit M) :
    imaginaryPart (H - M⁻¹) = M⁻¹.conjTranspose * imaginaryPart M * M⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hM
  have hR : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hd
  have hL : M⁻¹.conjTranspose * M.conjTranspose = 1 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using
      congrArg Matrix.conjTranspose hR
  have hcalc : M⁻¹.conjTranspose * (M - M.conjTranspose) * M⁻¹ =
      M⁻¹.conjTranspose - M⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    have hr : M⁻¹.conjTranspose * M * M⁻¹ = M⁻¹.conjTranspose := by
      rw [Matrix.mul_assoc, hR, mul_one]
    rw [hr, hL, one_mul]
  rw [imaginaryPart, Matrix.conjTranspose_sub, hH.eq]
  have hdiff : H - M⁻¹ - (H - M⁻¹.conjTranspose) = M⁻¹.conjTranspose - M⁻¹ := by abel
  rw [hdiff]
  simp only [imaginaryPart, Matrix.mul_smul, Matrix.smul_mul]
  rw [hcalc]

/-- Positive imaginary part is retained in exterior coordinates. -/
theorem rawExterior_imaginary_posDef (M : Mat) (hM : (imaginaryPart M).PosDef) :
    (imaginaryPart (rawExterior M)).PosDef := by
  have hu := isUnit_of_imaginary_posDef M hM
  have hJ : (GeneralizedSwitching.edgeMatrix : Mat).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [GeneralizedSwitching.edgeMatrix, Matrix.conjTranspose_apply]
  rw [rawExterior, imaginaryPart_hermitian_sub_inverse _ _ hJ hu]
  apply hM.conjTranspose_mul_mul_same
  exact Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_nonsing_inv_iff.mpr hu)

@[simp] theorem reconstruct_raw_matrix (M : Mat) (hM : IsUnit M) :
    ((GeneralizedSwitching.edgeMatrix : Mat) - rawExterior M)⁻¹ = M := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hM
  simp only [rawExterior, sub_sub_cancel]
  exact Matrix.nonsing_inv_nonsing_inv M hd

@[simp] theorem reconstruct_raw_derivative (M L : Mat) (hM : IsUnit M) :
    M * rawExteriorDerivative M L * M = L := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hM
  simp only [rawExteriorDerivative, ← Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv M hd, one_mul]
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul M hd, mul_one]

@[simp] theorem reconstruct_raw_scalar (s : ℂ) (M L : Mat) (hM : IsUnit M) :
    rawExteriorScalar s M L + Matrix.trace (M * rawExteriorDerivative M L) = s := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hM
  have ht : Matrix.trace (M * rawExteriorDerivative M L) = Matrix.trace (M⁻¹ * L) := by
    simp only [rawExteriorDerivative, ← Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv M hd, one_mul, Matrix.trace_mul_comm L M⁻¹]
  rw [ht, rawExteriorScalar]
  ring

/-- Spectral differentiation of the raw inverse gives the exterior derivative
used in the reconstructed scalar path. -/
theorem hasDerivAt_rawExterior {f : ℂ → Mat} {f' : Mat} {w : ℂ}
    (hf : HasDerivAt f f' w) (hu : IsUnit (f w)) :
    HasDerivAt (fun z => rawExterior (f z)) (rawExteriorDerivative (f w) f') w := by
  have h := hasDerivAt_matrix_sub (hasDerivAt_matrix_const
    (GeneralizedSwitching.edgeMatrix : Mat) w) (hasDerivAt_matrix_inverse hf hu)
  simpa only [rawExterior, rawExteriorDerivative, zero_sub, neg_neg] using h

/-- Either imaginary sign makes the raw matrix invertible. -/
theorem isUnit_of_imaginary_signDefinite (M : Mat)
    (hM : ImaginarySignDefinite M) : IsUnit M := by
  have h0 : (0 : Mat).IsHermitian := by simp [Matrix.IsHermitian]
  have h := isUnit_hermitian_sub_of_imaginary_signDefinite 0 M h0 hM
  have hn : IsUnit (-M) := by simpa only [zero_sub] using h
  simpa only [neg_neg] using hn.neg

/-- Both half-plane signs are preserved by the raw exterior transform. -/
theorem rawExterior_imaginary_signDefinite (M : Mat)
    (hM : ImaginarySignDefinite M) : ImaginarySignDefinite (rawExterior M) := by
  rcases hM with hp | hn
  · exact Or.inl (rawExterior_imaginary_posDef M hp)
  · apply Or.inr
    have hu := isUnit_of_imaginary_signDefinite M (Or.inr hn)
    have hJ : (GeneralizedSwitching.edgeMatrix : Mat).IsHermitian := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [GeneralizedSwitching.edgeMatrix, Matrix.conjTranspose_apply]
    rw [rawExterior, imaginaryPart_hermitian_sub_inverse _ _ hJ hu]
    have hpos := hn.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_nonsing_inv_iff.mpr hu))
    simpa only [Matrix.mul_neg, Matrix.neg_mul] using hpos

end GeneralizedBulk.Exterior
