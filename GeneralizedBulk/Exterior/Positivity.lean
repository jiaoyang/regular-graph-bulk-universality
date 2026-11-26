import GeneralizedBulk.Exterior.Rotation

/-!
# Positivity makes the exterior resolvent globally well-defined

The imaginary part is Hermitian. Strict positivity rules out a nonzero kernel
for any Hermitian real-background shift, and is preserved by the real rotation.
-/
noncomputable section
open scoped BigOperators ComplexOrder
namespace GeneralizedBulk.Exterior

/-- The Hermitian imaginary part, matching `(A-A*)/(2i)`. -/
def imaginaryPart (A : Mat) : Mat := (-Complex.I / 2) • (A - A.conjTranspose)

private theorem quadratic_conjTranspose (A : Mat) (v : Fin 4 → ℂ) :
    dotProduct (star v) (A.conjTranspose.mulVec v) =
      star (dotProduct (star v) (A.mulVec v)) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose]
  simp only [star_star]
  exact Matrix.star_dotProduct (A.mulVec v) v

/-- A strictly positive imaginary part excludes singularity after any
Hermitian shift. In particular this applies to `J-K`. -/
theorem isUnit_hermitian_sub_of_imaginary_posDef
    (H K : Mat) (hH : H.IsHermitian) (hK : (imaginaryPart K).PosDef) :
    IsUnit (H - K) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hker : (H - K).mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hzero : x - y = 0 := by
    by_contra hv
    let v := x - y
    have hKv : K.mulVec v = H.mulVec v := by
      have h := hker
      rw [Matrix.sub_mulVec] at h
      exact (sub_eq_zero.mp h).symm
    have hqH : star (dotProduct (star v) (H.mulVec v)) =
        dotProduct (star v) (H.mulVec v) := by
      rw [← quadratic_conjTranspose H v, hH.eq]
    have hqK : dotProduct (star v) ((imaginaryPart K).mulVec v) = 0 := by
      rw [imaginaryPart, Matrix.smul_mulVec_assoc, dotProduct_smul, Matrix.sub_mulVec,
        dotProduct_sub, quadratic_conjTranspose, hKv, hqH, sub_self, smul_zero]
    have hp := hK.2 v hv
    rw [hqK] at hp
    exact (lt_irrefl _ hp)
  exact sub_eq_zero.mp hzero

/-- Conjugation transports the imaginary part without additional error terms. -/
theorem imaginaryPart_conjugate (Q K : Mat) :
    imaginaryPart (Q * K * Q.conjTranspose) = Q * imaginaryPart K * Q.conjTranspose := by
  simp only [imaginaryPart, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- Rotation in exterior coordinates. -/
def exteriorPath (K : Mat) (t : ℝ) : Mat :=
  rotation t * K * (rotation t).conjTranspose

theorem exteriorPath_eq_transpose (K : Mat) (t : ℝ) :
    exteriorPath K t = rotation t * K * (rotation t).transpose := by
  rw [exteriorPath, rotation_conjTranspose]

@[simp] theorem exteriorPath_zero (K : Mat) : exteriorPath K 0 = K := by
  simp [exteriorPath]

theorem exteriorPath_imaginary_posDef (K : Mat) (hK : (imaginaryPart K).PosDef) (t : ℝ) :
    (imaginaryPart (exteriorPath K t)).PosDef := by
  rw [exteriorPath, imaginaryPart_conjugate]
  apply hK.mul_mul_conjTranspose_same
  intro x y hxy
  have hunit : IsUnit (rotation (t : ℂ)) :=
    ⟨⟨rotation t, (rotation t).transpose, rotation_mul_transpose _, rotation_transpose_mul _⟩, rfl⟩
  exact Matrix.vecMul_injective_iff_isUnit.mpr hunit hxy

private theorem edge_isHermitian : (GeneralizedSwitching.edgeMatrix : Mat).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [GeneralizedSwitching.edgeMatrix, Matrix.conjTranspose_apply]

/-- The matrix inverse in the constructed flow exists at every real angle. -/
theorem exteriorPath_resolvent_isUnit (K : Mat) (hK : (imaginaryPart K).PosDef) (t : ℝ) :
    IsUnit ((GeneralizedSwitching.edgeMatrix : Mat) - exteriorPath K t) :=
  isUnit_hermitian_sub_of_imaginary_posDef _ _ edge_isHermitian
    (exteriorPath_imaginary_posDef K hK t)

/-- The actual resolvent reconstructed from the rotated exterior state. -/
def resolventPath (K : Mat) (t : ℝ) : Mat :=
  ((GeneralizedSwitching.edgeMatrix : Mat) - exteriorPath K t)⁻¹

/-- Either half-plane sign suffices for every inverse in the exterior flow.
The sign may vary between the spectral parameters of one polynomial. -/
def ImaginarySignDefinite (M : Mat) : Prop :=
  (imaginaryPart M).PosDef ∨ (-imaginaryPart M).PosDef

@[simp] theorem imaginaryPart_neg (M : Mat) : imaginaryPart (-M) = -imaginaryPart M := by
  simp only [imaginaryPart, Matrix.conjTranspose_neg]
  rw [show -M - -M.conjTranspose = -(M - M.conjTranspose) by abel, smul_neg]

theorem isUnit_hermitian_sub_of_imaginary_signDefinite
    (H K : Mat) (hH : H.IsHermitian) (hK : ImaginarySignDefinite K) :
    IsUnit (H - K) := by
  rcases hK with hp | hn
  · exact isUnit_hermitian_sub_of_imaginary_posDef H K hH hp
  · have hneg : (imaginaryPart (-K)).PosDef := by simpa using hn
    have hu := isUnit_hermitian_sub_of_imaginary_posDef (-H) (-K) hH.neg hneg
    simpa only [neg_sub_neg, neg_sub] using hu.neg

theorem exteriorPath_imaginary_signDefinite (K : Mat)
    (hK : ImaginarySignDefinite K) (t : ℝ) : ImaginarySignDefinite (exteriorPath K t) := by
  rcases hK with hp | hn
  · exact Or.inl (exteriorPath_imaginary_posDef K hp t)
  · apply Or.inr
    have hneg := exteriorPath_imaginary_posDef (-K) (by simpa using hn) t
    simpa only [exteriorPath, Matrix.mul_neg, Matrix.neg_mul, imaginaryPart_neg] using hneg

theorem exteriorPath_resolvent_isUnit_of_signDefinite (K : Mat)
    (hK : ImaginarySignDefinite K) (t : ℝ) :
    IsUnit ((GeneralizedSwitching.edgeMatrix : Mat) - exteriorPath K t) :=
  isUnit_hermitian_sub_of_imaginary_signDefinite _ _ edge_isHermitian
    (exteriorPath_imaginary_signDefinite K hK t)

end GeneralizedBulk.Exterior
