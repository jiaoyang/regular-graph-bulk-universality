import GeneralizedBulk.ExternalInputs

/-!
# Finite spectral expansion of the genuine adjacency resolvent

Orthonormal eigenvectors form an actual square orthogonal matrix. The stated
eigen-equations therefore diagonalize the real adjacency, and the nonreal
matrix inverse is exactly its finite spectral sum. None of these finite
linear algebra facts is delegated to the external BS or HY hypotheses.
-/
noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder
namespace GeneralizedBulk.External.RegularSpectralData

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def eigenvectorMatrix : Matrix (Fin (N n)) (Fin (N n)) ℂ :=
  fun v a => (D.eigenvector n ω a v : ℂ)

def eigenvalueMatrix : Matrix (Fin (N n)) (Fin (N n)) ℂ :=
  Matrix.diagonal (fun a => (D.eigenvalue n ω a : ℂ))

theorem eigenvectorMatrix_transpose_mul :
    (D.eigenvectorMatrix n ω).transpose * D.eigenvectorMatrix n ω = 1 := by
  classical
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, eigenvectorMatrix, Matrix.one_apply]
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, apply_ite,
    Complex.ofReal_one, Complex.ofReal_zero] using
    congrArg Complex.ofReal (D.orthonormal n ω a b)

theorem eigenvectorMatrix_mul_transpose :
    D.eigenvectorMatrix n ω * (D.eigenvectorMatrix n ω).transpose = 1 :=
  Matrix.mul_eq_one_comm.mpr (D.eigenvectorMatrix_transpose_mul n ω)

theorem eigenvectorMatrix_isUnit : IsUnit (D.eigenvectorMatrix n ω) :=
  ⟨⟨D.eigenvectorMatrix n ω, (D.eigenvectorMatrix n ω).transpose,
    D.eigenvectorMatrix_mul_transpose n ω, D.eigenvectorMatrix_transpose_mul n ω⟩, rfl⟩

@[simp] theorem eigenvectorMatrix_conjTranspose :
    (D.eigenvectorMatrix n ω).conjTranspose = (D.eigenvectorMatrix n ω).transpose := by
  ext a b
  simp [Matrix.conjTranspose_apply, eigenvectorMatrix]

theorem adjacency_mul_eigenvectorMatrix :
    (D.adjacency n ω).map Complex.ofReal * D.eigenvectorMatrix n ω =
      D.eigenvectorMatrix n ω * D.eigenvalueMatrix n ω := by
  classical
  ext v a
  simp only [eigenvalueMatrix, Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Matrix.map_apply, eigenvectorMatrix]
  have h := congrArg Complex.ofReal (D.eigen_equation n ω a v)
  simp only [Complex.ofReal_sum, Complex.ofReal_mul] at h
  exact h.trans (mul_comm _ _)

theorem adjacency_spectral_decomposition :
    (D.adjacency n ω).map Complex.ofReal =
      D.eigenvectorMatrix n ω * D.eigenvalueMatrix n ω * (D.eigenvectorMatrix n ω).transpose := by
  rw [← D.adjacency_mul_eigenvectorMatrix n ω, Matrix.mul_assoc,
    D.eigenvectorMatrix_mul_transpose n ω, mul_one]

/-- Explicit finite spectral expression, before identifying it with the
nonsingular matrix inverse. -/
def spectralResolvent (z : ℂ) : Matrix (Fin (N n)) (Fin (N n)) ℂ :=
  D.eigenvectorMatrix n ω * Matrix.diagonal (fun a => ((D.eigenvalue n ω a : ℂ) - z)⁻¹) *
    (D.eigenvectorMatrix n ω).transpose

theorem real_eigenvalue_sub_ne_zero (z : ℂ) (hz : z.im ≠ 0) (a : Fin (N n)) :
    (D.eigenvalue n ω a : ℂ) - z ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub, neg_eq_zero] at hi
  exact hz hi

theorem shifted_adjacency_mul_eigenvectorMatrix (z : ℂ) :
    ((D.adjacency n ω).map Complex.ofReal - z • (1 : Matrix (Fin (N n)) _ ℂ)) *
      D.eigenvectorMatrix n ω = D.eigenvectorMatrix n ω *
        Matrix.diagonal (fun a => (D.eigenvalue n ω a : ℂ) - z) := by
  rw [Matrix.sub_mul, D.adjacency_mul_eigenvectorMatrix n ω,
    Matrix.smul_mul, one_mul]
  ext v a
  simp only [eigenvalueMatrix, Matrix.mul_diagonal, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem shifted_adjacency_mul_spectralResolvent (z : ℂ) (hz : z.im ≠ 0) :
    ((D.adjacency n ω).map Complex.ofReal - z • (1 : Matrix (Fin (N n)) _ ℂ)) *
      D.spectralResolvent n ω z = 1 := by
  classical
  have hd : Matrix.diagonal (fun a => ((D.eigenvalue n ω a : ℂ) - z) *
      ((D.eigenvalue n ω a : ℂ) - z)⁻¹) = (1 : Matrix (Fin (N n)) _ ℂ) := by
    simp only [mul_inv_cancel₀ (D.real_eigenvalue_sub_ne_zero n ω z hz _)]
    exact Matrix.diagonal_one
  calc
    _ = ((((D.adjacency n ω).map Complex.ofReal - z • (1 : Matrix (Fin (N n)) _ ℂ)) *
        D.eigenvectorMatrix n ω) *
        Matrix.diagonal (fun a => ((D.eigenvalue n ω a : ℂ) - z)⁻¹)) *
        (D.eigenvectorMatrix n ω).transpose := by simp only [spectralResolvent, Matrix.mul_assoc]
    _ = (D.eigenvectorMatrix n ω *
        ((Matrix.diagonal (fun a => (D.eigenvalue n ω a : ℂ) - z)) *
          Matrix.diagonal (fun a => ((D.eigenvalue n ω a : ℂ) - z)⁻¹))) *
        (D.eigenvectorMatrix n ω).transpose := by
      rw [D.shifted_adjacency_mul_eigenvectorMatrix n ω z]
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.diagonal_mul_diagonal, hd, mul_one, D.eigenvectorMatrix_mul_transpose n ω]

/-- Nonreal invertibility of the actual finite adjacency shift. -/
theorem shifted_adjacency_isUnit (z : ℂ) (hz : z.im ≠ 0) :
    IsUnit ((D.adjacency n ω).map Complex.ofReal - z • (1 : Matrix (Fin (N n)) _ ℂ)) := by
  let A := (D.adjacency n ω).map Complex.ofReal - z • (1 : Matrix (Fin (N n)) _ ℂ)
  let R := D.spectralResolvent n ω z
  have h : A * R = 1 := D.shifted_adjacency_mul_spectralResolvent n ω z hz
  exact ⟨⟨A, R, h, Matrix.mul_eq_one_comm.mpr h⟩, rfl⟩

/-- The inverse definition of the resolvent agrees with the actual finite
spectral decomposition. -/
theorem resolvent_eq_spectral (z : ℂ) (hz : z.im ≠ 0) :
    D.resolvent n ω z = D.spectralResolvent n ω z := by
  exact Matrix.inv_eq_right_inv (D.shifted_adjacency_mul_spectralResolvent n ω z hz)

/-- Entrywise spectral expansion, with the real normalized eigenvectors. -/
theorem resolvent_entry (z : ℂ) (hz : z.im ≠ 0) (v w : Fin (N n)) :
    D.resolvent n ω z v w = ∑ a, ((D.eigenvalue n ω a : ℂ) - z)⁻¹ *
      (D.eigenvector n ω a v : ℂ) * (D.eigenvector n ω a w : ℂ) := by
  rw [D.resolvent_eq_spectral n ω z hz]
  rw [spectralResolvent, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, eigenvectorMatrix, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- The normalized trace is exactly the finite empirical Stieltjes transform. -/
theorem scalarResolvent_eq_spectral (z : ℂ) (hz : z.im ≠ 0) :
    D.scalarResolvent n ω z = (N n : ℂ)⁻¹ *
      ∑ a, ((D.eigenvalue n ω a : ℂ) - z)⁻¹ := by
  rw [scalarResolvent, D.resolvent_eq_spectral n ω z hz, spectralResolvent,
    Matrix.trace_mul_cycle, D.eigenvectorMatrix_transpose_mul n ω, one_mul]
  simp [Matrix.trace_diagonal]

/-- Real eigenchannels make the complex resolvent symmetric. -/
theorem resolvent_transpose (z : ℂ) (hz : z.im ≠ 0) :
    (D.resolvent n ω z).transpose = D.resolvent n ω z := by
  ext v w
  simp only [Matrix.transpose_apply, D.resolvent_entry n ω z hz]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- The Hermitian imaginary part of the genuine finite resolvent. -/
def resolventImaginaryPart (z : ℂ) : Matrix (Fin (N n)) (Fin (N n)) ℂ :=
  (-Complex.I / 2) • (D.resolvent n ω z - (D.resolvent n ω z).conjTranspose)

private theorem scalar_imaginaryPart (z : ℂ) :
    (-Complex.I / 2) * (z - star z) = (z.im : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im] <;> ring

/-- Imaginary resolvent entries are the finite Poisson-weighted spectral sum. -/
theorem resolvent_entry_im (z : ℂ) (hz : z.im ≠ 0) (v w : Fin (N n)) :
    (D.resolvent n ω z v w).im = ∑ a,
      (z.im / Complex.normSq ((D.eigenvalue n ω a : ℂ) - z)) *
        D.eigenvector n ω a v * D.eigenvector n ω a w := by
  rw [D.resolvent_entry n ω z hz]
  simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    mul_zero, zero_mul, zero_add, add_zero, Complex.inv_im, Complex.sub_im,
    zero_sub, neg_neg]

/-- The Hermitian imaginary part is a positive weighted Gram matrix. -/
theorem resolventImaginaryPart_eq_spectral (z : ℂ) (hz : z.im ≠ 0) :
    D.resolventImaginaryPart n ω z = D.eigenvectorMatrix n ω *
      Matrix.diagonal (fun a => ((z.im / Complex.normSq ((D.eigenvalue n ω a : ℂ) - z) : ℝ) : ℂ)) *
      (D.eigenvectorMatrix n ω).conjTranspose := by
  classical
  ext v w
  have hsym : D.resolvent n ω z w v = D.resolvent n ω z v w :=
    congrFun (congrFun (D.resolvent_transpose n ω z hz) v) w
  simp only [resolventImaginaryPart, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, hsym, scalar_imaginaryPart]
  rw [D.eigenvectorMatrix_conjTranspose n ω, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, eigenvectorMatrix, Matrix.transpose_apply,
    D.resolvent_entry_im n ω z hz, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Strict positivity in the upper half-plane is a finite spectral theorem. -/
theorem resolventImaginaryPart_posDef (z : ℂ) (hz : 0 < z.im) :
    (D.resolventImaginaryPart n ω z).PosDef := by
  rw [D.resolventImaginaryPart_eq_spectral n ω z (ne_of_gt hz)]
  have hp : (Matrix.diagonal (fun a =>
      ((z.im / Complex.normSq ((D.eigenvalue n ω a : ℂ) - z) : ℝ) : ℂ))).PosDef := by
    apply Matrix.PosDef.diagonal
    intro a
    exact Complex.zero_lt_real.mpr (div_pos hz (Complex.normSq_pos.mpr
      (D.real_eigenvalue_sub_ne_zero n ω z (ne_of_gt hz) a)))
  apply hp.mul_mul_conjTranspose_same
  exact Matrix.vecMul_injective_iff_isUnit.mpr (D.eigenvectorMatrix_isUnit n ω)

/-- The scalar Stieltjes transform has positive imaginary part. -/
theorem scalarResolvent_im_pos (z : ℂ) (hz : 0 < z.im) :
    0 < (D.scalarResolvent n ω z).im := by
  classical
  have hN : (0 : ℝ) < N n := Nat.cast_pos.mpr (D.size_pos n)
  have hsum : 0 < ∑ a : Fin (N n), z.im /
      Complex.normSq ((D.eigenvalue n ω a : ℂ) - z) := by
    apply Finset.sum_pos
    · intro a ha
      exact div_pos hz (Complex.normSq_pos.mpr
        (D.real_eigenvalue_sub_ne_zero n ω z (ne_of_gt hz) a))
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, D.size_pos n⟩⟩
  rw [D.scalarResolvent_eq_spectral n ω z (ne_of_gt hz)]
  have hcast : ((N n : ℂ)⁻¹) = Complex.ofReal ((N n : ℝ)⁻¹) := by simp
  rw [hcast]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.im_sum, Complex.inv_im, Complex.sub_im, zero_sub, neg_neg]
  exact mul_pos (inv_pos.mpr hN) hsum

/-- The squared resolvent has the squared spectral coefficients. -/
theorem resolvent_mul_conjTranspose_eq_spectral (z : ℂ) (hz : z.im ≠ 0) :
    D.resolvent n ω z * (D.resolvent n ω z).conjTranspose =
      D.eigenvectorMatrix n ω * Matrix.diagonal (fun a =>
        (Complex.normSq (((D.eigenvalue n ω a : ℂ) - z)⁻¹) : ℂ)) *
        (D.eigenvectorMatrix n ω).conjTranspose := by
  classical
  let U := D.eigenvectorMatrix n ω
  let B := Matrix.diagonal (fun a => ((D.eigenvalue n ω a : ℂ) - z)⁻¹)
  have hU : U.conjTranspose = U.transpose := D.eigenvectorMatrix_conjTranspose n ω
  have hUT : U.transpose.conjTranspose = U := by
    rw [← hU, Matrix.conjTranspose_conjTranspose]
  have hR : D.resolvent n ω z = U * B * U.transpose := D.resolvent_eq_spectral n ω z hz
  have hstar : (U * B * U.transpose).conjTranspose = U * B.conjTranspose * U.transpose := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hUT, hU]
    simp only [Matrix.mul_assoc]
  have hB : B * B.conjTranspose = Matrix.diagonal (fun a =>
      (Complex.normSq (((D.eigenvalue n ω a : ℂ) - z)⁻¹) : ℂ)) := by
    simp only [B, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    change Matrix.diagonal (fun a => ((D.eigenvalue n ω a : ℂ) - z)⁻¹ *
      star (((D.eigenvalue n ω a : ℂ) - z)⁻¹)) = _
    simp only [Complex.star_def, Complex.mul_conj]
  rw [hR, hstar]
  calc
    _ = U * (B * (U.transpose * U) * B.conjTranspose) * U.transpose := by
      simp only [Matrix.mul_assoc]
    _ = U * (B * B.conjTranspose) * U.transpose := by
      rw [show U.transpose * U = 1 from D.eigenvectorMatrix_transpose_mul n ω, mul_one]
    _ = _ := by rw [hB, ← hU]

/-- Finite matrix Ward identity with the exact imaginary part convention. -/
theorem resolvent_ward_matrix (z : ℂ) (hz : z.im ≠ 0) :
    D.resolventImaginaryPart n ω z =
      (z.im : ℂ) • (D.resolvent n ω z * (D.resolvent n ω z).conjTranspose) := by
  classical
  rw [D.resolventImaginaryPart_eq_spectral n ω z hz,
    D.resolvent_mul_conjTranspose_eq_spectral n ω z hz]
  have hdiag : Matrix.diagonal (fun a =>
      ((z.im / Complex.normSq ((D.eigenvalue n ω a : ℂ) - z) : ℝ) : ℂ)) =
    (z.im : ℂ) • Matrix.diagonal (fun a =>
      (Complex.normSq (((D.eigenvalue n ω a : ℂ) - z)⁻¹) : ℂ)) := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp [Matrix.diagonal, Complex.normSq_inv, div_eq_mul_inv]
    · simp [Matrix.diagonal, hab]
  rw [hdiag]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- The row Ward identity, in the form used for remote resolvent tails. -/
theorem resolvent_ward_row (z : ℂ) (hz : z.im ≠ 0) (v : Fin (N n)) :
    (∑ w, Complex.normSq (D.resolvent n ω z v w)) = (D.resolvent n ω z v v).im / z.im := by
  have he := congrFun (congrFun (D.resolvent_ward_matrix n ω z hz) v) v
  simp only [resolventImaginaryPart, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, scalar_imaginaryPart,
    Matrix.mul_apply] at he
  have hnorm : (fun w => D.resolvent n ω z v w * star (D.resolvent n ω z v w)) =
      (fun w => (Complex.normSq (D.resolvent n ω z v w) : ℂ)) := by
    funext w
    exact Complex.mul_conj _
  rw [hnorm] at he
  have hr := congrArg Complex.re he
  simp only [← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re] at hr
  apply (eq_div_iff hz).mpr
  simpa only [mul_comm] using hr.symm

end GeneralizedBulk.External.RegularSpectralData
