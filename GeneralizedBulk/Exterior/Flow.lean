import GeneralizedBulk.Exterior.MatrixCalculus

/-!
# Constructed exterior flow and its polynomial responses

The path is an explicit trigonometric conjugation followed by an actual matrix
inverse. Positivity gives its existence at every real angle. The derivative
formulas are derived with the matrix calculus of the preceding module.
-/
noncomputable section
open scoped BigOperators ComplexOrder
namespace GeneralizedBulk.Exterior

/-- Holomorphic extension of the real exterior path. -/
def complexExterior (K : Mat) (z : ℂ) : Mat := rotation z * K * (rotation z).transpose

/-- Holomorphic extension of the reconstructed endpoint resolvent. -/
def complexResolvent (K : Mat) (z : ℂ) : Mat :=
  ((GeneralizedSwitching.edgeMatrix : Mat) - complexExterior K z)⁻¹

@[simp] theorem complexExterior_real (K : Mat) (t : ℝ) :
    complexExterior K t = exteriorPath K t := (exteriorPath_eq_transpose K t).symm

@[simp] theorem complexResolvent_real (K : Mat) (t : ℝ) :
    complexResolvent K t = resolventPath K t := by simp [complexResolvent, resolventPath]

theorem hasDerivAt_complexExterior (K : Mat) (z : ℂ) :
    HasDerivAt (complexExterior K)
      (rotationGenerator * complexExterior K z - complexExterior K z * rotationGenerator) z := by
  have hQ := hasDerivAt_rotation z
  have h := hasDerivAt_matrix_mul
    (hasDerivAt_matrix_mul hQ (hasDerivAt_matrix_const K z))
    (hasDerivAt_matrix_transpose hQ)
  convert h using 1
  simp only [complexExterior, Matrix.mul_zero, add_zero, Matrix.transpose_mul,
    rotationGenerator_transpose]
  noncomm_ring

/-- The ordered resolvent sandwich reduces to the polynomial matrix response. -/
theorem resolvent_response_algebra (K M : Mat)
    (hleft : M * (GeneralizedSwitching.edgeMatrix - K) = 1)
    (hright : (GeneralizedSwitching.edgeMatrix - K) * M = 1) :
    M * (rotationGenerator * K - K * rotationGenerator) * M = matrixResponse M := by
  have hMK : M * K = M * GeneralizedSwitching.edgeMatrix - 1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact (sub_eq_iff_eq_add.mp (by simpa only [Matrix.mul_sub] using hleft)).symm
  have hKM : K * M = GeneralizedSwitching.edgeMatrix * M - 1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact (sub_eq_iff_eq_add.mp (by simpa only [Matrix.sub_mul] using hright)).symm
  calc
    _ = M * rotationGenerator * (K * M) - (M * K) * rotationGenerator * M := by noncomm_ring
    _ = rotationGenerator * M - M * rotationGenerator +
        M * (rotationGenerator * GeneralizedSwitching.edgeMatrix -
          GeneralizedSwitching.edgeMatrix * rotationGenerator) * M := by
      rw [hKM, hMK]
      noncomm_ring
    _ = matrixResponse M := by
      rw [rotation_edge_commutator]
      simp only [matrixResponse, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- The inverse has the precise polynomial derivative at every nonsingular
point of the holomorphic extension. -/
theorem hasDerivAt_complexResolvent (K : Mat) (z : ℂ)
    (hu : IsUnit ((GeneralizedSwitching.edgeMatrix : Mat) - complexExterior K z)) :
    HasDerivAt (complexResolvent K) (matrixResponse (complexResolvent K z)) z := by
  have hK := hasDerivAt_complexExterior K z
  have h := hasDerivAt_matrix_inverse (hasDerivAt_matrix_sub (hasDerivAt_matrix_const (GeneralizedSwitching.edgeMatrix : Mat) z) hK) hu
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hr := resolvent_response_algebra (complexExterior K z) (complexResolvent K z)
    (Matrix.nonsing_inv_mul _ hdet) (Matrix.mul_nonsing_inv _ hdet)
  convert h using 1
  rw [← hr]
  simp only [complexResolvent, zero_sub]
  noncomm_ring

/-- Restriction of a holomorphic matrix path to a real angle has the same
matrix derivative, interpreted over the real scalar field. -/
theorem hasDerivAt_matrix_real_restrict {f : ℂ → Mat} {f' : Mat} {t : ℝ}
    (hf : HasDerivAt f f' (t : ℂ)) : HasDerivAt (fun s : ℝ => f s) f' t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i)) j).comp_ofReal

/-- Positivity supplies nonsingularity, so this derivative holds at every
real angle with no separate inverse or response assumption. -/
theorem hasDerivAt_resolventPath (K : Mat)
    (hK : ImaginarySignDefinite K) (t : ℝ) :
    HasDerivAt (resolventPath K) (matrixResponse (resolventPath K t)) t := by
  have hunit := exteriorPath_resolvent_isUnit_of_signDefinite K hK t
  have h := hasDerivAt_complexResolvent K t (by simpa using hunit)
  simpa only [complexResolvent_real] using hasDerivAt_matrix_real_restrict h

/-- The spectral derivative matrix enters scalar reconstruction through this
trace. Here `L` is the spectral derivative of the exterior self-energy. -/
def scalarPath (tau : ℂ) (K L : Mat) (t : ℝ) : ℂ :=
  tau + Matrix.trace (resolventPath K t * exteriorPath L t)

private theorem trace_four_cycle (A B C E : Mat) :
    Matrix.trace (A * B * C * E) = Matrix.trace (B * C * E * A) := by
  calc
    _ = Matrix.trace (A * (B * C * E)) := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_comm A (B * C * E)

set_option maxHeartbeats 2000000 in
/-- The commutators cancel inside the scalar trace. -/
theorem scalar_response_algebra (M L : Mat) :
    Matrix.trace (matrixResponse M * L +
      M * (rotationGenerator * L - L * rotationGenerator)) =
      2 * Matrix.trace (signMatrix * M * L * M) := by
  have hm : matrixResponse M * L + M * (rotationGenerator * L - L * rotationGenerator) =
      rotationGenerator * (M * L) - (M * L) * rotationGenerator +
        (2 : ℂ) • (M * signMatrix * M * L) := by
    simp only [matrixResponse, smul_eq_mul, Matrix.smul_mul]
    noncomm_ring
  rw [hm, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_mul_comm rotationGenerator (M * L), sub_self, zero_add]
  change (2 : ℂ) * Matrix.trace (M * signMatrix * M * L) =
    2 * Matrix.trace (signMatrix * M * L * M)
  exact congrArg (fun z : ℂ => 2 * z) (trace_four_cycle M signMatrix M L)

theorem hasDerivAt_trace {f : ℂ → Mat} {f' : Mat} {z : ℂ}
    (hf : HasDerivAt f f' z) :
    HasDerivAt (fun u => Matrix.trace (f u)) (Matrix.trace f') z := by
  exact HasDerivAt.sum (fun i _ => (hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i)) i)

/-- The scalar response is computed directly from the reconstructed trace,
so no exchange of mixed derivatives is assumed. -/
theorem hasDerivAt_scalarPath (tau : ℂ) (K L : Mat)
    (hK : ImaginarySignDefinite K) (t : ℝ) :
    HasDerivAt (scalarPath tau K L)
      (2 * Matrix.trace (signMatrix * resolventPath K t * exteriorPath L t *
        resolventPath K t)) t := by
  have hu : IsUnit ((GeneralizedSwitching.edgeMatrix : Mat) - complexExterior K t) := by
    simpa only [complexExterior_real] using exteriorPath_resolvent_isUnit_of_signDefinite K hK t
  have hm := hasDerivAt_complexResolvent K t hu
  have hl := hasDerivAt_complexExterior L t
  have hs := (hasDerivAt_trace (hasDerivAt_matrix_mul hm hl)).const_add tau
  rw [scalar_response_algebra] at hs
  have hs' := hs.comp_ofReal
  simpa only [complexResolvent_real, complexExterior_real, scalarPath] using hs'

/-- The centered sign observable has the polynomial sign-trace response. -/
theorem hasDerivAt_signTracePath (K : Mat)
    (hK : ImaginarySignDefinite K) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Matrix.trace (signMatrix * resolventPath K u))
      (Matrix.trace (signMatrix * matrixResponse (resolventPath K t))) t := by
  have hu : IsUnit ((GeneralizedSwitching.edgeMatrix : Mat) - complexExterior K t) := by
    simpa only [complexExterior_real] using exteriorPath_resolvent_isUnit_of_signDefinite K hK t
  have hm := hasDerivAt_complexResolvent K t hu
  have hh := hasDerivAt_trace
    (hasDerivAt_matrix_mul (hasDerivAt_matrix_const (signMatrix : Mat) t) hm)
  have hh' := hh.comp_ofReal
  simpa only [zero_mul, zero_add, complexResolvent_real] using hh'

end GeneralizedBulk.Exterior
