import GaussianWave.BS.GaussianBallReference
import GaussianWave.BS.ColoredInnovationCharts

/-! The actual invertible change from raw innovation coordinates to the
constructed isometric intrinsic ball coordinates. -/
noncomputable section
namespace GaussianWave.BS

theorem fullColumnFactor_injective {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq I] (M : Matrix V I ℝ) (hM : (M.transpose * M).det ≠ 0) :
    Function.Injective M.mulVec := by
  have hG : Function.Injective (M.transpose * M).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hM))
  intro x y hxy
  apply hG
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]

def vertexOrthoSolutionLinear (m k : ℕ) (energy : ℝ) :
    (VertexBallInnovation (m + 2) k → ℝ) →ₗ[ℝ] vertexBallEigenSpace m k energy :=
  (vertexOrthoGaussianMap m k energy).codRestrict _ (fun z =>
    ⟨vertexGaussianInnovation m k energy (vertexOrthoInputLift m k z), rfl⟩)

def edgeOrthoSolutionLinear (m k : ℕ) (energy : ℝ) :
    (EdgeBallInnovation (m + 2) k → ℝ) →ₗ[ℝ] edgeBallEigenSpace m k energy :=
  (edgeOrthoGaussianMap m k energy).codRestrict _ (fun z =>
    ⟨edgeGaussianInnovation m k energy (edgeOrthoInputLift m k z), rfl⟩)

def vertexOrthoSolutionEquiv (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    (VertexBallInnovation (m + 2) k → ℝ) ≃ₗ[ℝ] vertexBallEigenSpace m k energy := by
  let F := vertexOrthoSolutionLinear m k energy
  have hM : (vertexOrthoFactorMatrix m k energy).mulVec = vertexOrthoGaussianMap m k energy :=
    congrArg DFunLike.coe (Matrix.toLin'_toMatrix' (vertexOrthoGaussianMap m k energy))
  have hinj : Function.Injective F := by
    intro x y hxy
    apply fullColumnFactor_injective _ (vertexOrthoFactorMatrix_gram_det_pos m k energy he).ne'
    rw [hM]
    exact congrArg Subtype.val hxy
  have hdim : Module.finrank ℝ (VertexBallInnovation (m + 2) k → ℝ) =
      Module.finrank ℝ (vertexBallEigenSpace m k energy) := (vertexBallSolutionEquiv m k energy).finrank_eq
  exact LinearEquiv.ofBijective F ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

def edgeOrthoSolutionEquiv (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    (EdgeBallInnovation (m + 2) k → ℝ) ≃ₗ[ℝ] edgeBallEigenSpace m k energy := by
  let F := edgeOrthoSolutionLinear m k energy
  have hM : (edgeOrthoFactorMatrix m k energy).mulVec = edgeOrthoGaussianMap m k energy :=
    congrArg DFunLike.coe (Matrix.toLin'_toMatrix' (edgeOrthoGaussianMap m k energy))
  have hinj : Function.Injective F := by
    intro x y hxy
    apply fullColumnFactor_injective _ (edgeOrthoFactorMatrix_gram_det_pos m k energy he).ne'
    rw [hM]
    exact congrArg Subtype.val hxy
  have hdim : Module.finrank ℝ (EdgeBallInnovation (m + 2) k → ℝ) =
      Module.finrank ℝ (edgeBallEigenSpace m k energy) := (edgeBallSolutionEquiv m k energy).finrank_eq
  exact LinearEquiv.ofBijective F ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

theorem vertexGaussianIsometricChart_on_space (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (x : vertexBallEigenSpace m k energy) :
    (vertexGaussianIsometricChart m k energy he).transpose.mulVec
      ((vertexGaussianIsometricChart m k energy he).mulVec x) = x := by
  obtain ⟨z, rfl⟩ := (vertexOrthoSolutionEquiv m k energy he).surjective x
  have h := congrArg (fun M => M.mulVec z) (vertexGaussianIsometricChart_projection m k energy he)
  have hM : (vertexOrthoFactorMatrix m k energy).mulVec = vertexOrthoGaussianMap m k energy :=
    congrArg DFunLike.coe (Matrix.toLin'_toMatrix' (vertexOrthoGaussianMap m k energy))
  simpa only [← Matrix.mulVec_mulVec, hM] using h

theorem edgeGaussianIsometricChart_on_space (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (x : edgeBallEigenSpace m k energy) :
    (edgeGaussianIsometricChart m k energy he).transpose.mulVec
      ((edgeGaussianIsometricChart m k energy he).mulVec x) = x := by
  obtain ⟨z, rfl⟩ := (edgeOrthoSolutionEquiv m k energy he).surjective x
  have h := congrArg (fun M => M.mulVec z) (edgeGaussianIsometricChart_projection m k energy he)
  have hM : (edgeOrthoFactorMatrix m k energy).mulVec = edgeOrthoGaussianMap m k energy :=
    congrArg DFunLike.coe (Matrix.toLin'_toMatrix' (edgeOrthoGaussianMap m k energy))
  simpa only [← Matrix.mulVec_mulVec, hM] using h

def intrinsicCoordinateEquiv {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V]
    (S : Submodule ℝ (V → ℝ)) (F : (I → ℝ) ≃ₗ[ℝ] S) (O : Matrix I V ℝ)
    (hO : ∀ x : S, O.transpose.mulVec (O.mulVec x) = x) :
    (I → ℝ) ≃ₗ[ℝ] (I → ℝ) := by
  let L : (I → ℝ) →ₗ[ℝ] (I → ℝ) := O.toLin'.comp (S.subtype.comp F.toLinearMap)
  have hi : Function.Injective L := by
    intro x y hxy
    apply F.injective
    apply Subtype.ext
    have h := congrArg O.transpose.mulVec hxy
    change O.transpose.mulVec (O.mulVec (F x)) = O.transpose.mulVec (O.mulVec (F y)) at h
    exact (hO (F x)).symm.trans (h.trans (hO (F y)))
  exact LinearEquiv.ofBijective L ⟨hi,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

def vertexInnovationToIntrinsic (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :=
  intrinsicCoordinateEquiv (vertexBallEigenSpace m k energy) (vertexBallSolutionEquiv m k energy)
    (vertexGaussianIsometricChart m k energy he) (vertexGaussianIsometricChart_on_space m k energy he)

def edgeInnovationToIntrinsic (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :=
  intrinsicCoordinateEquiv (edgeBallEigenSpace m k energy) (edgeBallSolutionEquiv m k energy)
    (edgeGaussianIsometricChart m k energy he) (edgeGaussianIsometricChart_on_space m k energy he)

@[simp] theorem vertexInnovationToIntrinsic_apply (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (z : VertexBallInnovation (m + 2) k → ℝ) :
    vertexInnovationToIntrinsic m k energy he z =
      (vertexGaussianIsometricChart m k energy he).mulVec (vertexBallBuild m k energy z) := rfl

@[simp] theorem edgeInnovationToIntrinsic_apply (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (z : EdgeBallInnovation (m + 2) k → ℝ) :
    edgeInnovationToIntrinsic m k energy he z =
      (edgeGaussianIsometricChart m k energy he).mulVec (edgeBallBuild m k energy z) := rfl

theorem vertexInnovationToIntrinsic_inverse_chart (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (x : VertexBallVertex (m + 2) k → ℝ)
    (hx : VertexBallEigenrelation m k energy x) :
    (vertexInnovationToIntrinsic m k energy he).symm
      ((vertexGaussianIsometricChart m k energy he).mulVec x) = vertexBallExtract m k x := by
  apply (vertexInnovationToIntrinsic m k energy he).injective
  rw [LinearEquiv.apply_symm_apply, vertexInnovationToIntrinsic_apply,
    vertexBallBuild_extract m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)) x hx]

theorem edgeInnovationToIntrinsic_inverse_chart (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (x : EdgeBallVertex (m + 2) k → ℝ)
    (hx : EdgeBallEigenrelation m k energy x) :
    (edgeInnovationToIntrinsic m k energy he).symm
      ((edgeGaussianIsometricChart m k energy he).mulVec x) = edgeBallExtract m k x := by
  apply (edgeInnovationToIntrinsic m k energy he).injective
  rw [LinearEquiv.apply_symm_apply, edgeInnovationToIntrinsic_apply,
    edgeBallBuild_extract m k energy x hx]

end GaussianWave.BS
