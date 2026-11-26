import Mathlib

/-! A descending real symmetric eigenbasis with a prescribed unit top vector.
Reflection inside the top eigenspace handles multiplicities, without a
connectedness or simple-spectrum assumption. -/
noncomputable section
set_option maxHeartbeats 2000000
open Matrix
open scoped RealInnerProductSpace BigOperators Classical

namespace GeneralizedBulk.Graph.CanonicalSpectrum

theorem symmetric_commutes_reflection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (w : E) (a : ℝ) (hw : T w = a • w) (x : E) :
    T ((ℝ ∙ w)ᗮ.reflection x) = (ℝ ∙ w)ᗮ.reflection (T x) := by
  have hi : ⟪w, T x⟫ = a * ⟪w,x⟫ := by
    rw [← hT w x,hw,real_inner_smul_left]
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply,
    Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [map_neg,map_sub,map_smul,map_nsmul,hw,hi,smul_smul]
  congr 2
  ring

variable {M : ℕ} {A : Matrix (Fin M) (Fin M) ℝ}

def permutation (hA : A.IsHermitian) : Equiv.Perm (Fin M) :=
  Tuple.sort (fun i => OrderDual.toDual (hA.eigenvalues i))

def value (hA : A.IsHermitian) (i : Fin M) : ℝ := hA.eigenvalues (permutation hA i)

def basis (hA : A.IsHermitian) : OrthonormalBasis (Fin M) ℝ (EuclideanSpace ℝ (Fin M)) :=
  hA.eigenvectorBasis.reindex (permutation hA).symm

theorem value_antitone (hA : A.IsHermitian) : Antitone (value hA) :=
  Tuple.monotone_sort (fun i => OrderDual.toDual (hA.eigenvalues i))

theorem basis_eigen (hA : A.IsHermitian) (i : Fin M) :
    A.toEuclideanLin (basis hA i) = value hA i • basis hA i := by
  apply PiLp.ext
  intro v
  have h := congrFun (hA.mulVec_eigenvectorBasis (permutation hA i)) v
  simpa only [basis,value,OrthonormalBasis.reindex_apply,Equiv.symm_symm,
    Matrix.toEuclideanLin_apply,PiLp.smul_apply,Pi.smul_apply,smul_eq_mul] using h

theorem top_value (hA : A.IsHermitian) (hM : 0 < M)
    (u : EuclideanSpace ℝ (Fin M)) (hu : ‖u‖ = 1) (a : ℝ)
    (he : A.toEuclideanLin u = a • u)
    (hbound : ∀ i, hA.eigenvalues i ≤ a) : value hA ⟨0,hM⟩ = a := by
  have hne : u ≠ 0 := by intro h; simpa [h] using hu
  have hs : a ∈ spectrum ℝ A := by
    rw [← Matrix.IsHermitian.spectrum_toEuclideanLin (A := A)]
    exact (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr he,hne⟩).mem_spectrum
  rw [hA.eigenvalues_eq_spectrum_real] at hs
  obtain ⟨j,hj⟩ := hs
  apply le_antisymm (hbound _)
  let i := (permutation hA).symm j
  have hi : value hA i = a := by simp [value,i,hj]
  rw [←hi]
  exact value_antitone hA (show (⟨0,hM⟩ : Fin M) ≤ i by exact Nat.zero_le _)

def pinnedBasis (hA : A.IsHermitian) (hM : 0 < M)
    (u : EuclideanSpace ℝ (Fin M)) :
    OrthonormalBasis (Fin M) ℝ (EuclideanSpace ℝ (Fin M)) :=
  (basis hA).map ((ℝ ∙ (basis hA ⟨0,hM⟩ - u))ᗮ.reflection)

theorem pinnedBasis_first (hA : A.IsHermitian) (hM : 0 < M)
    (u : EuclideanSpace ℝ (Fin M)) (hu : ‖u‖ = 1) :
    pinnedBasis hA hM u ⟨0,hM⟩ = u := by
  change (ℝ ∙ (basis hA ⟨0,hM⟩ - u))ᗮ.reflection (basis hA ⟨0,hM⟩) = u
  apply Submodule.reflection_sub
  rw [(basis hA).orthonormal.1 _,hu]

theorem pinnedBasis_eigen (hA : A.IsHermitian) (hM : 0 < M)
    (u : EuclideanSpace ℝ (Fin M)) (hu : ‖u‖ = 1) (a : ℝ)
    (he : A.toEuclideanLin u = a • u)
    (hbound : ∀ i, hA.eigenvalues i ≤ a) (i : Fin M) :
    A.toEuclideanLin (pinnedBasis hA hM u i) = value hA i • pinnedBasis hA hM u i := by
  have htop := top_value hA hM u hu a he hbound
  have hw : A.toEuclideanLin (basis hA ⟨0,hM⟩ - u) =
      a • (basis hA ⟨0,hM⟩ - u) := by
    rw [map_sub,basis_eigen,htop,he,smul_sub]
  change A.toEuclideanLin ((ℝ ∙ (basis hA ⟨0,hM⟩ - u))ᗮ.reflection (basis hA i)) = _
  rw [symmetric_commutes_reflection A.toEuclideanLin
    (Matrix.isHermitian_iff_isSymmetric.mp hA) _ a hw, basis_eigen, map_smul]
  rfl

end GeneralizedBulk.Graph.CanonicalSpectrum
