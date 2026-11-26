import GeneralizedBulk.Entropy.GaussianSubspaceChannels

/-! Every finite-dimensional real observation subspace has a concrete
orthogonal-coordinate realization, constructed by extending its basis. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- Extend an actual orthonormal basis of a subspace to a basis of the ambient
space. Every basis vector outside the subspace is orthogonal to it. -/
theorem exists_observation_basis (reference : OrthonormalBasis I ℝ E) (S : Submodule ℝ E) :
    ∃ b : OrthonormalBasis I ℝ E, ∀ j, b j ∉ S → ∀ x : S, @inner ℝ E _ (b j) x = 0 := by
  classical
  let a := stdOrthonormalBasis ℝ S
  let v : Fin (Module.finrank ℝ S) → E := fun i => a i
  have hv : Orthonormal ℝ v := S.subtypeₗᵢ.orthonormal_comp_iff.mpr a.orthonormal
  have hrange : Orthonormal ℝ ((↑) : Set.range v → E) :=
    (orthonormal_subtype_range hv.linearIndependent.injective).2 hv
  obtain ⟨u, b, hu, hb⟩ := hrange.exists_orthonormalBasis_extension
  have hcard : Fintype.card I = Fintype.card u := by
    rw [← Module.finrank_eq_card_basis reference.toBasis, ← Module.finrank_eq_card_basis b.toBasis]
  let e : I ≃ u := Fintype.equivOfCardEq hcard
  refine ⟨b.reindex e.symm, ?_⟩
  intro j hj x
  have hv0 (l : Fin (Module.finrank ℝ S)) : @inner ℝ E _ ((b.reindex e.symm) j) (v l) = 0 := by
    have hl : v l ∈ u := hu ⟨l, rfl⟩
    let m : u := ⟨v l, hl⟩
    have hm : b m = v l := by simpa only [m] using congrFun hb m
    have hne : e j ≠ m := by
      intro heq
      apply hj
      simp only [OrthonormalBasis.reindex_apply, Equiv.symm_symm] at hj ⊢
      rw [heq, hm]
      exact (a l).property
    simp only [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
    rw [← hm]
    exact b.orthonormal.inner_eq_zero hne
  have hx := a.sum_repr x
  have hxe : (∑ l, a.repr x l • v l) = (x : E) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using congrArg (fun y : S => (y : E)) hx
  rw [← hxe, inner_sum]
  simp only [inner_smul_right, hv0, mul_zero, Finset.sum_const_zero]


/-- A fixed orthonormal coordinate realization of the observation subspace. -/
def observationBasis (reference : OrthonormalBasis I ℝ E) (S : Submodule ℝ E) : OrthonormalBasis I ℝ E :=
  Classical.choose (exists_observation_basis reference S)

def observationIndices (reference : OrthonormalBasis I ℝ E) (S : Submodule ℝ E) : Finset I := by
  classical
  exact Finset.univ.filter (fun j => observationBasis reference S j ∈ S)

@[simp] theorem mem_observationIndices (reference : OrthonormalBasis I ℝ E) (S : Submodule ℝ E) (j : I) :
    j ∈ observationIndices reference S ↔ observationBasis reference S j ∈ S := by
  classical
  simp [observationIndices]

theorem observationBasis_mem_iff (reference : OrthonormalBasis I ℝ E) (S : Submodule ℝ E) (x : E) :
    x ∈ S ↔ ∀ j, j ∉ observationIndices reference S → (observationBasis reference S).repr x j = 0 := by
  classical
  constructor
  · intro hx j hj
    rw [OrthonormalBasis.repr_apply_apply]
    exact Classical.choose_spec (exists_observation_basis reference S) j
      ((mem_observationIndices reference S j).not.mp hj) ⟨x, hx⟩
  · intro hx
    rw [← (observationBasis reference S).sum_repr x]
    apply S.sum_mem
    intro j hj
    by_cases hjs : j ∈ observationIndices reference S
    · exact S.smul_mem _ ((mem_observationIndices reference S j).mp hjs)
    · rw [hx j hjs, zero_smul]
      exact S.zero_mem

/-- The actual matrix from observation coordinates to the fixed reference
coordinates. -/
def observationMatrix (reference : OrthonormalBasis I ℝ E) (S : Submodule ℝ E) : Matrix I I ℝ :=
  reference.toBasis.toMatrix (observationBasis reference S)

theorem observationMatrix_orthogonal (reference : OrthonormalBasis I ℝ E) (S : Submodule ℝ E) :
    observationMatrix reference S * (observationMatrix reference S).transpose = 1 := by
  simpa only [Matrix.conjTranspose, star_trivial, Matrix.map_id] using
    reference.toMatrix_orthonormalBasis_self_mul_conjTranspose (observationBasis reference S)

/-- The inverse observation matrix computes the actual orthonormal
coordinates in the observation-adapted basis. -/
theorem observationMatrix_transpose_repr (reference : OrthonormalBasis I ℝ E) (S : Submodule ℝ E) (x : E) :
    (observationMatrix reference S).transpose.mulVec (reference.repr x) =
      (observationBasis reference S).repr x := by
  have hm : (observationMatrix reference S).mulVec ((observationBasis reference S).repr x) = reference.repr x := by
    exact Basis.toMatrix_mulVec_repr (b := (observationBasis reference S).toBasis)
      (b' := reference.toBasis) x
  have ho := observationMatrix_orthogonal reference S
  have he := congrArg ((observationMatrix reference S).transpose.mulVec) hm
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_eq_one_comm.mpr ho,
    Matrix.one_mulVec] using he.symm


/-- A genuine orthogonal endomorphism in fixed orthonormal coordinates. -/
def isometryMatrix (reference : OrthonormalBasis I ℝ E) (R : E ≃ₗᵢ[ℝ] E) : Matrix I I ℝ :=
  reference.toBasis.toMatrix (reference.map R)

theorem isometryMatrix_orthogonal (reference : OrthonormalBasis I ℝ E) (R : E ≃ₗᵢ[ℝ] E) :
    isometryMatrix reference R * (isometryMatrix reference R).transpose = 1 := by
  simpa only [Matrix.conjTranspose, star_trivial, Matrix.map_id] using
    reference.toMatrix_orthonormalBasis_self_mul_conjTranspose (reference.map R)

theorem isometryMatrix_repr (reference : OrthonormalBasis I ℝ E) (R : E ≃ₗᵢ[ℝ] E) (x : E) :
    (isometryMatrix reference R).mulVec (reference.repr x) = reference.repr (R x) := by
  have hrep : (reference.map R).repr (R x) = reference.repr x := by
    change reference.repr (R.symm (R x)) = _
    rw [R.symm_apply_apply]
  have hm : (isometryMatrix reference R).mulVec ((reference.map R).repr (R x)) = reference.repr (R x) :=
    Basis.toMatrix_mulVec_repr (b := (reference.map R).toBasis) (b' := reference.toBasis) (R x)
  rw [hrep] at hm
  exact hm

/-- Reference coordinates preserve the actual Euclidean bilinear form. -/
theorem orthonormalCoordinates_dot (reference : OrthonormalBasis I ℝ E) (x y : E) :
    (∑ j, reference.repr x j * reference.repr y j) = @inner ℝ E _ x y := by
  have h := reference.repr.inner_map_map x y
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm] using h

theorem orthonormalCoordinates_sq (reference : OrthonormalBasis I ℝ E) (x : E) :
    (∑ j, (reference.repr x j) ^ 2) = ‖x‖ ^ 2 := by
  simpa only [← pow_two, real_inner_self_eq_norm_sq] using orthonormalCoordinates_dot reference x x

end GeneralizedBulk.Entropy.Channel
