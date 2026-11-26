import GeneralizedBulk.Graph.CanonicalEigenbasis

/-! A prescribed unit eigenvector can be inserted into an ordered real
orthonormal eigenbasis without changing its eigenvalue list. Every different
eigenspace, in particular the constant top mode for a bulk vector, is fixed. -/
noncomputable section
open scoped Classical BigOperators RealInnerProductSpace

namespace GeneralizedBulk.Graph.CanonicalSpectrum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem inner_eq_zero_of_eigenvalues_ne (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (u v : E) (a b : ℝ) (hu : T u = a • u) (hv : T v = b • v)
    (hab : a ≠ b) : ⟪u,v⟫ = 0 := by
  have hm : a*⟪u,v⟫ = b*⟪u,v⟫ := by
    calc
      a*⟪u,v⟫ = ⟪T u,v⟫ := by rw [hu,real_inner_smul_left]
      _ = ⟪u,T v⟫ := hT u v
      _ = b*⟪u,v⟫ := by rw [hv,real_inner_smul_right]
  exact (mul_eq_mul_right_iff.mp hm).resolve_left hab

def eigenbasisPinning {M : ℕ} (b : OrthonormalBasis (Fin M) ℝ E)
    (j : Fin M) (q : E) : OrthonormalBasis (Fin M) ℝ E :=
  b.map ((ℝ ∙ (b j-q))ᗮ.reflection)

theorem eigenbasisPinning_at {M : ℕ} (b : OrthonormalBasis (Fin M) ℝ E)
    (j : Fin M) (q : E) (hq : ‖q‖ = 1) : eigenbasisPinning b j q j = q := by
  change (ℝ ∙ (b j-q))ᗮ.reflection (b j) = q
  apply Submodule.reflection_sub
  rw [b.orthonormal.1 _,hq]

theorem eigenbasisPinning_eigen {M : ℕ} (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis (Fin M) ℝ E) (value : Fin M → ℝ)
    (hb : ∀ i,T (b i)=value i • b i)
    (j : Fin M) (q : E) (a : ℝ) (hj : value j=a) (hq : T q=a • q) (i : Fin M) :
    T (eigenbasisPinning b j q i) = value i • eigenbasisPinning b j q i := by
  have hw : T (b j-q)=a • (b j-q) := by rw [map_sub,hb j,hj,hq,smul_sub]
  change T ((ℝ ∙ (b j-q))ᗮ.reflection (b i)) = _
  rw [symmetric_commutes_reflection T hT _ a hw,hb i,map_smul]
  rfl

theorem eigenbasisPinning_fixed {M : ℕ} (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis (Fin M) ℝ E) (value : Fin M → ℝ)
    (hb : ∀ i,T (b i)=value i • b i)
    (j : Fin M) (q : E) (a : ℝ) (hj : value j=a) (hq : T q=a • q)
    (i : Fin M) (hi : value i ≠ a) : eigenbasisPinning b j q i = b i := by
  have hw : T (b j-q)=a • (b j-q) := by rw [map_sub,hb j,hj,hq,smul_sub]
  change (ℝ ∙ (b j-q))ᗮ.reflection (b i) = b i
  apply Submodule.reflection_mem_subspace_eq_self
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  exact inner_eq_zero_of_eigenvalues_ne T hT _ _ (value i) a (hb i) hw hi

/-- Insert an arbitrary unit eigenvector into an existing ordered eigenbasis.
Repeated eigenvalues are allowed. No eigenvalue or measurability certificate
is assumed in finding the appropriate index. -/
theorem exists_eigenbasis_pinning {M : ℕ} (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis (Fin M) ℝ E) (value : Fin M → ℝ)
    (hb : ∀ i,T (b i)=value i • b i)
    (q : E) (a : ℝ) (hqnorm : ‖q‖=1) (hq : T q=a • q) :
    ∃ j : Fin M, value j=a ∧ eigenbasisPinning b j q j=q ∧
      (∀ i,T (eigenbasisPinning b j q i)=value i • eigenbasisPinning b j q i) ∧
      (∀ i,value i≠a → eigenbasisPinning b j q i=b i) := by
  have hcoeff : ∃ j : Fin M, ⟪b j,q⟫ ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hz : b.repr q=0 := by
      ext i
      simpa only [OrthonormalBasis.repr_apply_apply] using hn i
    have hqzero : q=0 := b.repr.injective (by simpa only [map_zero] using hz)
    have hbad : (0 : ℝ)=1 := by simpa only [hqzero,norm_zero] using hqnorm
    exact zero_ne_one hbad
  obtain ⟨j,hj⟩ := hcoeff
  have hvalue : value j=a := Classical.byContradiction (fun hne =>
    hj (inner_eq_zero_of_eigenvalues_ne T hT _ _ _ _ (hb j) hq hne))
  exact ⟨j,hvalue,eigenbasisPinning_at b j q hqnorm,
    eigenbasisPinning_eigen T hT b value hb j q a hvalue hq,
    eigenbasisPinning_fixed T hT b value hb j q a hvalue hq⟩

end GeneralizedBulk.Graph.CanonicalSpectrum
