import GeneralizedBulk.Graph.EigenfamilyPinning

/-! Simultaneously insert any finite orthonormal family of eigenvectors into
an ordered real eigenbasis. Reflections fix all vectors already inserted and
all eigenspaces outside the selected eigenvalue family. -/
noncomputable section
set_option maxHeartbeats 2000000
open scoped Classical BigOperators RealInnerProductSpace

namespace GeneralizedBulk.Graph.CanonicalSpectrum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem eigenbasisPinning_fixed_orthogonal {M : ℕ}
    (b : OrthonormalBasis (Fin M) ℝ E) (j : Fin M) (q : E) (i : Fin M)
    (hij : i ≠ j) (horth : ⟪b i,q⟫ = 0) : eigenbasisPinning b j q i = b i := by
  change (ℝ ∙ (b j-q))ᗮ.reflection (b i) = b i
  apply Submodule.reflection_mem_subspace_eq_self
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left,inner_sub_right,
    b.inner_eq_zero hij,horth,sub_self]

theorem exists_eigenvalue_coefficient {M : ℕ}
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis (Fin M) ℝ E) (value : Fin M → ℝ)
    (hb : ∀ i,T (b i)=value i • b i)
    (q : E) (a : ℝ) (hqnorm : ‖q‖=1) (hq : T q=a • q) :
    ∃ j : Fin M,value j=a ∧ ⟪b j,q⟫ ≠ 0 := by
  have hcoeff : ∃ j : Fin M,⟪b j,q⟫ ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hz : b.repr q=0 := by
      ext i
      simpa only [OrthonormalBasis.repr_apply_apply] using hn i
    have hqzero : q=0 := b.repr.injective (by simpa only [map_zero] using hz)
    have hbad : (0 : ℝ)=1 := by simpa only [hqzero,norm_zero] using hqnorm
    exact zero_ne_one hbad
  obtain ⟨j,hj⟩ := hcoeff
  refine ⟨j,?_,hj⟩
  have he := hT (b j) q
  rw [hb,hq,real_inner_smul_left,real_inner_smul_right] at he
  exact (mul_eq_mul_right_iff.mp he).resolve_right hj

/-- Extend an arbitrary finite orthonormal eigenfamily without changing the
ordered list of eigenvalues, and preserve every unselected eigenspace. -/
theorem exists_eigenbasis_pinning_family {M k : ℕ}
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis (Fin M) ℝ E) (value : Fin M → ℝ)
    (hb : ∀ i,T (b i)=value i • b i)
    (q : Fin k → E) (a : Fin k → ℝ) (ho : Orthonormal ℝ q)
    (he : ∀ r,T (q r)=a r • q r) :
    ∃ B : OrthonormalBasis (Fin M) ℝ E,∃ f : Fin k → Fin M,
      Function.Injective f ∧ (∀ r,value (f r)=a r) ∧ (∀ r,B (f r)=q r) ∧
      (∀ i,T (B i)=value i • B i) ∧
      (∀ i,(∀ r,value i≠a r) → B i=b i) := by
  induction k with
  | zero =>
    refine ⟨b,Fin.elim0,?_,?_,?_,hb,?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i _; rfl
  | succ k ih =>
    let qold : Fin k → E := fun r => q r.castSucc
    let aold : Fin k → ℝ := fun r => a r.castSucc
    have hold : Orthonormal ℝ qold := ho.comp _ (Fin.castSucc_injective k)
    obtain ⟨B,f,hfi,hval,hcontains,hB,hfixed⟩ := ih qold aold hold (fun r => he r.castSucc)
    let qnew := q (Fin.last k)
    let anew := a (Fin.last k)
    obtain ⟨j,hj,hcoeff⟩ := exists_eigenvalue_coefficient T hT B value hB
      qnew anew (ho.1 _) (he _)
    let B' := eigenbasisPinning B j qnew
    let f' : Fin (k+1) → Fin M := Fin.lastCases j f
    have hor (r : Fin k) : ⟪B (f r),qnew⟫ = 0 := by
      rw [hcontains]
      exact ho.inner_eq_zero (Fin.castSucc_ne_last r)
    have hne (r : Fin k) : f r ≠ j := by
      intro h
      apply hcoeff
      rw [←h]
      exact hor r
    have hcont' (r : Fin (k+1)) : B' (f' r)=q r := by
      refine Fin.lastCases ?_ (fun s => ?_) r
      · simpa only [f',Fin.lastCases_last] using eigenbasisPinning_at B j qnew (ho.1 _)
      · simp only [f',Fin.lastCases_castSucc]
        change eigenbasisPinning B j qnew (f s)=q s.castSucc
        rw [eigenbasisPinning_fixed_orthogonal B j qnew (f s) (hne s) (hor s)]
        exact hcontains s
    refine ⟨B',f',?_,?_,hcont',?_,?_⟩
    · intro r s hrs
      apply ho.linearIndependent.injective
      rw [←hcont' r,←hcont' s,hrs]
    · intro r
      refine Fin.lastCases ?_ (fun s => ?_) r
      · simpa only [f',Fin.lastCases_last] using hj
      · simpa only [f',Fin.lastCases_castSucc] using hval s
    · exact eigenbasisPinning_eigen T hT B value hB j qnew anew hj (he _)
    · intro i hi
      change eigenbasisPinning B j qnew i=b i
      rw [eigenbasisPinning_fixed T hT B value hB j qnew anew hj (he _) i (hi _)]
      exact hfixed i (fun r => hi r.castSucc)

end GeneralizedBulk.Graph.CanonicalSpectrum
