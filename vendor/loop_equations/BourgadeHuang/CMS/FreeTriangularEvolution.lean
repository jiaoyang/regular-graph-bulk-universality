import BourgadeHuang.CMS.TriangularTail
import BourgadeHuang.CMS.FreeDiagonalVolterra

/-! Identification of the constructed finite Duhamel evolution with the free
diagonal exponential when the triangular coefficient vanishes. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction BigOperators
namespace BourgadeHuang.CMS
variable {J : Type*} [Fintype J] [DecidableEq J]

@[simp] theorem triangularTerm_zero_successor (lam : J → ℂ) (n : ℕ)
    (t s : ℝ) (i j : J) : triangularTerm lam 0 (n+1) t s i j=0 := by
  simp [triangularTerm,backwardIntegral]

@[simp] theorem triangularEvolution_zero (lam : J → ℂ) (H : ℕ)
    (t s : ℝ) (i j : J) :
    triangularEvolution lam 0 H t s i j=
      if i=j then Complex.exp (lam i*((t-s:ℝ):ℂ)) else 0 := by
  unfold triangularEvolution
  rw [Finset.sum_range_succ']
  simp [triangularTerm,backwardIntegral]

@[simp] theorem principalOperator_zero {R : ℝ} (lam : J → ℂ) (H : ℕ) (t s : ℝ) :
    principalOperator lam (0 : Tail R →ᵇ (J → J → ℂ)) H t s=
      (freeDiagonalEvolution lam (s-t)).restrictScalars ℝ := by
  have he : extendTailMatrix (0 : Tail R →ᵇ (J → J → ℂ))=0 := rfl
  ext v i
  simp only [principalOperator,he,finiteMatrixOperator_apply,triangularEvolution_zero,
    freeDiagonalEvolution,complexDiagonalOperator_apply]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  congr 2
  simp only [Complex.ofReal_sub]
  ring

@[simp] theorem triangularGenerator_zero {R : ℝ} (lam : J → ℂ) (t : ℝ) :
    triangularGenerator lam (0 : Tail R →ᵇ (J → J → ℂ)) t=
      (complexDiagonalOperator lam).restrictScalars ℝ := by
  ext v i
  simp [triangularGenerator_apply,extendTailMatrix,complexDiagonalOperator_apply]

/-- The genuine free backward tail, in absolute coordinates. -/
def freeBackwardTail (lam : J → ℂ) (f : ℝ → (J → ℂ)) (t : ℝ) : J → ℂ :=
  -(∫s in Ioi t,freeDiagonalEvolution lam (s-t) (f s))

theorem backwardTail_zero_eq_free {R a : ℝ} (ha : 0<a) (lam : J → ℂ)
    (hlam : ∀i,a≤(lam i).re) (f : ℝ →ᵇ (J → ℂ)) {t : ℝ} (ht : R≤t) :
    backwardTail (principalOperator lam (0 : Tail R →ᵇ (J → J → ℂ)) 1) R f t=
      freeBackwardTail lam f t := by
  have hlam' : ∀i,2*(a/2)≤(lam i).re := by intro i; linarith [hlam i]
  rw [backwardTail_eq_integral _ _ _
    (principalOperator_comp lam 0 (fun _ => 0) (by intros; rfl) 1 (by intro i; change 0<1; omega))
    (integrable_principalOperator_tail (half_pos ha) lam 0 1 hlam' f) ht]
  simp only [principalOperator_zero,freeBackwardTail]
  rfl

/-- The free convolution solves the actual inhomogeneous diagonal ODE. -/
theorem hasDerivAt_freeBackwardTail {a : ℝ} (ha : 0<a) (lam : J → ℂ)
    (hlam : ∀i,a≤(lam i).re) (f : ℝ →ᵇ (J → ℂ)) (t : ℝ) :
    HasDerivAt (freeBackwardTail lam f)
      (complexDiagonalOperator lam (freeBackwardTail lam f t)+f t) t := by
  let R := t-1
  have hlam' : ∀i,2*(a/2)≤(lam i).re := by intro i; linarith [hlam i]
  have ht : R<t := by dsimp [R]; linarith
  have hd := hasDerivAt_triangularBackwardTail (R:=R) (half_pos ha) lam
    (0 : Tail R →ᵇ (J → J → ℂ)) (fun _ => 0) (by intros; rfl) 1
    (by intro i; change 0<1; omega) hlam' f ht
  rw [triangularGenerator_zero,backwardTail_zero_eq_free ha lam hlam f ht.le] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with s hs
  exact (backwardTail_zero_eq_free ha lam hlam f hs.le).symm

end BourgadeHuang.CMS
