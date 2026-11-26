import BourgadeHuang.CMS.TriangularVolterra
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Fundamental-solution composition for the constructed finite triangular evolution. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 600000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The principal evolution in absolute time coordinates. -/
def principalOperator {R : ℝ} (lam : J → ℂ) (N : Tail R →ᵇ (J → J → ℂ))
    (H : ℕ) (t s : ℝ) : (J → ℂ) →L[ℝ] (J → ℂ) :=
  finiteMatrixOperator (triangularEvolution lam (extendTailMatrix N) H t s)

@[simp] lemma principalOperator_self {R : ℝ} (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (H : ℕ) (s : ℝ) :
    principalOperator lam N H s s = ContinuousLinearMap.id ℝ (J → ℂ) := by
  ext v i
  simp [principalOperator,finiteMatrixOperator_apply]

def triangularGenerator {R : ℝ} (lam : J → ℂ) (N : Tail R →ᵇ (J → J → ℂ))
    (t : ℝ) : (J → ℂ) →L[ℝ] (J → ℂ) :=
  finiteMatrixOperator (fun i j => (if i=j then lam i else 0)+extendTailMatrix N t i j)

@[simp] lemma triangularGenerator_apply {R : ℝ} (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (t : ℝ) (v : J → ℂ) (i : J) :
    triangularGenerator lam N t v i = lam i*v i+∑ j, extendTailMatrix N t i j*v j := by
  simp [triangularGenerator,finiteMatrixOperator_apply,add_mul,Finset.sum_add_distrib]

lemma norm_triangularGenerator_le {R : ℝ} (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (t : ℝ) :
    ‖triangularGenerator lam N t‖≤(Fintype.card J:ℝ)*(‖lam‖+‖N‖) := by
  apply norm_finiteMatrixOperator_le (add_nonneg (norm_nonneg lam) (norm_nonneg N))
  intro i j
  apply (norm_add_le _ _).trans
  apply add_le_add _ (norm_extendTailMatrix_le N t i j)
  split_ifs
  · exact norm_le_pi_norm lam i
  · simp only [norm_zero]; exact norm_nonneg lam

lemma hasDerivAt_principalOperator_apply {R : ℝ} (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (degree : J → ℕ)
    (hN : ∀ x i j, ¬ degree j<degree i → N x i j=0)
    (H : ℕ) (hH : ∀ i, degree i<H) (t s : ℝ) (v : J → ℂ) :
    HasDerivAt (fun t => principalOperator lam N H t s v)
      (triangularGenerator lam N t (principalOperator lam N H t s v)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [triangularGenerator_apply,principalOperator] using
    hasDerivAt_triangularEvolution_apply lam N degree hN H hH t s v i

lemma hasDerivAt_principalOperator {R : ℝ} (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (degree : J → ℕ)
    (hN : ∀ x i j, ¬ degree j<degree i → N x i j=0)
    (H : ℕ) (hH : ∀ i, degree i<H) (t s : ℝ) :
    HasDerivAt (fun t => principalOperator lam N H t s)
      ((triangularGenerator lam N t).comp (principalOperator lam N H t s)) t := by
  have h := HasDerivAt.sum (u:=Finset.univ) (fun i _ =>
    HasDerivAt.sum (u:=Finset.univ) (fun j _ =>
      (hasDerivAt_triangularEvolution lam (extendTailMatrix N) (continuous_extendTailMatrix N)
        degree (fun x i j hij=>hN ⟨max R x,le_max_left _ _⟩ i j hij) H hH t s i j).smul_const
        (((ContinuousLinearMap.single ℝ (fun _ : J => ℂ) i).comp
          (ContinuousLinearMap.proj j)) : (J → ℂ) →L[ℝ] (J → ℂ))))
  convert h using 1
  apply ContinuousLinearMap.ext
  intro v
  apply funext
  intro i
  change _ = finiteMatrixOperator (fun i j => lam i*triangularEvolution lam (extendTailMatrix N) H t s i j+
    ∑ k,extendTailMatrix N t i k*triangularEvolution lam (extendTailMatrix N) H t s k j) v i
  simp only [ContinuousLinearMap.comp_apply,triangularGenerator_apply,principalOperator,
    finiteMatrixOperator_apply,add_mul,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]

/-- The exact cocycle identity for the finite Duhamel evolution. -/
theorem principalOperator_comp {R : ℝ} (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (degree : J → ℕ)
    (hN : ∀ x i j, ¬ degree j<degree i → N x i j=0)
    (H : ℕ) (hH : ∀ i, degree i<H) (t r s : ℝ) :
    (principalOperator lam N H t r).comp (principalOperator lam N H r s) =
      principalOperator lam N H t s := by
  apply ContinuousLinearMap.ext
  intro v
  let K : NNReal := ⟨(Fintype.card J:ℝ)*(‖lam‖+‖N‖),
    mul_nonneg (Nat.cast_nonneg _) (add_nonneg (norm_nonneg lam) (norm_nonneg N))⟩
  have hLip : ∀ t, LipschitzOnWith K (triangularGenerator lam N t) Set.univ := by
    intro t
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,← map_sub,dist_eq_norm]
    exact (triangularGenerator lam N t).le_opNorm _ |>.trans
      (mul_le_mul_of_nonneg_right (norm_triangularGenerator_le lam N t) (norm_nonneg _))
  have heq := ODE_solution_unique_univ (t₀:=r) hLip
    (fun u => ⟨hasDerivAt_principalOperator_apply lam N degree hN H hH u r
      (principalOperator lam N H r s v), Set.mem_univ _⟩)
    (fun u => ⟨hasDerivAt_principalOperator_apply lam N degree hN H hH u s v, Set.mem_univ _⟩)
    (by simp)
  exact congrFun heq t

end BourgadeHuang.CMS
