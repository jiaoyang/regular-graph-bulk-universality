import BourgadeHuang.CMS.TriangularEvolutionBounds

/-! The constructed triangular evolution as the continuous operator kernel of
the genuine weighted Volterra problem. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- A finite scalar matrix acting on the supremum-norm vector space. -/
def finiteMatrixOperator (A : J → J → ℂ) : (J → ℂ) →L[ℝ] (J → ℂ) :=
  ∑ i, ∑ j, A i j • ((ContinuousLinearMap.single ℝ (fun _ : J => ℂ) i).comp
    (ContinuousLinearMap.proj j))

@[simp] lemma finiteMatrixOperator_apply (A : J → J → ℂ) (v : J → ℂ) (i : J) :
    finiteMatrixOperator A v i = ∑ j, A i j * v j := by
  simp [finiteMatrixOperator,ContinuousLinearMap.sum_apply,Finset.sum_apply,
    Pi.single_apply,Finset.sum_ite_irrel]

lemma continuous_finiteMatrixOperator :
    Continuous (fun A : J → J → ℂ => finiteMatrixOperator A) := by
  apply continuous_finset_sum
  intro i hi
  apply continuous_finset_sum
  intro j hj
  exact ((continuous_apply j).comp (continuous_apply i)).smul continuous_const

lemma norm_finiteMatrixOperator_le {A : J → J → ℂ} {B : ℝ} (hB : 0≤B)
    (hA : ∀ i j, ‖A i j‖≤B) : ‖finiteMatrixOperator A‖≤(Fintype.card J:ℝ)*B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hB)
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) (norm_nonneg v))).2
  intro i
  rw [finiteMatrixOperator_apply]
  calc
    _ ≤ ∑ j, ‖A i j*v j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : J, B*‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (hA i j) (norm_le_pi_norm v j) (norm_nonneg (v j)) hB
    _ = _ := by simp [mul_assoc]

/-- Uniform coefficient extension below the initial radius, used only to make
all finite Duhamel integrands globally continuous. -/
def extendTailMatrix {R : ℝ} (N : Tail R →ᵇ (J → J → ℂ)) (t : ℝ) : J → J → ℂ :=
  N ⟨max R t,le_max_left _ _⟩

lemma continuous_extendTailMatrix {R : ℝ} (N : Tail R →ᵇ (J → J → ℂ)) (i j : J) :
    Continuous (fun t => extendTailMatrix N t i j) := by
  exact (continuous_apply j).comp ((continuous_apply i).comp
    (N.continuous.comp ((continuous_const.max continuous_id).subtype_mk _)))

lemma norm_extendTailMatrix_le {R : ℝ} (N : Tail R →ᵇ (J → J → ℂ)) (t : ℝ) (i j : J) :
    ‖extendTailMatrix N t i j‖≤‖N‖ :=
  (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans (N.norm_coe_le_norm _))

def triangularDecayConstant (a M : ℝ) (H : ℕ) : ℝ :=
  (Fintype.card J:ℝ)*(∑ n ∈ Finset.range (H+1), ((Fintype.card J:ℝ)*M*a⁻¹)^n)

lemma triangularDecayConstant_nonneg {a M : ℝ} (ha : 0<a) (hM : 0≤M) (H : ℕ) :
    0≤triangularDecayConstant (J:=J) a M H := by
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro n hn
  exact pow_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hM) (inv_nonneg.mpr ha.le)) n

/-- The actual constructed backward kernel, in the shifted coordinates used
by the tail integral operators. -/
def triangularKernel {R : ℝ} (lam : J → ℂ) (N : Tail R →ᵇ (J → J → ℂ))
    (H : ℕ) (t : Tail R) (u : ℝ) : (J → ℂ) →L[ℝ] (J → ℂ) :=
  finiteMatrixOperator (triangularEvolution lam (extendTailMatrix N) H t.val (tailShift t u).val)

lemma continuous_triangularKernel {R : ℝ} (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (H : ℕ) :
    Continuous (Function.uncurry (triangularKernel lam N H)) := by
  apply continuous_finiteMatrixOperator.comp
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_triangularEvolution lam (extendTailMatrix N)
    (continuous_extendTailMatrix N) H i j).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_tailShift))

lemma norm_triangularKernel_le {R a : ℝ} (ha : 0<a) (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (H : ℕ)
    (hlam : ∀ i, 2*a≤(lam i).re) (t : Tail R) (u : ℝ) (hu : 0<u) :
    ‖triangularKernel lam N H t u‖ ≤
      triangularDecayConstant (J:=J) a ‖N‖ H * Real.exp (-a*u) := by
  have hb : 0≤(∑ n ∈ Finset.range (H+1), ((Fintype.card J:ℝ)*‖N‖*a⁻¹)^n)*Real.exp (-a*u) := by
    apply mul_nonneg _ (Real.exp_nonneg _)
    apply Finset.sum_nonneg
    intro n hn
    exact pow_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg N))
      (inv_nonneg.mpr ha.le)) n
  have hm := norm_finiteMatrixOperator_le
    (A:=triangularEvolution lam (extendTailMatrix N) H t.val (tailShift t u).val) hb (fun i j => by
      simpa only [tailShift,max_eq_right hu.le,add_sub_cancel_left] using
        norm_triangularEvolution_le lam (extendTailMatrix N) (continuous_extendTailMatrix N)
          (R:=R) ha (norm_nonneg N) hlam (fun x _ i j=>norm_extendTailMatrix_le N x i j)
          H t.property (le_add_of_nonneg_right (le_max_left 0 u)) i j)
  simpa only [triangularKernel,triangularDecayConstant,mul_assoc] using hm

@[simp] lemma triangularKernel_zero {R : ℝ} (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (H : ℕ) (t : Tail R) :
    triangularKernel lam N H t 0 = ContinuousLinearMap.id ℝ (J → ℂ) := by
  ext v i
  simp [triangularKernel,tailShift,finiteMatrixOperator_apply]

/-- The principal evolution satisfies the actual triangular equation for
all vectors. This is the equation needed to differentiate the Volterra solution. -/
lemma hasDerivAt_triangularEvolution_apply {R : ℝ} (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (degree : J → ℕ)
    (hN : ∀ x i j, ¬ degree j<degree i → N x i j=0)
    (H : ℕ) (hH : ∀ i, degree i<H) (t s : ℝ) (v : J → ℂ) (i : J) :
    HasDerivAt (fun t => finiteMatrixOperator (triangularEvolution lam (extendTailMatrix N) H t s) v i)
      (lam i*finiteMatrixOperator (triangularEvolution lam (extendTailMatrix N) H t s) v i+
        ∑ k, extendTailMatrix N t i k *
          finiteMatrixOperator (triangularEvolution lam (extendTailMatrix N) H t s) v k) t := by
  simp only [finiteMatrixOperator_apply]
  have h := HasDerivAt.sum (u:=Finset.univ) (fun j _ =>
    (hasDerivAt_triangularEvolution lam (extendTailMatrix N) (continuous_extendTailMatrix N)
      degree (fun x i j hij=>hN ⟨max R x,le_max_left _ _⟩ i j hij) H hH t s i j).mul_const (v j))
  convert h using 1
  simp only [add_mul,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

/-- Fully constructed Volterra data: the evolution is supplied by the finite
Duhamel construction, rather than being an existence or decay assumption. -/
def triangularVolterraData {R a : ℝ} (ha : 0<a) (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (H : ℕ)
    (hlam : ∀ i, 2*a≤(lam i).re)
    (C01 : Tail R →ᵇ ((J → ℂ) →L[ℝ] ℂ))
    (C10 : Tail R →ᵇ (ℂ →L[ℝ] (J → ℂ)))
    (C11 : Tail R →ᵇ ((J → ℂ) →L[ℝ] (J → ℂ))) :
    VolterraData (E:=J → ℂ) R a (triangularDecayConstant (J:=J) a ‖N‖ H) where
  C01 := C01
  C10 := C10
  C11 := C11
  evolution := triangularKernel lam N H
  continuous_evolution := continuous_triangularKernel lam N H
  norm_evolution_le := norm_triangularKernel_le ha lam N H hlam

end BourgadeHuang.CMS
