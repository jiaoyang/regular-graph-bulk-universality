import BourgadeHuang.EdgeCMS.BoundedJetAssembly
import BourgadeHuang.CMS.SolutionSpace
import BourgadeHuang.CMS.VolterraEquation
import BourgadeHuang.EdgeCMS.HomogeneousCoefficients

/-! Actual scaled square-free jets as bounded continuous linear families.
The bounds are obtained from scalar Cauchy estimates on a dilation ball. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace BourgadeHuang.EdgeCMS
open CMS
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option linter.unusedSectionVars false

/-- Packaging a pointwise linear, continuous, bounded family does not alter its
values and preserves its linear dependence on the original function. -/
def boundedFamilyLinearMap {V T E : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace T] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : V →ₗ[ℂ] (T → E)) (hcont : ∀ v, Continuous (F v))
    (hbound : ∀ v, ∃ C : ℝ, ∀ t, ‖F v t‖ ≤ C) : V →ₗ[ℂ] (T →ᵇ E) where
  toFun v := BoundedContinuousFunction.ofNormedAddCommGroup (F v) (hcont v)
    (Classical.choose (hbound v)) (Classical.choose_spec (hbound v))
  map_add' v w := by ext t; exact congrFun (map_add F v w) t
  map_smul' c v := by ext t; exact congrFun (map_smul F c v) t

@[simp] theorem boundedFamilyLinearMap_apply {V T E : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace T] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : V →ₗ[ℂ] (T → E)) (hc : ∀ v, Continuous (F v))
    (hb : ∀ v, ∃ C : ℝ, ∀ t, ‖F v t‖ ≤ C) (v : V) (t : T) :
    boundedFamilyLinearMap F hc hb v t = F v t := rfl

section Generic
variable {V T J : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace T]
  [Fintype J] {d : ℕ} (F : V →ₗ[ℂ] (Point d → ℂ))
  (U : Set (Point d)) (hU : IsOpen U) (hF : ∀ v, AnalyticOnNhd ℂ (F v) U)
  (p : T → Point d) (weight : T → ℂ) (hp : ∀ t, p t ∈ U)
  (index : J → Finset (Fin d))

/-- The radial jets use the actual derivatives of the actual analytic family. -/
def scaledJetFunctionLinearMap : V →ₗ[ℂ] (T → J → ℂ) where
  toFun v t j := scaledSquareFree (index j) (F v) (p t) (weight t)
  map_add' v w := by
    funext t j
    simp only [map_add, Pi.add_apply, scaledSquareFree, squareFreeDerivative]
    rw [wordDerivative_add (index j).toList hU (hF v) (hF w) (hp t)]
    simp only [Pi.add_apply, mul_add]
  map_smul' c v := by
    funext t j
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, scaledSquareFree, squareFreeDerivative]
    change weight t ^ (index j).card *
      wordDerivative (index j).toList (fun z => c * F v z) (p t) =
      c * (weight t ^ (index j).card * wordDerivative (index j).toList (F v) (p t))
    rw [wordDerivative_const_mul (index j).toList c hU (hF v) (hp t)]
    ring

@[simp] theorem scaledJetFunctionLinearMap_apply (v : V) (t : T) (j : J) :
    scaledJetFunctionLinearMap F U hU hF p weight hp index v t j =
      scaledSquareFree (index j) (F v) (p t) (weight t) := rfl

theorem continuous_scaledJetFunction (hpc : Continuous p) (hwc : Continuous weight) (v : V) :
    Continuous (scaledJetFunctionLinearMap F U hU hF p weight hp index v) := by
  apply continuous_pi
  intro j
  have hs : ContinuousOn (squareFreeDerivative (index j) (F v)) U :=
    fun z hz => (analyticAt_squareFreeDerivative (index j) (hF v z hz)).continuousAt.continuousWithinAt
  exact (hwc.pow (index j).card).mul (hs.comp_continuous hpc hp)

/-- A finite family of coordinate bounds supplies the actual supremum-norm
bound required for a bounded continuous vector-valued radial map. -/
theorem scaledJetFunction_bounded
    (hb : ∀ v j, ∃ C : ℝ, ∀ t,
      ‖scaledSquareFree (index j) (F v) (p t) (weight t)‖ ≤ C) (v : V) :
    ∃ C : ℝ, ∀ t, ‖scaledJetFunctionLinearMap F U hU hF p weight hp index v t‖ ≤ C := by
  classical
  let B : J → ℝ := fun j => |Classical.choose (hb v j)|
  have hB (j : J) : 0 ≤ B j := abs_nonneg _
  refine ⟨∑ j, B j, fun t => ?_⟩
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => hB j))).2
  intro j
  exact ((Classical.choose_spec (hb v j) t).trans (le_abs_self _)).trans
    (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ j))

/-- The bounded continuous radial map; all coordinates remain genuine jets. -/
def boundedScaledJetMap (hpc : Continuous p) (hwc : Continuous weight)
    (hb : ∀ v j, ∃ C : ℝ, ∀ t,
      ‖scaledSquareFree (index j) (F v) (p t) (weight t)‖ ≤ C) :
    V →ₗ[ℂ] (T →ᵇ (J → ℂ)) :=
  boundedFamilyLinearMap (scaledJetFunctionLinearMap F U hU hF p weight hp index)
    (continuous_scaledJetFunction F U hU hF p weight hp index hpc hwc)
    (scaledJetFunction_bounded F U hU hF p weight hp index hb)

@[simp] theorem boundedScaledJetMap_apply (hpc : Continuous p) (hwc : Continuous weight)
    (hb : ∀ v j, ∃ C : ℝ, ∀ t,
      ‖scaledSquareFree (index j) (F v) (p t) (weight t)‖ ≤ C)
    (v : V) (t : T) (j : J) :
    boundedScaledJetMap F U hU hF p weight hp index hpc hwc hb v t j =
      scaledSquareFree (index j) (F v) (p t) (weight t) := rfl

end Generic

section Dilation
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}
  {J : Type*} [Fintype J] (F : V →ₗ[ℂ] (Point d → ℂ))
  (C : OpenCone d) (hF : ∀ v, AnalyticOnNhd ℂ (F v) C.carrier)
  (z : Point d) (r : ℝ) (hr : 0 < r) (hball : Metric.ball z r ⊆ C.carrier)
  (R : ℝ) (hR : 0 < R)
  (hb : ∀ v, ∃ M : ℝ, ∀ t : ℝ, R ≤ t → ∀ w ∈ Metric.ball z r,
    ‖F v ((t : ℂ) • w)‖ ≤ M)
  (index : J → Finset (Fin d))

include hF hr hball hR hb

/-- Scalar bounds on a dilation ball imply all the coordinate bounds used by
this actual bounded jet family. -/
theorem dilation_jet_bounds (v : V) (j : J) :
    ∃ M : ℝ, ∀ t : Tail R,
      ‖scaledSquareFree (index j) (F v) ((t.val : ℂ) • z) t.val‖ ≤ M := by
  obtain ⟨M, hM⟩ := hb v
  refine ⟨wordCauchyBound M r (index j).card, fun t => ?_⟩
  apply norm_scaledSquareFree_le_of_dilation_ball_bound (index j) hr t.val
  · intro w hw
    exact hF v _ (C.scale_mem (hR.trans_le t.property) (hball hw))
  · exact hM t.val t.property

/-- Linear bounded continuous maps of the genuine scaled jets along the
central ray; only scalar function bounds are required. -/
def dilationBoundedJetMap : V →ₗ[ℂ] (Tail R →ᵇ (J → ℂ)) :=
  boundedScaledJetMap F C.carrier C.isOpen hF
    (fun t : Tail R => (t.val : ℂ) • z) (fun t : Tail R => (t.val : ℂ))
    (fun t => C.scale_mem (hR.trans_le t.property) (hball (Metric.mem_ball_self hr)))
    index
    ((Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const)
    (Complex.continuous_ofReal.comp continuous_subtype_val)
    (dilation_jet_bounds F C hF z r hr hball R hR hb index)

@[simp] theorem dilationBoundedJetMap_apply (v : V) (t : Tail R) (j : J) :
    dilationBoundedJetMap F C hF z r hr hball R hR hb index v t j =
      scaledSquareFree (index j) (F v) ((t.val : ℂ) • z) t.val := rfl
end Dilation

end BourgadeHuang.EdgeCMS
