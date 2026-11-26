import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Integral operators on bounded continuous functions, used for the weighted
Volterra construction in Bourgade--Huang, §7.3.  The operator is the actual
Bochner integral; continuity and its norm bound follow from the kernel bounds. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
set_option linter.unusedSectionVars false
namespace BourgadeHuang.CMS

variable {X E F : Type*} [TopologicalSpace X] [FirstCountableTopology X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A continuous integral kernel with a uniformly bounded integral majorant
and a local integrable majorant.  The transport permits shifted tail integrals. -/
structure ContinuousIntegralKernel (μ : Measure ℝ) (B : ℝ) where
  kernel : X → ℝ → E →L[ℝ] F
  shift : X → ℝ → X
  continuous_kernel : Continuous (Function.uncurry kernel)
  continuous_shift : Continuous (Function.uncurry shift)
  bound : X → ℝ → ℝ
  integrable_bound : ∀ x, Integrable (bound x) μ
  norm_le_bound : ∀ x, ∀ᵐ s ∂μ, ‖kernel x s‖ ≤ bound x s
  integral_bound_le : ∀ x, (∫ s, bound x s ∂μ) ≤ B
  locally_dominated : ∀ x, ∃ g : ℝ → ℝ, Integrable g μ ∧
    ∀ᶠ y in 𝓝 x, ∀ᵐ s ∂μ, ‖kernel y s‖ ≤ g s

namespace ContinuousIntegralKernel
variable {μ : Measure ℝ} {B : ℝ} (K : ContinuousIntegralKernel (X:=X) (E:=E) (F:=F) μ B)

def integrand (f : X →ᵇ E) (x : X) (s : ℝ) : F :=
  K.kernel x s (f (K.shift x s))

lemma continuous_integrand (f : X →ᵇ E) :
    Continuous (Function.uncurry (K.integrand f)) := by
  exact K.continuous_kernel.clm_apply (f.continuous.comp K.continuous_shift)

lemma norm_integrand_le (f : X →ᵇ E) (x : X) :
    ∀ᵐ s ∂μ, ‖K.integrand f x s‖ ≤ K.bound x s * ‖f‖ := by
  filter_upwards [K.norm_le_bound x] with s hs
  exact (K.kernel x s).le_opNorm _ |>.trans
    (mul_le_mul hs (f.norm_coe_le_norm _) (norm_nonneg _) (le_trans (norm_nonneg _) hs))

lemma integrable_integrand (f : X →ᵇ E) (x : X) :
    Integrable (K.integrand f x) μ := by
  apply ((K.integrable_bound x).mul_const ‖f‖).mono'
  · exact ((K.continuous_integrand f).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact K.norm_integrand_le f x

lemma norm_integral_le (f : X →ᵇ E) (x : X) :
    ‖∫ s, K.integrand f x s ∂μ‖ ≤ B * ‖f‖ := by
  calc
    _ ≤ ∫ s, K.bound x s * ‖f‖ ∂μ :=
      norm_integral_le_of_norm_le ((K.integrable_bound x).mul_const ‖f‖) (K.norm_integrand_le f x)
    _ = (∫ s, K.bound x s ∂μ) * ‖f‖ := integral_mul_const _ _
    _ ≤ B * ‖f‖ := mul_le_mul_of_nonneg_right (K.integral_bound_le x) (norm_nonneg _)

lemma continuous_integral (f : X →ᵇ E) :
    Continuous (fun x => ∫ s, K.integrand f x s ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨g,hg,hdom⟩ := K.locally_dominated x
  apply continuousAt_of_dominated (bound:=fun s=>g s * ‖f‖)
  · exact Filter.Eventually.of_forall (fun y=>(K.integrable_integrand f y).aestronglyMeasurable)
  · filter_upwards [hdom] with y hy
    filter_upwards [hy] with s hs
    exact (K.kernel y s).le_opNorm _ |>.trans
      (mul_le_mul hs (f.norm_coe_le_norm _) (norm_nonneg _) (le_trans (norm_nonneg _) hs))
  · exact hg.mul_const _
  · exact Filter.Eventually.of_forall (fun s =>
      ((K.continuous_integrand f).comp (continuous_id.prodMk continuous_const)).continuousAt)

/-- The genuine integral operator with its supremum norm control. -/
def operator (hB : 0≤B) : (X →ᵇ E) →L[ℝ] (X →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := fun f => BoundedContinuousFunction.ofNormedAddCommGroup
        (fun x => ∫ s, K.integrand f x s ∂μ) (K.continuous_integral f)
        (B*‖f‖) (K.norm_integral_le f)
      map_add' := by
        intro f g
        ext x
        change (∫ s, K.integrand (f+g) x s ∂μ) = _
        simpa only [integrand, BoundedContinuousFunction.coe_add, Pi.add_apply,
          map_add] using
          integral_add (K.integrable_integrand f x) (K.integrable_integrand g x)
      map_smul' := by
        intro c f
        ext x
        simpa only [integrand, BoundedContinuousFunction.coe_smul, Pi.smul_apply,
          map_smul] using integral_smul c (K.integrand f x) }
    B (fun f => (BoundedContinuousFunction.norm_le (mul_nonneg hB (norm_nonneg f))).2
      (K.norm_integral_le f))

@[simp] lemma operator_apply (hB : 0≤B) (f : X →ᵇ E) (x : X) :
    K.operator hB f x = ∫ s, K.kernel x s (f (K.shift x s)) ∂μ := rfl

lemma norm_operator_le (hB : 0≤B) : ‖K.operator hB‖ ≤ B :=
  LinearMap.mkContinuous_norm_le _ hB _

end ContinuousIntegralKernel
end BourgadeHuang.CMS
