import BourgadeHuang.CMS.ComplexVolterraOperators

/-! The actual weighted scalar primitive as a bounded complex operator. -/
noncomputable section
open MeasureTheory Set
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
variable {R : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

/-- `f ↦ -t ∫ f(t+u)/(t+u)² du`, with norm at most one. -/
def complexPrimitiveOperator (hR : 0<R) : (Tail R →ᵇ E) →L[ℂ] (Tail R →ᵇ E) :=
  (inverseSquareKernel hR (BoundedContinuousFunction.const _ (ContinuousLinearMap.id ℝ E))).complexOperator
    (norm_nonneg (BoundedContinuousFunction.const (Tail R) (ContinuousLinearMap.id ℝ E))) (by
      intro t u c v
      change (-(t.val*(tailShift t u).val⁻¹^2)) • (c • v)=
        c • ((-(t.val*(tailShift t u).val⁻¹^2)) • v)
      exact smul_comm _ _ _)

theorem norm_complexPrimitiveOperator_le (hR : 0<R) :
    ‖complexPrimitiveOperator (E:=E) hR‖≤1 := by
  have h : ‖complexPrimitiveOperator (E:=E) hR‖≤
      ‖BoundedContinuousFunction.const (Tail R) (ContinuousLinearMap.id ℝ E)‖ :=
    ContinuousIntegralKernel.norm_complexOperator_le _ _ _
  exact h.trans ((BoundedContinuousFunction.norm_const_le _).trans ContinuousLinearMap.norm_id_le)

@[simp] theorem complexPrimitiveOperator_apply (hR : 0<R) (f : Tail R →ᵇ E) (t : Tail R) :
    complexPrimitiveOperator hR f t=
      ∫u,(-(t.val*(tailShift t u).val⁻¹^2):ℝ) • f (tailShift t u)
        ∂(volume.restrict (Ioi (0:ℝ))) := rfl

end BourgadeHuang.CMS
