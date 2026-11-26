import BourgadeHuang.CMS.Volterra
import BourgadeHuang.CMS.AnalyticAffineFixedPoint

/-! Complex-linear versions of the actual bounded integral and coefficient
operators, preserving their verified integral formulas and norm estimates. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS

namespace ContinuousIntegralKernel
variable {X E F : Type*} [TopologicalSpace X] [FirstCountableTopology X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
  {μ : Measure ℝ} {B : ℝ}

/-- The genuine Bochner integral operator is complex-linear whenever every
kernel operator is complex-linear. -/
def complexOperator (K : ContinuousIntegralKernel (X:=X) (E:=E) (F:=F) μ B) (hB : 0≤B)
    (hK : ∀x u (c : ℂ) v,K.kernel x u (c • v)=c • K.kernel x u v) :
    (X →ᵇ E) →L[ℂ] (X →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := K.operator hB
      map_add' := map_add (K.operator hB)
      map_smul' := by
        intro c f
        ext x
        simp only [operator_apply,BoundedContinuousFunction.smul_apply,hK]
        exact integral_smul c _ }
    B (fun f => ((K.operator hB).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (K.norm_operator_le hB) (norm_nonneg f)))

@[simp] theorem complexOperator_apply
    (K : ContinuousIntegralKernel (X:=X) (E:=E) (F:=F) μ B) (hB : 0≤B)
    (hK : ∀x u (c : ℂ) v,K.kernel x u (c • v)=c • K.kernel x u v)
    (f : X →ᵇ E) (x : X) :
    K.complexOperator hB hK f x=∫u,K.kernel x u (f (K.shift x u))∂μ := rfl

theorem norm_complexOperator_le
    (K : ContinuousIntegralKernel (X:=X) (E:=E) (F:=F) μ B) (hB : 0≤B)
    (hK : ∀x u (c : ℂ) v,K.kernel x u (c • v)=c • K.kernel x u v) :
    ‖K.complexOperator hB hK‖≤B := LinearMap.mkContinuous_norm_le _ hB _

end ContinuousIntegralKernel

section Coefficients
variable {X E F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Pointwise multiplication by an actual complex-linear operator coefficient. -/
def complexBoundedCoefficientOperator (A : X →ᵇ (E →L[ℂ] F)) :
    (X →ᵇ E) →L[ℂ] (X →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := fun f => BoundedContinuousFunction.ofNormedAddCommGroup
        (fun x => A x (f x)) (A.continuous.clm_apply f.continuous) (‖A‖*‖f‖)
        (fun x => (A x).le_opNorm _ |>.trans
          (mul_le_mul (A.norm_coe_le_norm x) (f.norm_coe_le_norm x)
            (norm_nonneg (f x)) (norm_nonneg A)))
      map_add' := by intro f g; ext x; exact map_add (A x) (f x) (g x)
      map_smul' := by intro c f; ext x; exact map_smul (A x) c (f x) }
    ‖A‖ (fun f => (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg A) (norm_nonneg f))).mpr
      (fun x => (A x).le_opNorm _ |>.trans
        (mul_le_mul (A.norm_coe_le_norm x) (f.norm_coe_le_norm x) (norm_nonneg (f x)) (norm_nonneg A))))

@[simp] theorem complexBoundedCoefficientOperator_apply (A : X →ᵇ (E →L[ℂ] F))
    (f : X →ᵇ E) (x : X) : complexBoundedCoefficientOperator A f x=A x (f x) := rfl

theorem norm_complexBoundedCoefficientOperator_le (A : X →ᵇ (E →L[ℂ] F)) :
    ‖complexBoundedCoefficientOperator A‖≤‖A‖ := LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

set_option synthInstance.maxHeartbeats 100000 in
/-- Dependence on the coefficient is itself a bounded complex-linear map. -/
def complexCoefficientAction :
    (X →ᵇ (E →L[ℂ] F)) →L[ℂ] ((X →ᵇ E) →L[ℂ] (X →ᵇ F)) := by
  let L : (X →ᵇ (E →L[ℂ] F)) →ₗ[ℂ] ((X →ᵇ E) →L[ℂ] (X →ᵇ F)) :=
    { toFun := fun A => complexBoundedCoefficientOperator A
      map_add' := by intro A B; ext f x; exact ContinuousLinearMap.add_apply (A x) (B x) (f x)
      map_smul' := by intro c A; ext f x; rfl }
  exact L.mkContinuous 1 (fun A : X →ᵇ (E →L[ℂ] F) => by
    change ‖complexBoundedCoefficientOperator A‖≤1*‖A‖
    simpa only [one_mul] using norm_complexBoundedCoefficientOperator_le (X := X) (E := E) (F := F) A)

theorem analyticAt_complexBoundedCoefficientOperator
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {A : P → (X →ᵇ (E →L[ℂ] F))} {p : P} (hA : AnalyticAt ℂ A p) :
    AnalyticAt ℂ (fun q => complexBoundedCoefficientOperator (A q)) p := by
  exact ((complexCoefficientAction (X := X) (E := E) (F := F)).analyticAt _).comp (f := A) hA

end Coefficients
end BourgadeHuang.CMS
