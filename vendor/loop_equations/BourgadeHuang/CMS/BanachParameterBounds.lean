import BourgadeHuang.CMS.AnalyticNormalizedRadial

/-! Parameter differentiation of bounded continuous radial families. The
estimates are uniform along the whole radial tail, directly from the Banach
norm of the genuine Fréchet derivative. -/
noncomputable section
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
section Evaluation
variable {E V X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace X]
  {F : E → (X →ᵇ V)} {z : E}

theorem hasFDerivAt_bounded_eval (hF : DifferentiableAt ℂ F z) (t : X) :
    HasFDerivAt (fun w=>F w t)
      ((BoundedContinuousFunction.evalCLM (𝕜:=ℂ) t).comp (fderiv ℂ F z)) z :=
  (BoundedContinuousFunction.evalCLM (𝕜:=ℂ) t : (X →ᵇ V) →L[ℂ] V).hasFDerivAt.comp z hF.hasFDerivAt

theorem fderiv_bounded_eval (hF : DifferentiableAt ℂ F z) (t : X) (v : E) :
    fderiv ℂ (fun w=>F w t) z v=(fderiv ℂ F z v) t := by
  rw [(hasFDerivAt_bounded_eval hF t).fderiv]
  rfl

theorem norm_fderiv_bounded_eval_le (hF : DifferentiableAt ℂ F z) (t : X) (v : E) :
    ‖fderiv ℂ (fun w=>F w t) z v‖≤‖fderiv ℂ F z‖*‖v‖ := by
  rw [fderiv_bounded_eval hF]
  exact ((fderiv ℂ F z v).norm_coe_le_norm t).trans ((fderiv ℂ F z).le_opNorm v)
end Evaluation

section Unweight
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [CompleteSpace V]
  {R : ℝ} (hR : 0<R) {F : E → (Tail R →ᵇ V)} {z : E}

theorem hasFDerivAt_unweighted_bounded_eval (hF : DifferentiableAt ℂ F z) (t : Tail R) :
    HasFDerivAt (fun w=>boundedUnweight hR (F w) t)
      ((BoundedContinuousFunction.evalCLM (𝕜:=ℂ) t).comp
        ((complexUnweightOperator (E:=V) hR).comp (fderiv ℂ F z))) z :=
  (BoundedContinuousFunction.evalCLM (𝕜:=ℂ) t : (Tail R →ᵇ V) →L[ℂ] V).hasFDerivAt.comp z
    ((complexUnweightOperator (E:=V) hR).hasFDerivAt.comp z hF.hasFDerivAt)

theorem norm_fderiv_unweighted_bounded_eval_le (hF : DifferentiableAt ℂ F z)
    (t : Tail R) (v : E) :
    ‖fderiv ℂ (fun w=>boundedUnweight hR (F w) t) z v‖≤
      (‖fderiv ℂ F z‖*‖v‖)/t.val := by
  rw [(hasFDerivAt_unweighted_bounded_eval hR hF t).fderiv]
  change ‖boundedUnweight hR (fderiv ℂ F z v) t‖≤_
  exact (norm_unweight_le hR _ t).trans
    (div_le_div_of_nonneg_right ((fderiv ℂ F z).le_opNorm v) (hR.trans_le t.property).le)
end Unweight
/-- Component coordinate differentiation is evaluation of the genuine
vector-valued Fréchet derivative in the corresponding basis direction. -/
theorem coordDeriv_component_eq_fderiv {d : ℕ} {ι : Type*} [Fintype ι]
    {F : Point d → ι → ℂ} {z : Point d} (hF : DifferentiableAt ℂ F z)
    (i : Fin d) (k : ι) :
    coordDeriv i (fun w=>F w k) z=(fderiv ℂ F z (Pi.single i 1)) k := by
  have hd := (ContinuousLinearMap.proj (R:=ℂ) k : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp z hF.hasFDerivAt
  change HasFDerivAt (fun w=>F w k) ((ContinuousLinearMap.proj (R:=ℂ) k).comp (fderiv ℂ F z)) z at hd
  rw [coordDeriv_eq_fderiv hd.differentiableAt,hd.fderiv]
  rfl

end BourgadeHuang.CMS
