import BourgadeHuang.CMS.TriangularAffineFixedPoint

/-! Analytic solution of the coupled weighted Volterra equation after exact
triangular elimination. All operators are the integral and coefficient
operators constructed in the preceding modules. -/
noncomputable section
open Filter
open scoped Topology
namespace BourgadeHuang.CMS
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {P E F G : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem analyticAt_clm_comp {A : P → F →L[ℂ] G} {B : P → E →L[ℂ] F} {x : P}
    (hA : AnalyticAt ℂ A x) (hB : AnalyticAt ℂ B x) :
    AnalyticAt ℂ (fun y => (A y).comp (B y)) x :=
  ((ContinuousLinearMap.compL ℂ E F G).analyticAt_bilinear _).comp₂ hA hB

theorem analyticAt_clm_apply {A : P → E →L[ℂ] F} {b : P → E} {x : P}
    (hA : AnalyticAt ℂ A x) (hb : AnalyticAt ℂ b x) :
    AnalyticAt ℂ (fun y => A y (b y)) x :=
  ((ContinuousLinearMap.id ℂ (E →L[ℂ] F)).analyticAt_bilinear _).comp₂ hA hb

section Coupled
variable [CompleteSpace E]
  (Q P₀ : E →L[ℂ] E) (K : F →L[ℂ] F)

/-- The reciprocal remainder after eliminating the empty component. -/
def coupledVolterraRemainder (C01 : E →L[ℂ] F) (C10 : F →L[ℂ] E)
    (C11 : E →L[ℂ] E) : E →L[ℂ] E :=
  P₀.comp ((C10.comp K).comp C01+C11)

/-- The actual finite-inverse formula for the weighted nonempty component. -/
def coupledVolterraSolution (N : E →L[ℂ] E) (C01 : E →L[ℂ] F)
    (C10 : F →L[ℂ] E) (C11 : E →L[ℂ] E) (e : F) (H : ℕ) : E :=
  triangularAffineFixedPoint (Q.comp N) (coupledVolterraRemainder P₀ K C01 C10 C11)
    (Q (C10 e)) H

theorem coupledVolterraSolution_equation
    (N : E →L[ℂ] E) (C01 : E →L[ℂ] F) (C10 : F →L[ℂ] E)
    (C11 : E →L[ℂ] E) (e : F) (H : ℕ)
    (hN : (Q.comp N)^H=0)
    (hsmall : ‖triangularInverse (Q.comp N) H*
      coupledVolterraRemainder P₀ K C01 C10 C11‖<1) :
    let Z := coupledVolterraSolution Q P₀ K N C01 C10 C11 e H
    Z=Q (N Z+C10 e)+P₀ (C10 (K (C01 Z))+C11 Z) := by
  dsimp only
  have hh := triangularAffineFixedPoint_equation hN hsmall (Q (C10 e))
  simpa only [coupledVolterraSolution,coupledVolterraRemainder,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,map_add,add_comm,add_left_comm,add_assoc] using hh.symm

theorem analyticAt_coupledVolterraSolution
    {N : P → E →L[ℂ] E} {C01 : P → E →L[ℂ] F}
    {C10 : P → F →L[ℂ] E} {C11 : P → E →L[ℂ] E} {x : P}
    (hN : AnalyticAt ℂ N x) (h01 : AnalyticAt ℂ C01 x)
    (h10 : AnalyticAt ℂ C10 x) (h11 : AnalyticAt ℂ C11 x)
    (e : F) (H : ℕ)
    (hsmall : ‖triangularInverse (Q.comp (N x)) H*
      coupledVolterraRemainder P₀ K (C01 x) (C10 x) (C11 x)‖<1) :
    AnalyticAt ℂ (fun y => coupledVolterraSolution Q P₀ K
      (N y) (C01 y) (C10 y) (C11 y) e H) x := by
  have hB : AnalyticAt ℂ (fun y => Q.comp (N y)) x :=
    analyticAt_clm_comp (analyticAt_const (v:=Q)) hN
  have hK : AnalyticAt ℂ (fun y => (C10 y).comp K) x :=
    analyticAt_clm_comp h10 (analyticAt_const (v:=K))
  have hC : AnalyticAt ℂ (fun y => ((C10 y).comp K).comp (C01 y)+C11 y) x :=
    (analyticAt_clm_comp hK h01).add h11
  have hA : AnalyticAt ℂ (fun y => coupledVolterraRemainder P₀ K (C01 y) (C10 y) (C11 y)) x :=
    analyticAt_clm_comp (analyticAt_const (v:=P₀)) hC
  have he : AnalyticAt ℂ (fun y => C10 y e) x :=
    analyticAt_clm_apply h10 (analyticAt_const (v:=e))
  have hb : AnalyticAt ℂ (fun y => Q (C10 y e)) x :=
    analyticAt_clm_apply (analyticAt_const (v:=Q)) he
  exact analyticAt_triangularAffineFixedPoint H hB hA hb hsmall

theorem coupledVolterraSolution_unique
    (N : E →L[ℂ] E) (C01 : E →L[ℂ] F) (C10 : F →L[ℂ] E)
    (C11 : E →L[ℂ] E) (e : F) (H : ℕ)
    (hN : (Q.comp N)^H=0)
    (hsmall : ‖triangularInverse (Q.comp N) H*
      coupledVolterraRemainder P₀ K C01 C10 C11‖<1) (Z : E)
    (hZ : Z=Q (N Z+C10 e)+P₀ (C10 (K (C01 Z))+C11 Z)) :
    Z=coupledVolterraSolution Q P₀ K N C01 C10 C11 e H := by
  apply triangularAffineFixedPoint_unique hN hsmall
  simpa only [coupledVolterraRemainder,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,map_add,add_comm,add_left_comm,add_assoc] using hZ.symm

end Coupled
end BourgadeHuang.CMS
