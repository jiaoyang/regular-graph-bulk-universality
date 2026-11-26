import BourgadeHuang.CMS.AnalyticRadialVolterraSolution
import BourgadeHuang.CMS.CoupledVolterraODE

/-! A holomorphic family of genuine normalized solutions of the actual CMS
radial system. Both differential equations and normalization are consequences
of the constructed improper integrals. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace RadialOperatorFamily
variable {d : ℕ} {R a : ℝ} (F : RadialOperatorFamily d R)
  (hR : 0<R) (ha : 0<a) (lam : NonemptySubset d → ℂ) (hlam : ∀i,a≤(lam i).re)

def normalizedNonempty (w : Point d) : RadialBanach d R :=
  boundedUnweight hR (F.weightedSolution hR ha lam hlam w)

def normalizedEmpty (w : Point d) : EmptyBanach R :=
  coupledEmptyComponent hR (F.C01 w) (1:EmptyVector) (F.weightedSolution hR ha lam hlam w)

theorem analyticAt_normalizedNonempty {z : Point d} (hF : F.AnalyticAt z)
    (hsmall : ‖F.effectiveOperator hR ha lam hlam z‖<1) :
    _root_.AnalyticAt ℂ (F.normalizedNonempty hR ha lam hlam) z := by
  have hu : _root_.AnalyticAt ℂ (fun w => complexUnweightOperator (E:=RadialVector d) hR) z := analyticAt_const
  exact analyticAt_clm_apply hu (F.analyticAt_weightedSolution hR ha lam hlam hF hsmall)

theorem analyticAt_normalizedEmpty {z : Point d} (hF : F.AnalyticAt z)
    (hsmall : ‖F.effectiveOperator hR ha lam hlam z‖<1) :
    _root_.AnalyticAt ℂ (F.normalizedEmpty hR ha lam hlam) z := by
  have hZ := F.analyticAt_weightedSolution hR ha lam hlam hF hsmall
  have h01 := analyticAt_complexBoundedCoefficientOperator hF.2.1
  have hc : _root_.AnalyticAt ℂ (fun w => F.c01Op w (F.weightedSolution hR ha lam hlam w)) z :=
    analyticAt_clm_apply h01 hZ
  have hp : _root_.AnalyticAt ℂ (fun w => complexPrimitiveOperator (E:=EmptyVector) hR
      (F.c01Op w (F.weightedSolution hR ha lam hlam w))) z :=
    analyticAt_clm_apply analyticAt_const hc
  have hu : _root_.AnalyticAt ℂ (fun w => complexUnweightOperator (E:=EmptyVector) hR
      (complexPrimitiveOperator hR (F.c01Op w (F.weightedSolution hR ha lam hlam w)))) z :=
    analyticAt_clm_apply analyticAt_const hp
  exact (analyticAt_const (v:=BoundedContinuousFunction.const (Tail R) (1:EmptyVector))).add hu

/-- Holomorphy of the actual scalar normalized germ at the start of the ray. -/
theorem analyticAt_normalizedGerm {z : Point d} (hF : F.AnalyticAt z)
    (hsmall : ‖F.effectiveOperator hR ha lam hlam z‖<1) :
    _root_.AnalyticAt ℂ (fun w => F.normalizedEmpty hR ha lam hlam w ⟨R,le_rfl⟩ ()) z := by
  let L : EmptyBanach R →L[ℂ] ℂ := (ContinuousLinearMap.proj (R:=ℂ) () : EmptyVector →L[ℂ] ℂ).comp
    (BoundedContinuousFunction.evalCLM (𝕜:=ℂ) (⟨R,le_rfl⟩ : Tail R))
  have hL : _root_.AnalyticAt ℂ L (F.normalizedEmpty hR ha lam hlam z) := L.analyticAt _
  exact hL.comp (f:=F.normalizedEmpty hR ha lam hlam)
    (F.analyticAt_normalizedEmpty hR ha lam hlam hF hsmall)

theorem normalized_components_limits (w : Point d) :
    Tendsto (F.normalizedEmpty hR ha lam hlam w) atTop (𝓝 (1:EmptyVector)) ∧
      Tendsto (F.normalizedNonempty hR ha lam hlam w) atTop (𝓝 0) :=
  ⟨coupledEmptyComponent_normalization hR (F.C01 w) _ _,tendsto_unweight_zero hR _⟩

theorem normalized_components_bound (w : Point d) :
    ∃B : ℝ,0≤B ∧ ∀t : Tail R,
      ‖F.normalizedEmpty hR ha lam hlam w t-1‖≤B/t.val ∧
      ‖F.normalizedNonempty hR ha lam hlam w t‖≤B/t.val :=
  coupledComponents_reciprocal_bound hR (F.C01 w) _ _

/-- Genuine ODEs for the two normalized blocks of the constructed family. -/
theorem normalized_components_derivatives (D : SectorialData d) (ω : Point d) (σ : Fin d → Sign)
    {w : Point d} (hF : F.Matches D ω σ w)
    (hsmall : ‖F.effectiveOperator hR ha lam hlam w‖<1)
    (t : Tail R) (ht : R<t.val) :
    HasDerivAt (tailExtension (F.normalizedEmpty hR ha lam hlam w))
      (t.val⁻¹ • F.C01 w t (F.normalizedNonempty hR ha lam hlam w t)) t.val ∧
    HasDerivAt (tailExtension (F.normalizedNonempty hR ha lam hlam w))
      (complexDiagonalOperator lam (F.normalizedNonempty hR ha lam hlam w t)+
        F.N w t (F.normalizedNonempty hR ha lam hlam w t)+t.val⁻¹ •
          (F.C10 w t (F.normalizedEmpty hR ha lam hlam w t)+
            F.C11 w t (F.normalizedNonempty hR ha lam hlam w t))) t.val := by
  constructor
  · exact hasDerivAt_coupledEmptyComponent hR (F.C01 w) _ _ t ht
  · exact hasDerivAt_coupledNonemptyComponent hR (F.N w) (F.C01 w) (F.C10 w) (F.C11 w)
      ha lam hlam _ _ (F.weightedSolution_equation D ω σ hR ha lam hlam hF hsmall) t ht

/-- The block equations are exactly the rational CMS radial equations,
expressed in the actual subset-indexed components. -/
theorem normalized_component_equations (D : SectorialData d) (ω : Point d) (σ : Fin d → Sign)
    {w : Point d} (hF : F.Matches D ω σ w)
    (hsmall : ‖F.effectiveOperator hR ha lam hlam w‖<1)
    (t : Tail R) (ht : R<t.val) :
    HasDerivAt (fun s => tailExtension (F.normalizedEmpty hR ha lam hlam w) s ())
      ((t.val⁻¹:ℝ) • ∑T : NonemptySubset d,
        D.radialRemainder ω (sectorialRay σ w R t) (t:ℝ) ∅ T.val*
          F.normalizedNonempty hR ha lam hlam w t T) t.val ∧
    ∀S : NonemptySubset d,
      HasDerivAt (fun s => tailExtension (F.normalizedNonempty hR ha lam hlam w) s S)
        (lam S*F.normalizedNonempty hR ha lam hlam w t S+
          (∑T : NonemptySubset d,D.principalRemainder ω (sectorialRay σ w R t) (t:ℝ) S.val T.val*
            F.normalizedNonempty hR ha lam hlam w t T)+
          (t.val⁻¹:ℝ) • (D.radialRemainder ω (sectorialRay σ w R t) (t:ℝ) S.val ∅*
            F.normalizedEmpty hR ha lam hlam w t ()+
            ∑T : NonemptySubset d,D.radialRemainder ω (sectorialRay σ w R t) (t:ℝ) S.val T.val*
              F.normalizedNonempty hR ha lam hlam w t T)) t.val := by
  obtain ⟨h0,h1⟩ := F.normalized_components_derivatives hR ha lam hlam D ω σ hF hsmall t ht
  constructor
  · have hd := (ContinuousLinearMap.proj (R:=ℝ) ()).hasFDerivAt.comp_hasDerivAt t.val h0
    simpa only [ContinuousLinearMap.proj_apply,Pi.smul_apply,hF.2.1] using hd
  · intro S
    have hd := (ContinuousLinearMap.proj (R:=ℝ) S).hasFDerivAt.comp_hasDerivAt t.val h1
    simpa only [ContinuousLinearMap.proj_apply,Pi.add_apply,Pi.smul_apply,
      complexDiagonalOperator_apply,hF.1,hF.2.2.1,hF.2.2.2,Fintype.sum_unique] using hd

end RadialOperatorFamily
end BourgadeHuang.CMS
