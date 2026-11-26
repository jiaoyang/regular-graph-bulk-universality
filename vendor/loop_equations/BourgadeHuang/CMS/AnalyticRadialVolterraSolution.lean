import BourgadeHuang.CMS.SectorialVolterraAnalytic

/-! A genuine holomorphic solution of the weighted radial Volterra equation,
with all coefficient bounds and nilpotence derived from the CMS reduction. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace RadialOperatorFamily
variable {d : ℕ} {R a : ℝ} (F : RadialOperatorFamily d R)

abbrev nOp (w : Point d) := complexBoundedCoefficientOperator (F.N w)
abbrev c01Op (w : Point d) := complexBoundedCoefficientOperator (F.C01 w)
abbrev c10Op (w : Point d) := complexBoundedCoefficientOperator (F.C10 w)
abbrev c11Op (w : Point d) := complexBoundedCoefficientOperator (F.C11 w)

def effectiveOperator (hR : 0<R) (ha : 0<a) (lam : NonemptySubset d → ℂ)
    (hlam : ∀i,a≤(lam i).re) (w : Point d) : RadialBanach d R →L[ℂ] RadialBanach d R :=
  triangularInverse ((freeForcingOperator hR ha lam hlam).comp (F.nOp w)) (d+1)*
    coupledVolterraRemainder (freeRemainderOperator hR ha lam hlam)
      (complexPrimitiveOperator (E:=EmptyVector) hR) (F.c01Op w) (F.c10Op w) (F.c11Op w)

def weightedSolution (hR : 0<R) (ha : 0<a) (lam : NonemptySubset d → ℂ)
    (hlam : ∀i,a≤(lam i).re) (w : Point d) : RadialBanach d R :=
  coupledVolterraSolution (freeForcingOperator hR ha lam hlam)
    (freeRemainderOperator hR ha lam hlam) (complexPrimitiveOperator (E:=EmptyVector) hR)
    (F.nOp w) (F.c01Op w) (F.c10Op w) (F.c11Op w)
    (BoundedContinuousFunction.const _ (1:EmptyVector)) (d+1)

theorem analyticAt_effectiveOperator (hR : 0<R) (ha : 0<a)
    (lam : NonemptySubset d → ℂ) (hlam : ∀i,a≤(lam i).re) {z : Point d}
    (hF : F.AnalyticAt z) : _root_.AnalyticAt ℂ (F.effectiveOperator hR ha lam hlam) z := by
  have hn := analyticAt_complexBoundedCoefficientOperator hF.1
  have h01 := analyticAt_complexBoundedCoefficientOperator hF.2.1
  have h10 := analyticAt_complexBoundedCoefficientOperator hF.2.2.1
  have h11 := analyticAt_complexBoundedCoefficientOperator hF.2.2.2
  have hB : _root_.AnalyticAt ℂ (fun w => (freeForcingOperator hR ha lam hlam).comp (F.nOp w)) z :=
    analyticAt_clm_comp analyticAt_const hn
  have hK : _root_.AnalyticAt ℂ (fun w => (F.c10Op w).comp (complexPrimitiveOperator (E:=EmptyVector) hR)) z :=
    analyticAt_clm_comp h10 analyticAt_const
  have hC : _root_.AnalyticAt ℂ (fun w =>
      ((F.c10Op w).comp (complexPrimitiveOperator (E:=EmptyVector) hR)).comp (F.c01Op w)+F.c11Op w) z :=
    (analyticAt_clm_comp hK h01).add h11
  exact (analyticAt_triangularInverse hB (d+1)).mul
    (analyticAt_clm_comp (analyticAt_const (v:=freeRemainderOperator hR ha lam hlam)) hC)

theorem analyticAt_weightedSolution (hR : 0<R) (ha : 0<a)
    (lam : NonemptySubset d → ℂ) (hlam : ∀i,a≤(lam i).re) {z : Point d}
    (hF : F.AnalyticAt z) (hsmall : ‖F.effectiveOperator hR ha lam hlam z‖<1) :
    _root_.AnalyticAt ℂ (F.weightedSolution hR ha lam hlam) z := by
  apply analyticAt_coupledVolterraSolution
    (freeForcingOperator hR ha lam hlam) (freeRemainderOperator hR ha lam hlam)
    (complexPrimitiveOperator (E:=EmptyVector) hR)
    (analyticAt_complexBoundedCoefficientOperator hF.1)
    (analyticAt_complexBoundedCoefficientOperator hF.2.1)
    (analyticAt_complexBoundedCoefficientOperator hF.2.2.1)
    (analyticAt_complexBoundedCoefficientOperator hF.2.2.2)
    _ (d+1) hsmall

theorem effectiveOperator_lt_one (D : SectorialData d) (ω : Point d) (σ : Fin d → Sign)
    (hR : 0<R) (ha : 0<a) (lam : NonemptySubset d → ℂ) (hlam : ∀i,a≤(lam i).re)
    {z : Point d} (hF : F.Matches D ω σ z) (hz : z∈OrderedDomain d)
    (hsep : ∀i j,i≠j→R≤‖z i-z j‖)
    (hlarge : triangularInverseBound a (blockBound D ω) (d+1)*a⁻¹*
      (blockBound D ω*blockBound D ω+blockBound D ω)<R) :
    ‖F.effectiveOperator hR ha lam hlam z‖<1 := by
  obtain ⟨hn,h01,h10,h11⟩ := F.norm_blocks_le D ω σ hF hR hz hsep
  exact eliminated_coupledVolterra_lt_one_of_radius hR ha (blockBound_pos D ω).le
    (freeForcingOperator hR ha lam hlam) (freeRemainderOperator hR ha lam hlam)
    (complexPrimitiveOperator (E:=EmptyVector) hR)
    (F.nOp z) (F.c01Op z) (F.c10Op z) (F.c11Op z)
    (norm_freeForcingOperator_le hR ha lam hlam) (norm_freeRemainderOperator_le hR ha lam hlam)
    (norm_complexPrimitiveOperator_le hR)
    ((norm_complexBoundedCoefficientOperator_le _).trans hn)
    ((norm_complexBoundedCoefficientOperator_le _).trans h01)
    ((norm_complexBoundedCoefficientOperator_le _).trans h10)
    ((norm_complexBoundedCoefficientOperator_le _).trans h11) (d+1) hlarge

/-- The constructed analytic family satisfies the actual coupled integral
equation wherever the proven matrix identities and contraction hold. -/
theorem weightedSolution_equation (D : SectorialData d) (ω : Point d) (σ : Fin d → Sign)
    (hR : 0<R) (ha : 0<a) (lam : NonemptySubset d → ℂ) (hlam : ∀i,a≤(lam i).re)
    {w : Point d} (hF : F.Matches D ω σ w)
    (hsmall : ‖F.effectiveOperator hR ha lam hlam w‖<1) :
    let Z := F.weightedSolution hR ha lam hlam w
    Z=freeForcingOperator hR ha lam hlam (F.nOp w Z+
        F.c10Op w (BoundedContinuousFunction.const _ (1:EmptyVector)))+
      freeRemainderOperator hR ha lam hlam
        (F.c10Op w (complexPrimitiveOperator hR (F.c01Op w Z))+F.c11Op w Z) :=
  coupledVolterraSolution_equation _ _ _ _ _ _ _ _ _
    (F.principal_integral_nilpotent D ω σ hF hR ha lam hlam) hsmall

end RadialOperatorFamily

namespace SectorialData
variable {d : ℕ} (D : SectorialData d) (ω : Point d) (σ : Fin d → Sign)
  {R a : ℝ} {z : Point d}

/-- Explicit large-radius construction of a holomorphic family of true
weighted Volterra solutions for the CMS radial coefficients. -/
theorem exists_analytic_weightedRadialSolution (hR : 0<R) (ha : 0<a)
    (lam : NonemptySubset d → ℂ) (hlam : ∀i,a≤(lam i).re)
    (hz : z∈OrderedDomain d) (hsep : ∀i j,i≠j→R≤‖z i-z j‖)
    (hlarge : triangularInverseBound a (RadialOperatorFamily.blockBound D ω) (d+1)*a⁻¹*
      (RadialOperatorFamily.blockBound D ω*RadialOperatorFamily.blockBound D ω+
        RadialOperatorFamily.blockBound D ω)<R) :
    ∃F : RadialOperatorFamily d R,F.AnalyticAt z ∧
      _root_.AnalyticAt ℂ (F.weightedSolution hR ha lam hlam) z ∧
      ∀ᶠw in 𝓝 z,F.Matches D ω σ w ∧
        ‖F.effectiveOperator hR ha lam hlam w‖<1 := by
  obtain ⟨F,hF,hmatch⟩ := D.exists_analytic_radialOperatorFamily ω σ hR hz hsep
  have hs := F.effectiveOperator_lt_one D ω σ hR ha lam hlam hmatch.self_of_nhds hz hsep hlarge
  refine ⟨F,hF,F.analyticAt_weightedSolution hR ha lam hlam hF hs,?_⟩
  have hc0 : ContinuousAt (F.effectiveOperator hR ha lam hlam) z :=
    (F.analyticAt_effectiveOperator hR ha lam hlam hF).continuousAt
  have hc : ContinuousAt (fun w => ‖F.effectiveOperator hR ha lam hlam w‖) z :=
    ContinuousAt.norm (f := F.effectiveOperator hR ha lam hlam) hc0
  have hse : ∀ᶠw in 𝓝 z,‖F.effectiveOperator hR ha lam hlam w‖<1 :=
    hc.eventually (Iio_mem_nhds hs)
  filter_upwards [hmatch,hse] with w hw hsw
  exact ⟨hw,hsw⟩

end SectorialData
end BourgadeHuang.CMS
