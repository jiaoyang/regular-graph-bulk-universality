import BourgadeHuang.CMS.CanonicalRadialEquation
import BourgadeHuang.CMS.CanonicalParameterBounds
import BourgadeHuang.CMS.CommutatorCalculus

/-! Differentiated ray covariance of the canonical analytic jet. Parameter
holomorphy and the exact translation identity give uniform decay of the
scaled coordinate derivatives along the actual ray. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

/-- Translation of the base point preserves coordinate differentiation. -/
theorem coordDeriv_shiftedRay {d : ℕ} (σ : Fin d → Sign) (h : ℝ)
    {f : Point d → ℂ} {z : Point d}
    (hf : DifferentiableAt ℂ f (shiftedRay σ z h)) (i : Fin d) :
    coordDeriv i (fun w=>f (shiftedRay σ w h)) z=
      coordDeriv i f (shiftedRay σ z h) := by
  have ht : HasFDerivAt (fun w : Point d=>shiftedRay σ w h)
      (ContinuousLinearMap.id ℂ (Point d)) z :=
    (hasFDerivAt_id z).add_const (fun j=>(h:ℂ)*shiftedDirection σ j)
  have hd := hf.hasFDerivAt.comp z ht
  change HasFDerivAt (fun w=>f (shiftedRay σ w h)) _ z at hd
  rw [coordDeriv_eq_fderiv hd.differentiableAt,hd.fderiv,
    coordDeriv_eq_fderiv hf]
  rfl

namespace RadialConstructionData
variable {d : ℕ} (P : RadialConstructionData d)

/-- Every evaluated component of the complete scaled family is analytic. -/
theorem analyticOnNhd_fullFamily_component (t : Tail P.radius) (S : Finset (Fin d)) :
    AnalyticOnNhd ℂ (fun z=>P.fullFamily z t S) (OrderedGapDomain d P.radius) := by
  intro z hz
  by_cases hS : S.Nonempty
  · let L : RadialBanach d P.radius →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (R:=ℂ) (⟨S,hS⟩ : NonemptySubset d) : RadialVector d →L[ℂ] ℂ).comp
        (BoundedContinuousFunction.evalCLM (𝕜:=ℂ) t)
    have ha := (L.analyticAt (P.nonemptyFamily z)).comp (f:=P.nonemptyFamily)
      (P.analyticOnNhd_nonemptyFamily z hz)
    simpa only [fullFamily,subsetVector,dif_pos hS,tailExtension_apply,L,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
      BoundedContinuousFunction.evalCLM_apply] using ha
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    let L : EmptyBanach P.radius →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (R:=ℂ) () : EmptyVector →L[ℂ] ℂ).comp
        (BoundedContinuousFunction.evalCLM (𝕜:=ℂ) t)
    have ha := (L.analyticAt (P.emptyFamily z)).comp (f:=P.emptyFamily)
      (P.analyticOnNhd_emptyFamily z hz)
    simpa only [fullFamily_empty,tailExtension_apply,L,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
      BoundedContinuousFunction.evalCLM_apply] using ha

/-- Coordinate differentiation commutes with the exact canonical ray shift. -/
theorem canonicalJet_coordinate_shift {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) {h : ℝ} (hh : 0≤h)
    (i : Fin d) (S : Finset (Fin d)) :
    coordDeriv i (fun w=>P.canonicalJet w S) (shiftedRay P.sign z h)=
      (((P.radius+h:ℝ):ℂ)^S.card)⁻¹*
        coordDeriv i (fun w=>P.fullFamily w (P.radius+h) S) z := by
  have he : (fun w=>P.canonicalJet (shiftedRay P.sign w h) S)=ᶠ[𝓝 z]
      (fun w=>(((P.radius+h:ℝ):ℂ)^S.card)⁻¹*P.fullFamily w (P.radius+h) S) :=
    Filter.eventuallyEq_of_mem ((orderedGapDomain_isOpen d P.radius).mem_nhds hz)
      (fun w hw=>P.canonicalJet_shift hw hh S)
  have hd := coordDeriv_congr_nhds he i
  rw [coordDeriv_shiftedRay P.sign h
    (P.analyticOnNhd_canonicalJet S _ (shiftedRay_mem_orderedGapDomain P.sign hz hh)).differentiableAt,
    coordDeriv_const_mul_analytic
      (P.analyticOnNhd_fullFamily_component (⟨P.radius+h,by linarith⟩ : Tail P.radius) S z hz)] at hd
  exact hd

/-- Along the actual sectorial ray the derivative carries precisely the
inverse subset-degree factor, with no additional derivative of time. -/
theorem canonicalJet_coordinate_ray {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) (t : Tail P.radius)
    (i : Fin d) (S : Finset (Fin d)) :
    coordDeriv i (fun w=>P.canonicalJet w S) (sectorialRay P.sign z P.radius t)=
      ((t.val:ℂ)^S.card)⁻¹*coordDeriv i (fun w=>P.fullFamily w t S) z := by
  have he := P.canonicalJet_coordinate_shift hz (sub_nonneg.mpr t.property) i S
  simpa only [sectorialRay,add_sub_cancel] using he

/-- Multiplication by the subset degree leaves a reciprocal-tail derivative
bound, uniformly in every coordinate and every subset. -/
theorem canonicalJet_scaled_coordinate_bound {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) :
    ∃C : ℝ,0≤C ∧ ∀t : Tail P.radius,∀i : Fin d,∀S : Finset (Fin d),
      ‖(t.val:ℂ)^S.card*coordDeriv i (fun w=>P.canonicalJet w S)
        (sectorialRay P.sign z P.radius t)‖≤C/t.val := by
  obtain ⟨C,hC,hbound⟩ := P.coordinate_derivatives_reciprocal_bound hz
  refine ⟨C,hC,?_⟩
  intro t i S
  rw [P.canonicalJet_coordinate_ray hz t i S,←mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (P.radius_pos.trans_le t.property).ne')),one_mul]
  by_cases hS : S.Nonempty
  · simpa only [fullFamily,subsetVector,dif_pos hS,tailExtension_apply] using
      (hbound t i).2 (⟨S,hS⟩ : NonemptySubset d)
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simpa only [fullFamily_empty,tailExtension_apply] using (hbound t i).1

end RadialConstructionData
end BourgadeHuang.CMS
