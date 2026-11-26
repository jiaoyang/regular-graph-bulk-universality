import BourgadeHuang.CMS.CanonicalRayCovariance

/-! The patched canonical finite vector is genuinely analytic in its base
point and satisfies the actual radial connection equation there. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace RadialConstructionData
variable {d : ℕ} (P : RadialConstructionData d)

/-- Each canonical candidate jet is holomorphic on the large chamber. -/
theorem analyticOnNhd_canonicalJet (S : Finset (Fin d)) :
    AnalyticOnNhd ℂ (fun z => P.canonicalJet z S) (OrderedGapDomain d P.radius) := by
  intro z hz
  by_cases hS : S.Nonempty
  · let L : RadialBanach d P.radius →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (R:=ℂ) (⟨S,hS⟩ : NonemptySubset d) : RadialVector d →L[ℂ] ℂ).comp
        (BoundedContinuousFunction.evalCLM (𝕜:=ℂ) (⟨P.radius,le_rfl⟩ : Tail P.radius))
    have hL : AnalyticAt ℂ L (P.nonemptyFamily z) := L.analyticAt _
    have ha := (analyticAt_const (v:=((P.radius:ℂ)^S.card)⁻¹)).mul (hL.comp (f:=P.nonemptyFamily) (P.analyticOnNhd_nonemptyFamily z hz))
    simpa only [canonicalJet,fullFamily,subsetVector,dif_pos hS,L,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply,BoundedContinuousFunction.evalCLM_apply,
      show ∀w,tailExtension (P.nonemptyFamily w) P.radius=P.nonemptyFamily w ⟨P.radius,le_rfl⟩ from
        fun w => tailExtension_apply _ ⟨P.radius,le_rfl⟩] using ha
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    have ha := P.analyticOnNhd_normalizedGerm z hz
    simpa only [canonicalJet,fullFamily_empty,Finset.card_empty,pow_zero,inv_one,one_mul,
      normalizedGerm,show ∀w,tailExtension (P.emptyFamily w) P.radius=P.emptyFamily w ⟨P.radius,le_rfl⟩ from
        fun w => tailExtension_apply _ ⟨P.radius,le_rfl⟩] using ha

/-- Positive-time differentiation follows from actual shift covariance and
the original normalized radial ODE. -/
theorem hasDerivAt_canonicalJet_shift {z : Point d} (hz : z∈OrderedGapDomain d P.radius)
    {h : ℝ} (hh : 0<h) (S : Finset (Fin d)) :
    HasDerivAt (fun r : ℝ => P.canonicalJet (shiftedRay P.sign z r) S)
      (P.D.radialConnectionAction (shiftedDirection P.sign) (shiftedRay P.sign z h)
        (P.canonicalJet (shiftedRay P.sign z h)) S) h := by
  have ht : 0<P.radius+h := by linarith [P.radius_pos]
  have hY := P.hasDerivAt_fullFamily hz (⟨P.radius+h,by linarith⟩ : Tail P.radius) (by dsimp; linarith) S
  have hd := (P.D.hasDerivAt_unscale_radial (shiftedDirection P.sign)
    (sectorialRay P.sign z P.radius (P.radius+h)) (P.fullFamily z) ht.ne' S hY).scomp h
      ((hasDerivAt_id h).const_add P.radius)
  have hp : sectorialRay P.sign z P.radius (P.radius+h)=shiftedRay P.sign z h := by
    simp [sectorialRay]
  have hv : (fun T => (((P.radius+h:ℝ):ℂ)^T.card)⁻¹*P.fullFamily z (P.radius+h) T)=
      P.canonicalJet (shiftedRay P.sign z h) := by
    funext T
    exact (P.canonicalJet_shift hz hh.le T).symm
  simp only [one_smul,hp,hv] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hh] with r hr
  exact P.canonicalJet_shift hz hr.le S

/-- A short backward shift stays in the open large chamber. -/
theorem exists_backward_shift {z : Point d} (hz : z∈OrderedGapDomain d P.radius) :
    ∃h : ℝ,0<h ∧ shiftedRay P.sign z (-h)∈OrderedGapDomain d P.radius := by
  have hc : Continuous (fun r : ℝ => shiftedRay P.sign z (-r)) := by
    apply continuous_pi
    intro i
    change Continuous (fun r : ℝ => z i+((-r:ℝ):ℂ)*shiftedDirection P.sign i)
    fun_prop
  have hn : ∀ᶠr in 𝓝 (0:ℝ),shiftedRay P.sign z (-r)∈OrderedGapDomain d P.radius := by
    have hc0 : Tendsto (fun r : ℝ => shiftedRay P.sign z (-r)) (𝓝 0) (𝓝 z) := by
      have hc0 := hc.continuousAt (x:=0)
      change Tendsto (fun r : ℝ => shiftedRay P.sign z (-r)) (𝓝 0)
        (𝓝 (shiftedRay P.sign z (-(0:ℝ)))) at hc0
      rw [show shiftedRay P.sign z (-(0:ℝ))=z by
        funext i
        simp [shiftedRay]] at hc0
      exact hc0
    exact hc0.eventually ((orderedGapDomain_isOpen d P.radius).mem_nhds hz)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε/2,by linarith,hball ?_⟩
  simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hε)]
  linarith

/-- The canonical analytic finite vector satisfies the true first-order
radial equation at every point, including its initial ray point. -/
theorem canonicalJet_radial {z : Point d} (hz : z∈OrderedGapDomain d P.radius)
    (S : Finset (Fin d)) :
    (∑i,shiftedDirection P.sign i*coordDeriv i (fun w => P.canonicalJet w S) z)=
      P.D.radialConnectionAction (shiftedDirection P.sign) z (P.canonicalJet z) S := by
  obtain ⟨h,hh,hw⟩ := P.exists_backward_shift hz
  let w := shiftedRay P.sign z (-h)
  have he : shiftedRay P.sign w h=z := by
    funext i
    simp only [w,shiftedRay,Complex.ofReal_neg]
    ring
  have hd := P.hasDerivAt_canonicalJet_shift hw hh S
  have ha : AnalyticAt ℂ (fun q => P.canonicalJet q S)
      (complexAffineRay w (shiftedDirection P.sign) (h:ℂ)) := by
    change AnalyticAt ℂ (fun q => P.canonicalJet q S) (shiftedRay P.sign w h)
    rw [he]
    exact P.analyticOnNhd_canonicalJet S z hz
  have hc := (hasDerivAt_comp_complexAffineRay w (shiftedDirection P.sign) (h:ℂ) ha).comp_ofReal
  have hu := hc.unique hd
  change (∑i,shiftedDirection P.sign i*coordDeriv i (fun q => P.canonicalJet q S)
    (shiftedRay P.sign w h))=P.D.radialConnectionAction (shiftedDirection P.sign)
      (shiftedRay P.sign w h) (P.canonicalJet (shiftedRay P.sign w h)) S at hu
  simpa only [he] using hu

end RadialConstructionData
end BourgadeHuang.CMS
