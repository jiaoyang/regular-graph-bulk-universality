import BourgadeHuang.CMS.WeightedRadialZero
import BourgadeHuang.CMS.CanonicalRadialEquation
import BourgadeHuang.CMS.CanonicalUniformBounds

/-! Independence of the canonical analytic jet from the auxiliary starting
radius and spectral-gap witnesses. The actual normalized families solve the
same differential equation, and their difference has zero terminal data. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace RadialConstructionData
variable {d : ℕ} (P : RadialConstructionData d)

/-- The canonical jet has the required weighted normalization when measured
from any smaller positive starting radius. -/
theorem canonicalJet_bounds_from_smaller_radius {R : ℝ} (hR : 0<R)
    (hRP : R≤P.radius) {z : Point d} (hz : z∈OrderedGapDomain d P.radius) :
    ∃B : ℝ,0≤B ∧ ∀t : Tail R,
      ‖P.canonicalJet (sectorialRay P.sign z R t) ∅-1‖≤B/t.val ∧
      ∀S : NonemptySubset d,
        ‖(t.val:ℂ)^S.val.card*P.canonicalJet (sectorialRay P.sign z R t) S.val‖≤B/t.val := by
  obtain ⟨B,hB,hbound⟩ := P.families_reciprocal_bound hz
  refine ⟨B,hB,?_⟩
  intro t
  let u : Tail P.radius := ⟨P.radius+(t.val-R),by linarith [t.property]⟩
  have ht : 0<t.val := hR.trans_le t.property
  have hu : 0<u.val := P.radius_pos.trans_le u.property
  have htu : t.val≤u.val := by dsimp [u];linarith
  have he (S : Finset (Fin d)) :
      P.canonicalJet (sectorialRay P.sign z R t) S=
        ((u.val:ℂ)^S.card)⁻¹*P.fullFamily z u S :=
    P.canonicalJet_shift hz (sub_nonneg.mpr t.property) S
  constructor
  · rw [he,Finset.card_empty,pow_zero,inv_one,one_mul,fullFamily_empty,tailExtension_apply]
    exact ((norm_le_pi_norm (P.emptyFamily z u-1) ()).trans (hbound u).1).trans
      (div_le_div_of_nonneg_left hB ht htu)
  · intro S
    rw [he,←mul_assoc,norm_mul,norm_mul,norm_inv,norm_pow,norm_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu]
    have hr : t.val^S.val.card*(u.val^S.val.card)⁻¹≤1 := by
      rw [←div_eq_mul_inv,←div_pow]
      exact pow_le_one₀ (div_nonneg ht.le hu.le) ((div_le_one hu).mpr htu)
    have hb : ‖P.fullFamily z u S.val‖≤B/t.val := by
      rw [fullFamily_nonempty,tailExtension_apply]
      exact ((norm_le_pi_norm (P.nonemptyFamily z u) S).trans (hbound u).2).trans
        (div_le_div_of_nonneg_left hB ht htu)
    exact (mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans (by simpa only [one_mul] using hb)

/-- Actual differentiation along a ray based at an arbitrary earlier time. -/
theorem hasDerivAt_canonicalJet_ray {R : ℝ} {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) {t : ℝ} (ht : R<t)
    (S : Finset (Fin d)) :
    HasDerivAt (fun r : ℝ=>P.canonicalJet (sectorialRay P.sign z R r) S)
      (P.D.radialConnectionAction (shiftedDirection P.sign)
        (sectorialRay P.sign z R t) (P.canonicalJet (sectorialRay P.sign z R t)) S) t := by
  have hd := (P.hasDerivAt_canonicalJet_shift hz (sub_pos.mpr ht) S).scomp t
    ((hasDerivAt_id t).sub_const R)
  simpa only [sectorialRay,one_smul] using hd

/-- The canonical jet is independent of every auxiliary construction datum
once the actual connection and ray direction agree. -/
theorem canonicalJet_eq_of_same_connection (Q : RadialConstructionData d)
    (hD : P.D=Q.D) (hs : P.sign=Q.sign) (hR : P.radius≤Q.radius)
    {z : Point d} (hzP : z∈OrderedGapDomain d P.radius)
    (hzQ : z∈OrderedGapDomain d Q.radius) : P.canonicalJet z=Q.canonicalJet z := by
  let H : ℝ → Finset (Fin d) → ℂ := fun t S=>
    P.canonicalJet (sectorialRay P.sign z P.radius t) S-
      Q.canonicalJet (sectorialRay P.sign z P.radius t) S
  have hcont (S : Finset (Fin d)) : Continuous (fun t : Tail P.radius=>H t.val S) := by
    have hray : Continuous (fun t : Tail P.radius=>sectorialRay P.sign z P.radius t) := by
      unfold sectorialRay shiftedRay
      fun_prop
    have hPc : Continuous (fun t : Tail P.radius=>P.canonicalJet (sectorialRay P.sign z P.radius t) S) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (P.analyticOnNhd_canonicalJet S _
        (shiftedRay_mem_orderedGapDomain P.sign hzP (sub_nonneg.mpr t.property))).continuousAt.comp (f:=fun t : Tail P.radius=>sectorialRay P.sign z P.radius t)
        hray.continuousAt
    have hQc : Continuous (fun t : Tail P.radius=>Q.canonicalJet (sectorialRay P.sign z P.radius t) S) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      have hm : sectorialRay P.sign z P.radius t∈OrderedGapDomain d Q.radius :=
        shiftedRay_mem_orderedGapDomain P.sign hzQ (sub_nonneg.mpr t.property)
      exact (Q.analyticOnNhd_canonicalJet S _ hm).continuousAt.comp
        (f:=fun t : Tail P.radius=>sectorialRay P.sign z P.radius t) hray.continuousAt
    exact hPc.sub hQc
  have hb : ∃C : ℝ,0≤C ∧ ∀t : Tail P.radius,∀S,
      ‖(t.val:ℂ)^S.card*H t.val S‖≤C/t.val := by
    obtain ⟨B,hB,hp⟩ := P.canonicalJet_bounds_from_smaller_radius P.radius_pos le_rfl hzP
    obtain ⟨C,hC,hq⟩ := Q.canonicalJet_bounds_from_smaller_radius P.radius_pos hR hzQ
    refine ⟨B+C,add_nonneg hB hC,?_⟩
    intro t S
    have hq' := hq t
    rw [←hs] at hq'
    by_cases hS : S.Nonempty
    · dsimp only [H]
      rw [mul_sub]
      exact (norm_sub_le _ _).trans ((add_le_add ((hp t).2 ⟨S,hS⟩)
        (hq'.2 ⟨S,hS⟩)).trans_eq (by ring))
    · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      simp only [Finset.card_empty,pow_zero,one_mul,H]
      rw [show P.canonicalJet (sectorialRay P.sign z P.radius t) ∅-
          Q.canonicalJet (sectorialRay P.sign z P.radius t) ∅=
          (P.canonicalJet (sectorialRay P.sign z P.radius t) ∅-1)-
          (Q.canonicalJet (sectorialRay P.sign z P.radius t) ∅-1) by ring]
      exact (norm_sub_le _ _).trans ((add_le_add (hp t).1 hq'.1).trans_eq (by ring))
  have hODE : ∀t : Tail P.radius,P.radius<t.val → ∀S,
      HasDerivAt (fun r : ℝ=>(r:ℂ)^S.card*H r S)
        (P.D.scaledRadialAction (shiftedDirection P.sign)
          (sectorialRay P.sign z P.radius t) (t:ℝ)
          (fun T=>(t.val:ℂ)^T.card*H t.val T) S) t.val := by
    intro t ht S
    have hp := P.hasDerivAt_canonicalJet_ray hzP ht S
    have hq := Q.hasDerivAt_canonicalJet_ray hzQ ht S
    rw [←hs,←hD] at hq
    have hd := hp.sub hq
    have hu : HasDerivAt (fun r=>H r S)
        (P.D.radialConnectionAction (shiftedDirection P.sign)
          (sectorialRay P.sign z P.radius t) (H t.val) S) t.val := by
      simpa only [H,SectorialData.radialConnectionAction,mul_sub,Finset.sum_sub_distrib] using hd
    exact P.D.hasDerivAt_scale_radial _ _ H (P.radius_pos.trans ht).ne' S hu
  have he := P.unscaled_radial_zero hzP H hcont hb hODE
  funext S
  have hh := he S
  have hstart : sectorialRay P.sign z P.radius P.radius=z := by
    funext i
    simp [sectorialRay,shiftedRay]
  change P.canonicalJet (sectorialRay P.sign z P.radius P.radius) S-
    Q.canonicalJet (sectorialRay P.sign z P.radius P.radius) S=0 at hh
  rw [hstart] at hh
  exact sub_eq_zero.mp hh

/-- No ordering of the two construction radii is needed in the final
choice-independence statement. -/
theorem canonicalJet_eq (Q : RadialConstructionData d)
    (hD : P.D=Q.D) (hs : P.sign=Q.sign) {z : Point d}
    (hzP : z∈OrderedGapDomain d P.radius) (hzQ : z∈OrderedGapDomain d Q.radius) :
    P.canonicalJet z=Q.canonicalJet z := by
  rcases le_total P.radius Q.radius with hR|hR
  · exact P.canonicalJet_eq_of_same_connection Q hD hs hR hzP hzQ
  · exact (Q.canonicalJet_eq_of_same_connection P hD.symm hs.symm hR hzQ hzP).symm

@[simp] theorem canonicalJet_empty (z : Point d) :
    P.canonicalJet z ∅=P.normalizedGerm z := by
  simp only [canonicalJet,Finset.card_empty,pow_zero,inv_one,one_mul,fullFamily_empty,
    normalizedGerm,show ∀w,tailExtension (P.emptyFamily w) P.radius=P.emptyFamily w ⟨P.radius,le_rfl⟩ from
      fun w=>tailExtension_apply _ ⟨P.radius,le_rfl⟩]

theorem normalizedGerm_eq (Q : RadialConstructionData d)
    (hD : P.D=Q.D) (hs : P.sign=Q.sign) {z : Point d}
    (hzP : z∈OrderedGapDomain d P.radius) (hzQ : z∈OrderedGapDomain d Q.radius) :
    P.normalizedGerm z=Q.normalizedGerm z := by
  have he := congrFun (P.canonicalJet_eq Q hD hs hzP hzQ) ∅
  simpa only [canonicalJet_empty] using he

end RadialConstructionData
end BourgadeHuang.CMS
