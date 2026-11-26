import BourgadeHuang.CMS.FullRadialUniqueness
import BourgadeHuang.CMS.ScaledRadialCalculus
import BourgadeHuang.CMS.BoundedTailTranslation

/-! Choice-free ray covariance of the actual normalized sectorial family.
It follows from the proved differential equations and their genuine uniqueness. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace RadialConstructionData
variable {d : ℕ} (P : RadialConstructionData d)

private theorem translated_full_value (z : Point d) {h : ℝ} (hh : 0≤h)
    (t : Tail P.radius) (S : Finset (Fin d)) :
    subsetVector ((translateTailOperator hh (P.emptyFamily z)) t ())
      (boundedUnweight P.radius_pos
        (translateWeighted P.radius_pos hh (fun S : NonemptySubset d => S.val.card)
          (P.weightedFamily z)) t) S=
      ((t.val:ℂ)/((t.val:ℂ)+(h:ℂ)))^S.card*P.fullFamily z (t.val+h) S := by
  by_cases hS : S.Nonempty
  · change _=((t.val:ℂ)/((t.val:ℂ)+(h:ℂ)))^S.card*
      P.fullFamily z (translateTail hh t).val (⟨S,hS⟩ : NonemptySubset d).val
    rw [fullFamily_nonempty,tailExtension_apply]
    simp only [subsetVector,dif_pos hS,unweight_translateWeighted,
      Complex.ofReal_div,Complex.ofReal_add,nonemptyFamily]
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp only [subsetVector_empty,Finset.card_empty,pow_zero,one_mul,fullFamily_empty,
      translateTailOperator_apply]
    change _=tailExtension (P.emptyFamily z) (translateTail hh t).val ()
    rw [tailExtension_apply]

/-- Moving the origin along its actual ray translates the normalized weighted
solution with precisely the subset degree correction. -/
theorem weightedFamily_shift {z : Point d} (hz : z∈OrderedGapDomain d P.radius)
    {h : ℝ} (hh : 0≤h) :
    translateWeighted P.radius_pos hh (fun S : NonemptySubset d => S.val.card)
        (P.weightedFamily z)=P.weightedFamily (shiftedRay P.sign z h) ∧
      translateTailOperator hh (P.emptyFamily z)=P.emptyFamily (shiftedRay P.sign z h) := by
  let Y0 := translateTailOperator hh (P.emptyFamily z)
  let Z := translateWeighted P.radius_pos hh (fun S : NonemptySubset d => S.val.card)
    (P.weightedFamily z)
  have hlim : Tendsto Y0 atTop (𝓝 (1:EmptyVector)) :=
    (P.families_limits hz).1.comp (tendsto_translateTail_atTop hh)
  apply P.full_radial_unique (shiftedRay_mem_orderedGapDomain P.sign hz hh) Y0 Z hlim
  intro t ht S
  have htp : 0<t.val := P.radius_pos.trans ht
  have hthp : 0<t.val+h := by linarith
  have hd := P.D.hasDerivAt_translate_scaled_radial P.sign z P.radius h
    (P.fullFamily z) htp.ne' hthp.ne'
    (fun T => P.hasDerivAt_fullFamily hz (translateTail hh t) (by dsimp; linarith) T) S
  have hv : subsetVector (Y0 t ()) (boundedUnweight P.radius_pos Z t)=
      fun T => ((t.val:ℂ)/((t.val:ℂ)+(h:ℂ)))^T.card*P.fullFamily z (t.val+h) T := by
    funext T
    exact P.translated_full_value z hh t T
  rw [hv]
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with s hs
  have he := P.translated_full_value z hh (⟨s,hs.le⟩ : Tail P.radius) S
  change subsetVector (tailExtension Y0 (⟨s,hs.le⟩ : Tail P.radius).val ())
    (tailExtension (boundedUnweight P.radius_pos Z) (⟨s,hs.le⟩ : Tail P.radius).val) S=_
  rw [tailExtension_apply,tailExtension_apply]
  exact he

/-- Full scaled ray covariance, valid also at the endpoint of the half-line. -/
theorem fullFamily_shift {z : Point d} (hz : z∈OrderedGapDomain d P.radius)
    {h : ℝ} (hh : 0≤h) (t : Tail P.radius) (S : Finset (Fin d)) :
    P.fullFamily (shiftedRay P.sign z h) t S=
      ((t.val:ℂ)/((t.val:ℂ)+(h:ℂ)))^S.card*P.fullFamily z (t.val+h) S := by
  have he := P.translated_full_value z hh t S
  obtain ⟨hZ,h0⟩ := P.weightedFamily_shift hz hh
  rw [hZ,h0] at he
  simpa only [fullFamily,tailExtension_apply,nonemptyFamily] using he

/-- The candidate unscaled square-free jet at the initial ray point. -/
def canonicalJet (z : Point d) (S : Finset (Fin d)) : ℂ :=
  ((P.radius:ℂ)^S.card)⁻¹*P.fullFamily z P.radius S

/-- The canonical jet agrees with the entire unscaled radial curve at every
positive translate. This is the actual compatibility of base point and time. -/
theorem canonicalJet_shift {z : Point d} (hz : z∈OrderedGapDomain d P.radius)
    {h : ℝ} (hh : 0≤h) (S : Finset (Fin d)) :
    P.canonicalJet (shiftedRay P.sign z h) S=
      (((P.radius+h:ℝ):ℂ)^S.card)⁻¹*P.fullFamily z (P.radius+h) S := by
  unfold canonicalJet
  rw [P.fullFamily_shift hz hh (⟨P.radius,le_rfl⟩ : Tail P.radius)]
  have hR : (P.radius:ℂ)≠0 := Complex.ofReal_ne_zero.mpr P.radius_pos.ne'
  simp only [Complex.ofReal_add,div_pow,div_eq_mul_inv,mul_pow,inv_pow]
  simp only [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hR),one_mul]

end RadialConstructionData
end BourgadeHuang.CMS
