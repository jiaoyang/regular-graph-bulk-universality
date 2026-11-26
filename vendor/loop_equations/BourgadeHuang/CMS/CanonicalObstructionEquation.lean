import BourgadeHuang.CMS.CanonicalRadialEquation
import BourgadeHuang.CMS.SectorialObstruction

/-! The actual coordinate obstruction of the constructed physical family
satisfies the homogeneous radial equation, by proved matrix flatness. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
namespace RadialConstructionData
variable {d : ℕ} {β : ℝ} (hβ : 0<β) (c : Fin d → ℂ) (σ : Fin d → Sign)
  (hc : ∀i,c i= -1 ∨ c i=(β:ℂ)/2)

/-- The coordinate defect is an actual analytic function on the constructed chamber. -/
theorem physical_analyticOnNhd_obstruction (i : Fin d) (S : Finset (Fin d)) :
    let P:=physical hβ c σ hc
    AnalyticOnNhd ℂ (P.D.obstruction P.canonicalJet i S) (OrderedGapDomain d P.radius) := by
  let P:=physical hβ c σ hc
  exact P.D.analyticOnNhd_obstruction P.canonicalJet
    (orderedGapDomain_subset_orderedDomain P.radius_pos.le) P.analyticOnNhd_canonicalJet i S

/-- The homogeneous radial equation follows from the genuine physical
connection curvature and the now proved radial equation of the family. -/
theorem physical_obstruction_radial {z : Point d}
    (hz : z∈OrderedGapDomain d (physical hβ c σ hc).radius)
    (i : Fin d) (S : Finset (Fin d)) :
    let P:=physical hβ c σ hc
    (∑j,shiftedDirection P.sign j*coordDeriv j (P.D.obstruction P.canonicalJet i S) z)=
      P.D.radialConnectionAction (shiftedDirection P.sign) z
        (fun T=>P.D.obstruction P.canonicalJet i T z) S := by
  let P:=physical hβ c σ hc
  exact SectorialData.general_obstruction_radial (β:ℂ) c σ
    (Complex.ofReal_ne_zero.mpr hβ.ne') hc P.canonicalJet (shiftedDirection P.sign)
    (orderedGapDomain_isOpen d P.radius)
    (orderedGapDomain_subset_orderedDomain P.radius_pos.le)
    P.analyticOnNhd_canonicalJet (fun w hw S=>P.canonicalJet_radial hw S) i S hz

/-- The degree-scaled obstruction obeys precisely the full scaled ODE used
in the established zero-normalization uniqueness theorem. -/
theorem physical_hasDerivAt_scaled_obstruction {z : Point d}
    (hz : z∈OrderedGapDomain d (physical hβ c σ hc).radius)
    (i : Fin d) (S : Finset (Fin d)) (t : Tail (physical hβ c σ hc).radius)
    (ht : (physical hβ c σ hc).radius<t.val) :
    let P:=physical hβ c σ hc
    HasDerivAt (fun r : ℝ=>(r:ℂ)^S.card*
      P.D.obstruction P.canonicalJet i S (sectorialRay P.sign z P.radius r))
      (P.D.scaledRadialAction (shiftedDirection P.sign)
        (sectorialRay P.sign z P.radius t) (t:ℝ)
        (fun T=>(t.val:ℂ)^T.card*P.D.obstruction P.canonicalJet i T
          (sectorialRay P.sign z P.radius t)) S) t.val := by
  let P:=physical hβ c σ hc
  let b:=shiftedRay P.sign z (-P.radius)
  have he (s : ℝ) : complexAffineRay b (shiftedDirection P.sign) (s:ℂ)=
      sectorialRay P.sign z P.radius s := by
    funext j
    simp only [b,complexAffineRay,sectorialRay,shiftedRay,Complex.ofReal_neg,Complex.ofReal_sub]
    ring
  have hm : sectorialRay P.sign z P.radius t∈OrderedGapDomain d P.radius :=
    shiftedRay_mem_orderedGapDomain P.sign hz (sub_nonneg.mpr t.property)
  have ha := physical_analyticOnNhd_obstruction hβ c σ hc i S _ hm
  have hda := (hasDerivAt_comp_complexAffineRay b (shiftedDirection P.sign) (t.val:ℂ)
    (by simpa only [he] using ha)).comp_ofReal
  simp only [he] at hda
  rw [physical_obstruction_radial hβ c σ hc hm i S] at hda
  exact P.D.hasDerivAt_scale_radial (shiftedDirection P.sign)
    (sectorialRay P.sign z P.radius t)
    (fun r T=>P.D.obstruction P.canonicalJet i T (sectorialRay P.sign z P.radius r))
    (P.radius_pos.trans ht).ne' S hda

end RadialConstructionData
end BourgadeHuang.CMS
