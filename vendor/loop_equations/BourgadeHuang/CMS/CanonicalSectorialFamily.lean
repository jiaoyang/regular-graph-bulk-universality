import BourgadeHuang.CMS.PhysicalAnalyticRadial
import BourgadeHuang.CMS.SectorialRadialUniqueness

/-! Canonical holomorphic normalized radial families on the large ordered
chamber, patched from the constructed local Banach-space solutions. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

/-- The large ordered chamber is an actual open set. -/
theorem orderedGapDomain_isOpen (d : ℕ) (R : ℝ) : IsOpen (OrderedGapDomain d R) := by
  simp only [OrderedGapDomain,setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro hij
  exact isOpen_lt continuous_const (by fun_prop)

theorem orderedGapDomain_norm_separation {d : ℕ} {R : ℝ} {z : Point d}
    (hz : z∈OrderedGapDomain d R) : ∀i j,i≠j→R≤‖z i-z j‖ := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij|hji
  · have hh := (hz i j hij).le.trans (Complex.re_le_norm (z j-z i))
    simpa only [norm_sub_rev] using hh
  · exact (hz j i hji).le.trans (Complex.re_le_norm (z i-z j))

/-- Input data with only the proved spectral and radius conditions. The
physical constructor below derives them from β>0 and the finite charges. -/
structure RadialConstructionData (d : ℕ) where
  D : SectorialData d
  sign : Fin d → Sign
  radius : ℝ
  gap : ℝ
  radius_pos : 0<radius
  gap_pos : 0<gap
  lam : NonemptySubset d → ℂ
  lam_eq : ∀S,lam S=D.principalDiagonal (shiftedDirection sign) S.val
  lam_gap : ∀S,gap≤(lam S).re
  radius_large : triangularInverseBound gap
    (RadialOperatorFamily.blockBound D (shiftedDirection sign)) (d+1)*gap⁻¹*
      (RadialOperatorFamily.blockBound D (shiftedDirection sign)*
        RadialOperatorFamily.blockBound D (shiftedDirection sign)+
        RadialOperatorFamily.blockBound D (shiftedDirection sign))<radius

namespace RadialConstructionData
variable {d : ℕ}

/-- The article's physical sectorial input, with no gap or radius assumption
left to the caller. -/
def physical {β : ℝ} (hβ : 0<β) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hc : ∀i,c i=-1 ∨ c i=(β:ℂ)/2) : RadialConstructionData d where
  D := SectorialData.general (β:ℂ) c σ
  sign := SectorialData.physicalRaySign c σ
  radius := (SectorialData.general (β:ℂ) c σ).analyticRadius
    (shiftedDirection (SectorialData.physicalRaySign c σ)) (min 2 β/2)
  gap := min 2 β/2
  radius_pos := (SectorialData.general (β:ℂ) c σ).analyticRadius_pos _
    (SectorialData.physical_halfGap_pos hβ)
  gap_pos := SectorialData.physical_halfGap_pos hβ
  lam S := (SectorialData.general (β:ℂ) c σ).principalDiagonal
    (shiftedDirection (SectorialData.physicalRaySign c σ)) S.val
  lam_eq := fun _ => rfl
  lam_gap := SectorialData.physical_analytic_gap hβ c σ hc
  radius_large := lt_add_one _

variable (P : RadialConstructionData d)

/-- A local lift chosen from the proved actual construction. -/
def localFamily (z : Point d) (hz : z∈OrderedGapDomain d P.radius) :
    RadialOperatorFamily d P.radius :=
  (P.D.exists_analytic_weightedRadialSolution (shiftedDirection P.sign) P.sign
    P.radius_pos P.gap_pos P.lam P.lam_gap
    (orderedGapDomain_subset_orderedDomain P.radius_pos.le hz)
    (orderedGapDomain_norm_separation hz) P.radius_large).choose

theorem localFamily_spec (z : Point d) (hz : z∈OrderedGapDomain d P.radius) :
    (P.localFamily z hz).AnalyticAt z ∧
      AnalyticAt ℂ ((P.localFamily z hz).weightedSolution P.radius_pos P.gap_pos P.lam P.lam_gap) z ∧
      ∀ᶠw in 𝓝 z,(P.localFamily z hz).Matches P.D (shiftedDirection P.sign) P.sign w ∧
        ‖(P.localFamily z hz).effectiveOperator P.radius_pos P.gap_pos P.lam P.lam_gap w‖<1 :=
  (P.D.exists_analytic_weightedRadialSolution (shiftedDirection P.sign) P.sign
    P.radius_pos P.gap_pos P.lam P.lam_gap
    (orderedGapDomain_subset_orderedDomain P.radius_pos.le hz)
    (orderedGapDomain_norm_separation hz) P.radius_large).choose_spec

/-- The choice-independent weighted family on the whole large chamber. -/
def weightedFamily (z : Point d) : RadialBanach d P.radius := by
  classical
  exact if hz : z∈OrderedGapDomain d P.radius then
    (P.localFamily z hz).weightedSolution P.radius_pos P.gap_pos P.lam P.lam_gap z else 0

def emptyFamily (z : Point d) : EmptyBanach P.radius := by
  classical
  exact if hz : z∈OrderedGapDomain d P.radius then
    (P.localFamily z hz).normalizedEmpty P.radius_pos P.gap_pos P.lam P.lam_gap z
  else BoundedContinuousFunction.const _ 1

def nonemptyFamily (z : Point d) : RadialBanach d P.radius :=
  boundedUnweight P.radius_pos (P.weightedFamily z)

/-- The locally constructed actual solutions agree with the canonical family
on one neighborhood, by equality of their true coefficient blocks. -/
theorem eventually_localFamily_eq {z : Point d} (hz : z∈OrderedGapDomain d P.radius) :
    ∀ᶠw in 𝓝 z,
      (P.localFamily z hz).weightedSolution P.radius_pos P.gap_pos P.lam P.lam_gap w=P.weightedFamily w ∧
      (P.localFamily z hz).normalizedEmpty P.radius_pos P.gap_pos P.lam P.lam_gap w=P.emptyFamily w := by
  filter_upwards [(orderedGapDomain_isOpen d P.radius).mem_nhds hz,
    (P.localFamily_spec z hz).2.2] with w hw hf
  obtain ⟨hZ,h0,_⟩ := (P.localFamily z hz).weightedSolution_eq_of_matches (P.localFamily w hw)
    P.D (shiftedDirection P.sign) P.sign P.radius_pos P.gap_pos P.lam P.lam_gap
    hf.1 (P.localFamily_spec w hw).2.2.self_of_nhds.1
  exact ⟨by simpa only [weightedFamily,dif_pos hw] using hZ,
    by simpa only [emptyFamily,dif_pos hw] using h0⟩

theorem analyticOnNhd_weightedFamily : AnalyticOnNhd ℂ P.weightedFamily (OrderedGapDomain d P.radius) := by
  intro z hz
  exact (P.localFamily_spec z hz).2.1.congr ((P.eventually_localFamily_eq hz).mono (fun _ h => h.1))

theorem analyticOnNhd_emptyFamily : AnalyticOnNhd ℂ P.emptyFamily (OrderedGapDomain d P.radius) := by
  intro z hz
  have hf := P.localFamily_spec z hz
  exact ((P.localFamily z hz).analyticAt_normalizedEmpty P.radius_pos P.gap_pos P.lam P.lam_gap
    hf.1 hf.2.2.self_of_nhds.2).congr ((P.eventually_localFamily_eq hz).mono (fun _ h => h.2))

theorem analyticOnNhd_nonemptyFamily : AnalyticOnNhd ℂ P.nonemptyFamily (OrderedGapDomain d P.radius) := by
  intro z hz
  have hU : AnalyticAt ℂ (fun _ : Point d => complexUnweightOperator (E:=RadialVector d) P.radius_pos) z := analyticAt_const
  exact analyticAt_clm_apply hU (P.analyticOnNhd_weightedFamily z hz)

/-- The actual scalar normalized germ on the large chamber. -/
def normalizedGerm (z : Point d) : ℂ := P.emptyFamily z ⟨P.radius,le_rfl⟩ ()

theorem analyticOnNhd_normalizedGerm : AnalyticOnNhd ℂ P.normalizedGerm (OrderedGapDomain d P.radius) := by
  intro z hz
  let L : EmptyBanach P.radius →L[ℂ] ℂ := (ContinuousLinearMap.proj (R:=ℂ) () : EmptyVector →L[ℂ] ℂ).comp
    (BoundedContinuousFunction.evalCLM (𝕜:=ℂ) (⟨P.radius,le_rfl⟩ : Tail P.radius))
  have hL : AnalyticAt ℂ L (P.emptyFamily z) := L.analyticAt _
  exact hL.comp (f:=P.emptyFamily) (P.analyticOnNhd_emptyFamily z hz)

theorem families_limits {z : Point d} (hz : z∈OrderedGapDomain d P.radius) :
    Tendsto (P.emptyFamily z) atTop (𝓝 (1:EmptyVector)) ∧
      Tendsto (P.nonemptyFamily z) atTop (𝓝 0) := by
  simpa only [emptyFamily,weightedFamily,nonemptyFamily,dif_pos hz,
    RadialOperatorFamily.normalizedNonempty] using
    (P.localFamily z hz).normalized_components_limits P.radius_pos P.gap_pos P.lam P.lam_gap z

theorem families_reciprocal_bound {z : Point d} (hz : z∈OrderedGapDomain d P.radius) :
    ∃B : ℝ,0≤B ∧ ∀t : Tail P.radius,
      ‖P.emptyFamily z t-1‖≤B/t.val ∧ ‖P.nonemptyFamily z t‖≤B/t.val := by
  simpa only [emptyFamily,weightedFamily,nonemptyFamily,dif_pos hz,
    RadialOperatorFamily.normalizedNonempty] using
    (P.localFamily z hz).normalized_components_bound P.radius_pos P.gap_pos P.lam P.lam_gap z

end RadialConstructionData
end BourgadeHuang.CMS
