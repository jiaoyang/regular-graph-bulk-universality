import BourgadeHuang.CMS.AnalyticNormalizedRadial

/-! The physical-charge sectorial system supplies every hypothesis of the
holomorphic normalized radial construction, including the gap and radius. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace SectorialData
variable {d : ℕ}

/-- An explicit radius making the actual eliminated Volterra map contractive. -/
def analyticRadius (D : SectorialData d) (ω : Point d) (a : ℝ) : ℝ :=
  triangularInverseBound a (RadialOperatorFamily.blockBound D ω) (d+1)*a⁻¹*
    (RadialOperatorFamily.blockBound D ω*RadialOperatorFamily.blockBound D ω+
      RadialOperatorFamily.blockBound D ω)+1

theorem analyticRadius_pos (D : SectorialData d) (ω : Point d) {a : ℝ} (ha : 0<a) :
    0<D.analyticRadius ω a := by
  have hM := (RadialOperatorFamily.blockBound_pos D ω).le
  have hG := triangularInverseBound_nonneg ha.le hM (d+1)
  unfold analyticRadius
  positivity

/-- The actual finite-charge gap, stated in the form used by the free kernel. -/
theorem physical_analytic_gap {β : ℝ} (hβ : 0<β) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hc : ∀i,c i=-1 ∨ c i=(β:ℂ)/2) :
    ∀S : NonemptySubset d,min 2 β/2≤
      ((general (β:ℂ) c σ).principalDiagonal (shiftedDirection (physicalRaySign c σ)) S.val).re := by
  intro S
  have h := principalDiagonal_general_gap hβ c σ hc S.val S.property
  have hp : 0<min 2 β := lt_min (by norm_num) hβ
  linarith

theorem physical_halfGap_pos {β : ℝ} (hβ : 0<β) : 0<min 2 β/2 := by positivity

/-- A genuine holomorphic normalized radial family at the explicit radius.
The resulting family has the exact ODEs and limits proved in
`RadialOperatorFamily.normalized_component_equations` and
`RadialOperatorFamily.normalized_components_limits`. -/
theorem exists_analytic_normalizedRadial_at_radius
    (D : SectorialData d) (σ : Fin d → Sign) {a : ℝ} (ha : 0<a)
    (lam : NonemptySubset d → ℂ) (hlam : ∀S,a≤(lam S).re)
    {z : Point d} (hz : z∈OrderedDomain d)
    (hsep : ∀i j,i≠j→D.analyticRadius (shiftedDirection σ) a≤‖z i-z j‖) :
    let R := D.analyticRadius (shiftedDirection σ) a
    let hR := D.analyticRadius_pos (shiftedDirection σ) ha
    ∃F : RadialOperatorFamily d R,F.AnalyticAt z ∧
      AnalyticAt ℂ (F.normalizedEmpty hR ha lam hlam) z ∧
      AnalyticAt ℂ (F.normalizedNonempty hR ha lam hlam) z ∧
      ∀ᶠw in 𝓝 z,F.Matches D (shiftedDirection σ) σ w ∧
        ‖F.effectiveOperator hR ha lam hlam w‖<1 := by
  dsimp only
  obtain ⟨F,hF,hZ,hmatch⟩ := D.exists_analytic_weightedRadialSolution (shiftedDirection σ) σ
    (D.analyticRadius_pos (shiftedDirection σ) ha) ha lam hlam hz hsep
    (lt_add_one _)
  have hs := hmatch.self_of_nhds.2
  exact ⟨F,hF,F.analyticAt_normalizedEmpty _ _ _ _ hF hs,
    F.analyticAt_normalizedNonempty _ _ _ _ hF hs,hmatch⟩

/-- For β>0 and the article's physical charges, the gap and radius are proved
internally. The normalized analytic radial family is genuinely constructed. -/
theorem exists_physical_analytic_normalizedRadial {β : ℝ} (hβ : 0<β)
    (c : Fin d → ℂ) (σ : Fin d → Sign) (hc : ∀i,c i=-1 ∨ c i=(β:ℂ)/2)
    {z : Point d} (hz : z∈OrderedDomain d)
    (hsep : ∀i j,i≠j→(general (β:ℂ) c σ).analyticRadius
      (shiftedDirection (physicalRaySign c σ)) (min 2 β/2)≤‖z i-z j‖) :
    let D := general (β:ℂ) c σ
    let τ := physicalRaySign c σ
    let a := min 2 β/2
    let R := D.analyticRadius (shiftedDirection τ) a
    let hR := D.analyticRadius_pos (shiftedDirection τ) (physical_halfGap_pos hβ)
    let lam := fun S : NonemptySubset d => D.principalDiagonal (shiftedDirection τ) S.val
    let hlam := physical_analytic_gap hβ c σ hc
    ∃F : RadialOperatorFamily d R,F.AnalyticAt z ∧
      AnalyticAt ℂ (F.normalizedEmpty hR (physical_halfGap_pos hβ) lam hlam) z ∧
      AnalyticAt ℂ (F.normalizedNonempty hR (physical_halfGap_pos hβ) lam hlam) z ∧
      ∀ᶠw in 𝓝 z,F.Matches D (shiftedDirection τ) τ w ∧
        ‖F.effectiveOperator hR (physical_halfGap_pos hβ) lam hlam w‖<1 := by
  exact (general (β:ℂ) c σ).exists_analytic_normalizedRadial_at_radius
    (physicalRaySign c σ) (physical_halfGap_pos hβ)
    (fun S => (general (β:ℂ) c σ).principalDiagonal (shiftedDirection (physicalRaySign c σ)) S.val)
    (physical_analytic_gap hβ c σ hc) hz hsep

end SectorialData
end BourgadeHuang.CMS
