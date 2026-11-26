import BourgadeHuang.CMS.TwoScaleBranchLimits

/-! Positive-degree elimination and zero-degree normalization for the
constructed physical sectorial family on the genuine two-scale rays. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.CMS.RadialConstructionData
variable {d : ℕ} {β : ℝ} (hβ : 0<β) (c : Fin d → ℂ)
  (hc : ∀i,c i= -1 ∨ c i=(β:ℂ)/2)

theorem physical_coefficient_zero_of_twoScale_bounded
    (ξ δ : Fin d → ℝ) (σ : Fin d → Sign) (k : ℕ) (hξ : StrictMono ξ)
    (b : (Fin d → Sign) → ℂ)
    (hsep : ∀τ,b τ≠0 → τ≠σ → ∃e : ℝ,0<e ∧ ∀ᶠr : ℝ in atTop,
      (generalRayPhase c τ (twoScaleRay ξ δ σ k r)-
        generalRayPhase c σ (twoScaleRay ξ δ σ k r)).re≤ -e*r)
    (F : ℝ → ℂ)
    (hexp : ∀ᶠr : ℝ in atTop,F r=∑τ,b τ*physicalBranch hβ c τ hc (twoScaleRay ξ δ σ k r))
    (hphase : ∀ᶠr : ℝ in atTop,(generalRayPhase c σ (twoScaleRay ξ δ σ k r)).re=0)
    (hdegree : 0<(generalRayDegree (β:ℂ) c σ).re)
    (hbound : ∃C : ℝ,∀ᶠr : ℝ in atTop,‖F r‖≤C) : b σ=0 := by
  obtain ⟨C,hC⟩ := hbound
  have hp : 0<(((k+2:ℕ):ℂ)*generalRayDegree (β:ℂ) c σ).re := by
    simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
    positivity
  have hF := tendsto_normalized_bounded_zero
    (fun r=>generalRayPhase c σ (twoScaleRay ξ δ σ k r))
    (((k+2:ℕ):ℂ)*generalRayDegree (β:ℂ) c σ) hp F C hphase hC
  have he := physical_coefficient_eq_of_twoScale_limit hβ c hc ξ δ σ k hξ b hsep F hexp hF
  simpa only [zero_div] using he

theorem physical_coefficient_eq_inv_of_twoScale_phase_limit
    (ξ δ : Fin d → ℝ) (σ : Fin d → Sign) (k : ℕ) (hξ : StrictMono ξ)
    (b : (Fin d → Sign) → ℂ)
    (hsep : ∀τ,b τ≠0 → τ≠σ → ∃e : ℝ,0<e ∧ ∀ᶠr : ℝ in atTop,
      (generalRayPhase c τ (twoScaleRay ξ δ σ k r)-
        generalRayPhase c σ (twoScaleRay ξ δ σ k r)).re≤ -e*r)
    (F : ℝ → ℂ)
    (hexp : ∀ᶠr : ℝ in atTop,F r=∑τ,b τ*physicalBranch hβ c τ hc (twoScaleRay ξ δ σ k r))
    (hdegree : generalRayDegree (β:ℂ) c σ=0)
    (hF : Tendsto (fun r : ℝ=>Complex.exp (-generalRayPhase c σ (twoScaleRay ξ δ σ k r))*F r)
      atTop (𝓝 1)) : b σ=(twoScaleBranchConstant (β:ℂ) c σ)⁻¹ := by
  have he := physical_coefficient_eq_of_twoScale_limit hβ c hc ξ δ σ k hξ b hsep F hexp
    (by simpa only [hdegree,mul_zero,sub_zero] using hF)
  simpa only [one_div] using he

end BourgadeHuang.CMS.RadialConstructionData
