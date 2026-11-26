import BourgadeHuang.CMS.TwoScaleRays
import BourgadeHuang.CMS.PairScaledCoefficientLimits

/-! The distinguished branch on the actual two-scale rays. Its pair degree
reduces to a multiple of the signed-charge square, and its nonzero leading
constant depends only on the charges and sign pattern. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.CMS
variable {d : ℕ}

theorem couplingExponent_eq_zero_of_eq (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) {i j : Fin d} (h : σ i=σ j) :
    couplingExponent β c σ i j=0 := by
  unfold couplingExponent
  rw [h,←pow_two,signValue_sq,sub_self,mul_zero]

theorem generalPairDegree_twoScale_self (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (k : ℕ) :
    generalPairDegree β c σ (fun p=>twoScaleGapExponent k σ p.1 p.2)=
      (k+2:ℕ)*generalRayDegree β c σ := by
  unfold generalPairDegree generalRayDegree
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hs : σ p.1=σ p.2
  · rw [couplingExponent_eq_zero_of_eq β c σ hs,zero_mul,mul_zero]
  · simp only [twoScaleGapExponent,if_neg hs]
    ring

/-- Universal complex phase of the polynomial prefactor on a sign ray. -/
def twoScaleBranchConstant (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign) : ℂ :=
  generalPairLeadingConstant β c σ
    (fun p=>Complex.I*(signValue (σ p.2)-signValue (σ p.1)))

@[simp] theorem twoScaleBranchConstant_ne_zero (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) : twoScaleBranchConstant β c σ≠0 :=
  generalPairLeadingConstant_ne_zero _ _ _ _

theorem generalPairLeadingConstant_twoScale_self (β : ℂ) (c : Fin d → ℂ)
    (ξ δ : Fin d → ℝ) (σ : Fin d → Sign) :
    generalPairLeadingConstant β c σ (fun p=>twoScaleGapLimit ξ δ σ p.1 p.2)=
      twoScaleBranchConstant β c σ := by
  unfold generalPairLeadingConstant twoScaleBranchConstant
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hs : σ p.1=σ p.2
  · rw [couplingExponent_eq_zero_of_eq β c σ hs,zero_mul,zero_mul]
  · simp only [twoScaleGapLimit,if_neg hs]

/-- The branch normalization tends to zero against every bounded observable
when the true pair degree is positive and the phase has zero real part. -/
theorem tendsto_normalized_bounded_zero (phase : ℝ → ℂ) (p : ℂ)
    (hp : 0<p.re) (F : ℝ → ℂ) (C : ℝ)
    (hphase : ∀ᶠr : ℝ in atTop,(phase r).re=0)
    (hbound : ∀ᶠr : ℝ in atTop,‖F r‖≤C) :
    Tendsto (fun r : ℝ=>Complex.exp (-phase r-(Real.log r:ℂ)*p)*F r) atTop (𝓝 0) := by
  have hl := (tendsto_rpow_neg_atTop hp).mul_const C
  simp only [zero_mul] at hl
  apply squeeze_zero_norm' _ hl
  filter_upwards [hphase,hbound,eventually_gt_atTop (0:ℝ)] with r hpr hr hr0
  rw [norm_mul,Complex.norm_exp]
  have he : (-phase r-(Real.log r:ℂ)*p).re=Real.log r*(-p.re) := by
    simp only [Complex.sub_re,Complex.neg_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,hpr]
    ring
  rw [he,←Real.rpow_def_of_pos hr0]
  exact mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg hr0.le _)

namespace RadialConstructionData
variable {β : ℝ} (hβ : 0<β) (c : Fin d → ℂ)
  (hc : ∀i,c i= -1 ∨ c i=(β:ℂ)/2)

/-- Genuine dominant-branch asymptotic with its universal nonzero constant. -/
theorem physicalBranch_twoScale_dominant_limit
    (ξ δ : Fin d → ℝ) (σ : Fin d → Sign) (k : ℕ) (hξ : StrictMono ξ) :
    Tendsto (fun r : ℝ=>
      Complex.exp (-generalRayPhase c σ (twoScaleRay ξ δ σ k r)-
        (Real.log r:ℂ)*((k+2:ℕ)*generalRayDegree (β:ℂ) c σ))*
        physicalBranch hβ c σ hc (twoScaleRay ξ δ σ k r)) atTop
      (𝓝 (twoScaleBranchConstant (β:ℂ) c σ)) := by
  have hh := tendsto_physicalBranch_pair_normalization hβ c hc σ
    (fun p=>twoScaleGapExponent k σ p.1 p.2) (twoScaleRay ξ δ σ k)
    (fun p=>twoScaleGapLimit ξ δ σ p.1 p.2)
    (twoScaleRay_eventually_orderedGapDomain ξ δ σ k hξ)
    (fun p _=>tendsto_twoScaleRay_normalized_gap ξ δ σ k p.1 p.2)
    (fun p hp=>twoScaleGapLimit_mem_slitPlane ξ δ σ hξ (Finset.mem_filter.mp hp).2)
  simpa only [generalPairDegree_twoScale_self,generalPairLeadingConstant_twoScale_self] using hh

/-- A single coefficient is recovered on the concrete two-scale ray, once
the observable's normalized limit and the competitors' phase deficit are known. -/
theorem physical_coefficient_eq_of_twoScale_limit
    (ξ δ : Fin d → ℝ) (σ : Fin d → Sign) (k : ℕ) (hξ : StrictMono ξ)
    (b : (Fin d → Sign) → ℂ)
    (hsep : ∀τ,b τ≠0 → τ≠σ → ∃e : ℝ,0<e ∧ ∀ᶠr : ℝ in atTop,
      (generalRayPhase c τ (twoScaleRay ξ δ σ k r)-
        generalRayPhase c σ (twoScaleRay ξ δ σ k r)).re≤ -e*r)
    (F : ℝ → ℂ)
    (hexp : ∀ᶠr : ℝ in atTop,F r=∑τ,b τ*physicalBranch hβ c τ hc (twoScaleRay ξ δ σ k r))
    {L : ℂ} (hF : Tendsto (fun r : ℝ=>
      Complex.exp (-generalRayPhase c σ (twoScaleRay ξ δ σ k r)-
        (Real.log r:ℂ)*((k+2:ℕ)*generalRayDegree (β:ℂ) c σ))*F r)
      atTop (𝓝 L)) : b σ=L/twoScaleBranchConstant (β:ℂ) c σ := by
  apply (physical_coefficient_eq_of_pair_limit hβ c hc σ
    (fun p=>twoScaleGapExponent k σ p.1 p.2) (twoScaleRay ξ δ σ k)
    (fun p=>twoScaleGapLimit ξ δ σ p.1 p.2)
    (twoScaleRay_eventually_orderedGapDomain ξ δ σ k hξ)
    (fun p _=>tendsto_twoScaleRay_normalized_gap ξ δ σ k p.1 p.2)
    (fun p hp=>twoScaleGapLimit_mem_slitPlane ξ δ σ hξ (Finset.mem_filter.mp hp).2)
    b hsep F hexp ?_).trans (by rw [generalPairLeadingConstant_twoScale_self])
  simpa only [generalPairDegree_twoScale_self] using hF

end RadialConstructionData
end BourgadeHuang.CMS
