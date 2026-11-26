import BourgadeHuang.CMS.PhysicalDominatingRays
import BourgadeHuang.CMS.PhysicalSectorialSolution
import BourgadeHuang.CMS.CanonicalGapNormalization

/-! Genuine linear independence of all physical sectorial branches. Actual
large-gap normalization and strict exponential phase separation supply the
dual limits; no independence or asymptotic premise is imposed. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1200000
namespace RadialConstructionData
variable {d : ℕ} {β : ℝ} (hβ : 0<β) (c : Fin d → ℂ)
  (hc : ∀i,c i= -1 ∨ c i=(β:ℂ)/2)

/-- One actual large chamber works for every one of the finitely many signs. -/
def physicalCommonRadius : ℝ := 1+∑σ : Fin d → Sign,(physical hβ c σ hc).radius

theorem physical_radius_le_common (σ : Fin d → Sign) :
    (physical hβ c σ hc).radius≤physicalCommonRadius hβ c hc := by
  exact (Finset.single_le_sum (fun τ _=>(physical hβ c τ hc).radius_pos.le)
    (Finset.mem_univ σ)).trans (le_add_of_nonneg_left zero_le_one)

theorem physical_common_subset (σ : Fin d → Sign) :
    OrderedGapDomain d (physicalCommonRadius hβ c hc)⊆
      OrderedGapDomain d (physical hβ c σ hc).radius := by
  intro z hz i j hij
  exact (physical_radius_le_common hβ c hc σ).trans_lt (hz i j hij)

/-- Actual dual evaluations for the complete constructed sectorial family. -/
theorem physicalBranch_dual_limit (σ τ : Fin d → Sign) :
    Tendsto (fun r : ℝ=>
      (generalBranch (β:ℂ) c σ (fun i=>(r:ℂ)*dominantPhysicalDirection c σ i))⁻¹*
        physicalBranch hβ c τ hc (fun i=>(r:ℂ)*dominantPhysicalDirection c σ i)) atTop
      (𝓝 (if τ=σ then (1:ℂ) else 0)) := by
  have hg := (physical hβ c τ hc).normalizedGerm_tendsto_one_of_gaps
    (dominantPhysicalRay_gaps c σ)
  have hq : Tendsto (fun r : ℝ=>
      generalBranch (β:ℂ) c τ (fun i=>(r:ℂ)*dominantPhysicalDirection c σ i)/
        generalBranch (β:ℂ) c σ (fun i=>(r:ℂ)*dominantPhysicalDirection c σ i)) atTop
      (𝓝 (if τ=σ then (1:ℂ) else 0)) := by
    by_cases he : τ=σ
    · subst τ
      simpa only [div_self (generalBranch_ne_zero _ _ _ _),if_true] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ=>(1:ℂ)) atTop (𝓝 1))
    · simpa only [if_neg he] using tendsto_generalBranch_quotient_zero (β:ℂ) c σ τ
        (dominantPhysicalDirection c σ) (dominantPhysicalDirection_collisionFree c σ)
        (generalRayPhase_dominantPhysical_lt hβ c σ τ hc he)
  have hh := hq.mul hg
  simp only [mul_one] at hh
  convert hh using 1
  funext r
  unfold physicalBranch
  ring

/-- The actual branch restrictions to the common large chamber are linearly
independent, in every dimension and for every positive physical coupling. -/
theorem physicalBranch_linearIndependent_common :
    LinearIndependent ℂ (fun σ : Fin d → Sign=>
      fun z : OrderedGapDomain d (physicalCommonRadius hβ c hc)=>physicalBranch hβ c σ hc z.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha σ
  have hrel : ∀z∈OrderedGapDomain d (physicalCommonRadius hβ c hc),
      (∑τ,a τ*physicalBranch hβ c τ hc z)=0 := by
    intro z hz
    have hh := congrFun ha ⟨z,hz⟩
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using hh
  let v := dominantPhysicalDirection c σ
  let normer := fun r : ℝ=>(generalBranch (β:ℂ) c σ (fun i=>(r:ℂ)*v i))⁻¹
  have hlim : Tendsto (fun r : ℝ=>∑τ,a τ*(normer r*physicalBranch hβ c τ hc (fun i=>(r:ℂ)*v i)))
      atTop (𝓝 (a σ)) := by
    simpa only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] using
      tendsto_finset_sum Finset.univ (fun τ _=>(physicalBranch_dual_limit hβ c hc σ τ).const_mul (a τ))
  have he : ∀ᶠr : ℝ in atTop,
      (∑τ,a τ*(normer r*physicalBranch hβ c τ hc (fun i=>(r:ℂ)*v i)))=0 := by
    filter_upwards [dominantPhysicalRay_gaps c σ (physicalCommonRadius hβ c hc)] with r hr
    calc
      _=normer r*(∑τ,a τ*physicalBranch hβ c τ hc (fun i=>(r:ℂ)*v i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro τ hτ
        ring
      _=0 := by rw [hrel _ hr,mul_zero]
  exact tendsto_nhds_unique (hlim.congr' he) tendsto_const_nhds

end RadialConstructionData
end BourgadeHuang.CMS
