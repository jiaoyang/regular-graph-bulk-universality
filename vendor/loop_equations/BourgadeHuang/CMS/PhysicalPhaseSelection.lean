import BourgadeHuang.CMS.PhysicalSectorialBasis

/-! Exponential growth selects the permitted phases of a genuine physical
sectorial expansion. The fractional powers and analytic corrections are
controlled by their proved ray formulas, rather than assumed asymptotics. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
variable {d : ℕ}

theorem ordered_scale_gaps {v : Point d} (hv : v∈OrderedDomain d) (R : ℝ) :
    ∀ᶠr : ℝ in atTop,(fun i=>(r:ℂ)*v i)∈OrderedGapDomain d R := by
  have hi (i j : Fin d) : ∀ᶠr : ℝ in atTop,
      i<j → R<((r:ℂ)*v j-(r:ℂ)*v i).re := by
    by_cases hij : i<j
    · have hp : 0<(v j-v i).re := by simpa only [Complex.sub_re] using sub_pos.mpr (hv i j hij)
      filter_upwards [eventually_gt_atTop (R/(v j-v i).re)] with r hr _
      have hh := (div_lt_iff₀ hp).mp hr
      simpa only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero,mul_sub] using hh
    · exact Filter.Eventually.of_forall (fun _ h=>False.elim (hij h))
  change ∀ᶠr : ℝ in atTop,∀i j,i<j → R<((r:ℂ)*v j-(r:ℂ)*v i).re
  exact Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (hi i))

/-- Exact reciprocal branch norm along a positively scaled ray. -/
theorem norm_inv_generalBranch_scale (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (v : Point d) (hv : CollisionFree v) {r : ℝ} (hr : 0<r) :
    ‖(generalBranch β c σ (fun i=>(r:ℂ)*v i))⁻¹‖=
      Real.exp (-(generalRayLogCoefficient β c σ v).re)*
        r^(-(generalRayDegree β c σ).re)*
        Real.exp (-r*(generalRayPhase c σ v).re) := by
  rw [generalBranch,←Complex.exp_neg,Complex.norm_exp,generalBranchLog_scale β c σ v hv hr,
    Real.rpow_def_of_pos hr,←Real.exp_add,←Real.exp_add]
  congr 1
  simp only [Complex.neg_re,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  ring

/-- Any strictly slower observable vanishes after normalization by the branch,
even with arbitrary real logarithmic degree. -/
theorem tendsto_inv_generalBranch_mul_zero_of_growth (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (v : Point d) (hv : CollisionFree v)
    (F : ℝ → ℂ) (M C : ℝ) (hrate : M<(generalRayPhase c σ v).re)
    (hbound : ∀ᶠr : ℝ in atTop,‖F r‖≤C*Real.exp (r*M)) :
    Tendsto (fun r : ℝ=>(generalBranch β c σ (fun i=>(r:ℂ)*v i))⁻¹*F r) atTop (𝓝 0) := by
  let K := Real.exp (-(generalRayLogCoefficient β c σ v).re)*C
  let p := -(generalRayDegree β c σ).re
  let b := (generalRayPhase c σ v).re-M
  have hb : 0<b := sub_pos.mpr hrate
  have hl := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p b hb).const_mul K
  simp only [mul_zero] at hl
  apply squeeze_zero_norm' _ hl
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with r hr hr0
  rw [norm_mul,norm_inv_generalBranch_scale β c σ v hv hr0]
  calc
    _≤(Real.exp (-(generalRayLogCoefficient β c σ v).re)*
      r^(-(generalRayDegree β c σ).re)*Real.exp (-r*(generalRayPhase c σ v).re))*
        (C*Real.exp (r*M)) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _=K*(r^p*Real.exp (-b*r)) := by
      simp only [K,p,b]
      rw [show -((generalRayPhase c σ v).re-M)*r=
        -r*(generalRayPhase c σ v).re+r*M by ring,Real.exp_add]
      ring

namespace RadialConstructionData
variable {β : ℝ} (hβ : 0<β) (c : Fin d → ℂ)
  (hc : ∀i,c i= -1 ∨ c i=(β:ℂ)/2)

/-- A maximal nonzero phase is recovered by an actual ray limit. -/
theorem physical_combination_dual_limit (v : Point d) (hv : v∈OrderedDomain d)
    (a : (Fin d → Sign) → ℂ) (σ : Fin d → Sign)
    (hmax : ∀τ,a τ≠0 → τ≠σ →
      (generalRayPhase c τ v).re<(generalRayPhase c σ v).re) :
    Tendsto (fun r : ℝ=>(generalBranch (β:ℂ) c σ (fun i=>(r:ℂ)*v i))⁻¹*
      (∑τ,a τ*physicalBranch hβ c τ hc (fun i=>(r:ℂ)*v i))) atTop (𝓝 (a σ)) := by
  classical
  have ht (τ : Fin d → Sign) : Tendsto (fun r : ℝ=>a τ*
      ((generalBranch (β:ℂ) c σ (fun i=>(r:ℂ)*v i))⁻¹*
        physicalBranch hβ c τ hc (fun i=>(r:ℂ)*v i))) atTop
      (𝓝 (if τ=σ then a σ else 0)) := by
    by_cases he : a τ=0
    · by_cases ht : τ=σ
      · subst τ
        simp only [he,zero_mul,if_true]
        exact tendsto_const_nhds
      · simp only [he,zero_mul,if_neg ht]
        exact tendsto_const_nhds
    by_cases ht : τ=σ
    · subst τ
      have hg := ((physical hβ c σ hc).normalizedGerm_tendsto_one_of_gaps
        (ordered_scale_gaps hv)).const_mul (a σ)
      simpa only [physicalBranch,←mul_assoc,inv_mul_cancel₀ (generalBranch_ne_zero _ _ _ _),
        one_mul,mul_one,if_true] using hg
    · have hq := tendsto_generalBranch_quotient_zero (β:ℂ) c σ τ v
        (orderedDomain_collisionFree hv) (hmax τ he ht)
      have hg := (physical hβ c τ hc).normalizedGerm_tendsto_one_of_gaps (ordered_scale_gaps hv)
      have hh := (hq.mul hg).const_mul (a τ)
      simp only [zero_mul,mul_zero] at hh
      rw [if_neg ht]
      apply hh.congr'
      exact Filter.Eventually.of_forall (fun r=>by
        simp only [physicalBranch,div_eq_mul_inv,if_neg ht]
        ring)
  have hs := tendsto_finset_sum Finset.univ (fun τ _=>ht τ)
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true] at hs
  convert hs using 1
  funext r
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  ring

/-- Observable exponential growth forbids every larger phase in a genuine
physical expansion, when the direction separates the finitely many rates. -/
theorem physical_expansion_phase_support (v : Point d) (hv : v∈OrderedDomain d)
    (hinj : Function.Injective (fun σ : Fin d → Sign=>(generalRayPhase c σ v).re))
    (a : (Fin d → Sign) → ℂ) (F : ℝ → ℂ) (M C : ℝ)
    (hexp : ∀ᶠr : ℝ in atTop,F r=∑τ,a τ*physicalBranch hβ c τ hc (fun i=>(r:ℂ)*v i))
    (hbound : ∀ᶠr : ℝ in atTop,‖F r‖≤C*Real.exp (r*M)) :
    ∀σ,M<(generalRayPhase c σ v).re → a σ=0 := by
  classical
  intro σ hσ
  by_contra ha
  let s : Finset (Fin d → Sign) := Finset.univ.filter (fun τ=>a τ≠0)
  have hs : s.Nonempty := ⟨σ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
  obtain ⟨τ,hτ,hmax⟩ := s.exists_max_image (fun τ=>(generalRayPhase c τ v).re) hs
  have hτa : a τ≠0 := (Finset.mem_filter.mp hτ).2
  have hrate : M<(generalRayPhase c τ v).re := hσ.trans_le
    (hmax σ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩))
  have hm (ρ : Fin d → Sign) (hρ : a ρ≠0) (hne : ρ≠τ) :
      (generalRayPhase c ρ v).re<(generalRayPhase c τ v).re :=
    lt_of_le_of_ne (hmax ρ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hρ⟩))
      (fun hh=>hne (hinj hh))
  have hl := physical_combination_dual_limit hβ c hc v hv a τ hm
  have hl' := tendsto_inv_generalBranch_mul_zero_of_growth (β:ℂ) c τ v
    (orderedDomain_collisionFree hv) F M C hrate hbound
  have hl'' := hl'.congr' (hexp.mono (fun r hr=>congrArg
    (fun w=>(generalBranch (β:ℂ) c τ (fun i=>(r:ℂ)*v i))⁻¹*w) hr))
  exact hτa (tendsto_nhds_unique hl hl'')

end RadialConstructionData
end BourgadeHuang.CMS
