import BourgadeHuang.CMS.PairScaledBranchLimits

/-! Extraction of a single coefficient of the actual CMS expansion on
polynomially separated rays. Strict phase decay dominates every fractional
gap power; the complex leading constant is retained explicitly. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000

theorem tendsto_exp_log_power_zero_of_re_bound (f : ℝ → ℂ) (p : ℂ)
    {a : ℝ} (ha : 0<a) (hb : ∀ᶠr : ℝ in atTop,(f r).re≤ -a*r) :
    Tendsto (fun r : ℝ=>Complex.exp (f r+(Real.log r:ℂ)*p)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p.re a ha)
  filter_upwards [hb,eventually_gt_atTop (0:ℝ)] with r hr hr0
  rw [Complex.norm_exp,Real.rpow_def_of_pos hr0,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  linarith

namespace RadialConstructionData
variable {d : ℕ} {β : ℝ} (hβ : 0<β) (c : Fin d → ℂ)
  (hc : ∀i,c i= -1 ∨ c i=(β:ℂ)/2)

/-- Every competitor with a strict exponential deficit disappears under
normalization by the distinguished branch's true phase and pair degree. -/
theorem tendsto_competing_physicalBranch_pair_normalization
    (σ τ : Fin d → Sign) (n : Fin d × Fin d → ℕ) (z : ℝ → Point d)
    (a : Fin d × Fin d → ℂ)
    (hgap : ∀R : ℝ,∀ᶠr : ℝ in atTop,z r∈OrderedGapDomain d R)
    (hlim : ∀p∈upperPairs d,Tendsto (fun r : ℝ=>(z r p.2-z r p.1)/(r:ℂ)^n p)
      atTop (𝓝 (a p)))
    (ha : ∀p∈upperPairs d,a p∈Complex.slitPlane)
    {b : ℝ} (hb : 0<b)
    (hphase : ∀ᶠr : ℝ in atTop,
      (generalRayPhase c τ (z r)-generalRayPhase c σ (z r)).re≤ -b*r) :
    Tendsto (fun r : ℝ=>
      Complex.exp (-generalRayPhase c σ (z r)-(Real.log r:ℂ)*generalPairDegree (β:ℂ) c σ n)*
        physicalBranch hβ c τ hc (z r)) atTop (𝓝 0) := by
  have he := tendsto_exp_log_power_zero_of_re_bound
    (fun r=>generalRayPhase c τ (z r)-generalRayPhase c σ (z r))
    (generalPairDegree (β:ℂ) c τ n-generalPairDegree (β:ℂ) c σ n) hb hphase
  have hl := he.mul (tendsto_physicalBranch_pair_normalization hβ c hc τ n z a hgap hlim ha)
  simp only [zero_mul] at hl
  apply hl.congr'
  exact Filter.Eventually.of_forall (fun r=>by
    dsimp only
    rw [←mul_assoc,←Complex.exp_add]
    congr 2
    ring)

/-- Dual extraction from the complete genuine branch family. -/
theorem physical_pair_combination_limit
    (σ : Fin d → Sign) (n : Fin d × Fin d → ℕ) (z : ℝ → Point d)
    (a : Fin d × Fin d → ℂ)
    (hgap : ∀R : ℝ,∀ᶠr : ℝ in atTop,z r∈OrderedGapDomain d R)
    (hlim : ∀p∈upperPairs d,Tendsto (fun r : ℝ=>(z r p.2-z r p.1)/(r:ℂ)^n p)
      atTop (𝓝 (a p)))
    (ha : ∀p∈upperPairs d,a p∈Complex.slitPlane)
    (b : (Fin d → Sign) → ℂ)
    (hsep : ∀τ,b τ≠0 → τ≠σ → ∃e : ℝ,0<e ∧ ∀ᶠr : ℝ in atTop,
      (generalRayPhase c τ (z r)-generalRayPhase c σ (z r)).re≤ -e*r) :
    Tendsto (fun r : ℝ=>
      Complex.exp (-generalRayPhase c σ (z r)-(Real.log r:ℂ)*generalPairDegree (β:ℂ) c σ n)*
        (∑τ,b τ*physicalBranch hβ c τ hc (z r))) atTop
      (𝓝 (b σ*generalPairLeadingConstant (β:ℂ) c σ a)) := by
  classical
  have ht (τ : Fin d → Sign) : Tendsto (fun r : ℝ=>b τ*
      (Complex.exp (-generalRayPhase c σ (z r)-(Real.log r:ℂ)*generalPairDegree (β:ℂ) c σ n)*
        physicalBranch hβ c τ hc (z r))) atTop
      (𝓝 (if τ=σ then b σ*generalPairLeadingConstant (β:ℂ) c σ a else 0)) := by
    by_cases ht : τ=σ
    · subst τ
      simpa only [if_true] using
        (tendsto_physicalBranch_pair_normalization hβ c hc σ n z a hgap hlim ha).const_mul (b σ)
    rw [if_neg ht]
    by_cases hb : b τ=0
    · simpa only [hb,zero_mul] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ=>(0:ℂ)) atTop (𝓝 0))
    obtain ⟨e,he,hphase⟩ := hsep τ hb ht
    simpa only [mul_zero] using
      (tendsto_competing_physicalBranch_pair_normalization hβ c hc σ τ n z a
        hgap hlim ha he hphase).const_mul (b τ)
  have hs := tendsto_finset_sum Finset.univ (fun τ _=>ht τ)
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true] at hs
  convert hs using 1
  funext r
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  ring

/-- The coefficient is fixed by the normalized observable limit. -/
theorem physical_coefficient_eq_of_pair_limit
    (σ : Fin d → Sign) (n : Fin d × Fin d → ℕ) (z : ℝ → Point d)
    (a : Fin d × Fin d → ℂ)
    (hgap : ∀R : ℝ,∀ᶠr : ℝ in atTop,z r∈OrderedGapDomain d R)
    (hlim : ∀p∈upperPairs d,Tendsto (fun r : ℝ=>(z r p.2-z r p.1)/(r:ℂ)^n p)
      atTop (𝓝 (a p)))
    (ha : ∀p∈upperPairs d,a p∈Complex.slitPlane)
    (b : (Fin d → Sign) → ℂ)
    (hsep : ∀τ,b τ≠0 → τ≠σ → ∃e : ℝ,0<e ∧ ∀ᶠr : ℝ in atTop,
      (generalRayPhase c τ (z r)-generalRayPhase c σ (z r)).re≤ -e*r)
    (F : ℝ → ℂ) (hexp : ∀ᶠr : ℝ in atTop,F r=∑τ,b τ*physicalBranch hβ c τ hc (z r))
    {L : ℂ} (hF : Tendsto (fun r : ℝ=>
      Complex.exp (-generalRayPhase c σ (z r)-(Real.log r:ℂ)*generalPairDegree (β:ℂ) c σ n)*F r)
      atTop (𝓝 L)) : b σ=L/generalPairLeadingConstant (β:ℂ) c σ a := by
  have he := (physical_pair_combination_limit hβ c hc σ n z a hgap hlim ha b hsep).congr'
    (hexp.mono (fun r hr=>congrArg
      (fun w=>Complex.exp (-generalRayPhase c σ (z r)-
        (Real.log r:ℂ)*generalPairDegree (β:ℂ) c σ n)*w) hr.symm))
  apply (eq_div_iff (generalPairLeadingConstant_ne_zero _ _ _ _)).mpr
  exact tendsto_nhds_unique he hF

end RadialConstructionData
end BourgadeHuang.CMS
