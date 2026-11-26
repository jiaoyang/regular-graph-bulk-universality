import BourgadeHuang.CMS.PhysicalSectorialBasis
import BourgadeHuang.CMS.GeneralBranchDegree

/-! Actual branch limits when different coordinate gaps have different
polynomial scales. This retains the complex branch constants and fractional
degrees needed in the orthogonal coefficient comparisons. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
variable {d : ℕ}

def generalPairDegree (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (n : Fin d × Fin d → ℕ) : ℂ :=
  ∑p∈upperPairs d,couplingExponent β c σ p.1 p.2*(n p:ℂ)

def generalPairLeadingConstant (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (a : Fin d × Fin d → ℂ) : ℂ :=
  Complex.exp (∑p∈upperPairs d,couplingExponent β c σ p.1 p.2*Complex.log (a p))

@[simp] theorem generalPairLeadingConstant_ne_zero (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (a : Fin d × Fin d → ℂ) :
    generalPairLeadingConstant β c σ a≠0 := Complex.exp_ne_zero _

/-- Exact normalization of every pair gap by its own positive real power. -/
theorem generalBranch_pair_normalization (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (n : Fin d × Fin d → ℕ) (z : Point d)
    (hz : CollisionFree z) {r : ℝ} (hr : 0<r) :
    Complex.exp (-generalRayPhase c σ z-(Real.log r:ℂ)*generalPairDegree β c σ n)*
      generalBranch β c σ z=
    Complex.exp (∑p∈upperPairs d,couplingExponent β c σ p.1 p.2*
      Complex.log ((z p.2-z p.1)/(r:ℂ)^n p)) := by
  have hl (p : Fin d × Fin d) (hp : p∈upperPairs d) :
      Complex.log (z p.2-z p.1)=(n p:ℂ)*(Real.log r:ℂ)+
        Complex.log ((z p.2-z p.1)/(r:ℂ)^n p) := by
    have hn := hz.sub_ne_zero (ne_of_gt (Finset.mem_filter.mp hp).2)
    have hrc : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have he : z p.2-z p.1=((r^n p:ℝ):ℂ)*((z p.2-z p.1)/(r:ℂ)^n p) := by
      rw [Complex.ofReal_pow]
      field_simp
    rw [he,Complex.log_ofReal_mul (pow_pos hr _)]
    · rw [Real.log_pow,Complex.ofReal_mul,Complex.ofReal_natCast]
      congr 1
      rw [Complex.ofReal_pow]
      field_simp
    · exact div_ne_zero hn (pow_ne_zero _ hrc)
  rw [generalBranch,←Complex.exp_add]
  congr 1
  change -generalRayPhase c σ z-(Real.log r:ℂ)*generalPairDegree β c σ n+
    (generalRayPhase c σ z+generalRayLogCoefficient β c σ z)=_
  unfold generalPairDegree generalRayLogCoefficient
  simp only [Finset.mul_sum]
  have he : (∑p∈upperPairs d,couplingExponent β c σ p.1 p.2*Complex.log (z p.2-z p.1))=
      (∑p∈upperPairs d,(Real.log r:ℂ)*(couplingExponent β c σ p.1 p.2*(n p:ℂ)))+
        ∑p∈upperPairs d,couplingExponent β c σ p.1 p.2*
          Complex.log ((z p.2-z p.1)/(r:ℂ)^n p) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hl p hp]
    ring
  rw [he]
  ring

/-- Every actual pairwise asymptotic yields the full complex leading branch
constant, including the specified logarithm branches. -/
theorem tendsto_generalBranch_pair_normalization (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (n : Fin d × Fin d → ℕ) (z : ℝ → Point d)
    (a : Fin d × Fin d → ℂ)
    (hz : ∀ᶠr : ℝ in atTop,CollisionFree (z r))
    (hlim : ∀p∈upperPairs d,Tendsto (fun r : ℝ=>(z r p.2-z r p.1)/(r:ℂ)^n p)
      atTop (𝓝 (a p)))
    (ha : ∀p∈upperPairs d,a p∈Complex.slitPlane) :
    Tendsto (fun r : ℝ=>
      Complex.exp (-generalRayPhase c σ (z r)-(Real.log r:ℂ)*generalPairDegree β c σ n)*
        generalBranch β c σ (z r)) atTop (𝓝 (generalPairLeadingConstant β c σ a)) := by
  have hl := (tendsto_finset_sum (upperPairs d) (fun p hp=>
    ((hlim p hp).clog (ha p hp)).const_mul (couplingExponent β c σ p.1 p.2))).cexp
  apply hl.congr'
  filter_upwards [hz,eventually_gt_atTop (0:ℝ)] with r hr hr0
  exact (generalBranch_pair_normalization β c σ n (z r) hr hr0).symm

namespace RadialConstructionData
variable {β : ℝ} (hβ : 0<β) (c : Fin d → ℂ)
  (hc : ∀i,c i= -1 ∨ c i=(β:ℂ)/2)

/-- The same leading constants hold for the genuine CMS solutions, since
their constructed analytic correction tends to one as the real gaps grow. -/
theorem tendsto_physicalBranch_pair_normalization
    (σ : Fin d → Sign) (n : Fin d × Fin d → ℕ) (z : ℝ → Point d)
    (a : Fin d × Fin d → ℂ)
    (hgap : ∀R : ℝ,∀ᶠr : ℝ in atTop,z r∈OrderedGapDomain d R)
    (hlim : ∀p∈upperPairs d,Tendsto (fun r : ℝ=>(z r p.2-z r p.1)/(r:ℂ)^n p)
      atTop (𝓝 (a p)))
    (ha : ∀p∈upperPairs d,a p∈Complex.slitPlane) :
    Tendsto (fun r : ℝ=>
      Complex.exp (-generalRayPhase c σ (z r)-(Real.log r:ℂ)*generalPairDegree (β:ℂ) c σ n)*
        physicalBranch hβ c σ hc (z r)) atTop
      (𝓝 (generalPairLeadingConstant (β:ℂ) c σ a)) := by
  have hz : ∀ᶠr : ℝ in atTop,CollisionFree (z r) :=
    (hgap 0).mono (fun r hr=>orderedDomain_collisionFree
      (orderedGapDomain_subset_orderedDomain le_rfl hr))
  have hl := (tendsto_generalBranch_pair_normalization (β:ℂ) c σ n z a hz hlim ha).mul
    ((physical hβ c σ hc).normalizedGerm_tendsto_one_of_gaps hgap)
  simpa only [physicalBranch,mul_assoc,mul_one] using hl

end RadialConstructionData
end BourgadeHuang.CMS
