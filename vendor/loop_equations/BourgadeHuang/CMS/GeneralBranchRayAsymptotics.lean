import BourgadeHuang.CMS.GeneralBranches
import BourgadeHuang.CMS.RayIndependence

/-! Actual large-ray asymptotics of the general-coupling holomorphic branch
factors. Real powers arise from the logarithmic gap exponents. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-- Linear exponential phase on an arbitrary fixed ray. -/
def generalRayPhase (c : Fin d → ℂ) (σ : Fin d → Sign) (v : Point d) : ℂ :=
  Complex.I*∑i,c i*signValue (σ i)*v i

/-- Total (possibly nonintegral) homogeneity of the logarithmic prefactor. -/
def generalRayDegree (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign) : ℂ :=
  ∑p∈upperPairs d,couplingExponent β c σ p.1 p.2

/-- The nonzero direction-dependent branch coefficient. -/
def generalRayLogCoefficient (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (v : Point d) : ℂ :=
  ∑p∈upperPairs d,couplingExponent β c σ p.1 p.2*Complex.log (v p.2-v p.1)

/-- Exact positive-real scaling, including the true nonintegral homogeneity. -/
theorem generalBranchLog_scale (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (v : Point d) (hv : CollisionFree v) {r : ℝ} (hr : 0<r) :
    generalBranchLog β c σ (fun i=>(r:ℂ)*v i)=
      (r:ℂ)*generalRayPhase c σ v+(Real.log r:ℂ)*generalRayDegree β c σ+
        generalRayLogCoefficient β c σ v := by
  unfold generalBranchLog generalRayPhase generalRayDegree generalRayLogCoefficient
  have hg (p : Fin d × Fin d) (hp : p∈upperPairs d) :
      Complex.log ((r:ℂ)*v p.2-(r:ℂ)*v p.1)=
        (Real.log r:ℂ)+Complex.log (v p.2-v p.1) := by
    rw [←mul_sub,Complex.log_ofReal_mul hr]
    exact (hv.sub_ne_zero (ne_of_gt (Finset.mem_filter.mp hp).2))
  have hp : Complex.I*(∑i,c i*signValue (σ i)*((r:ℂ)*v i))=
      (r:ℂ)*(Complex.I*∑i,c i*signValue (σ i)*v i) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hs : (∑p∈upperPairs d,couplingExponent β c σ p.1 p.2*
        Complex.log ((r:ℂ)*v p.2-(r:ℂ)*v p.1))=
      (Real.log r:ℂ)*(∑p∈upperPairs d,couplingExponent β c σ p.1 p.2)+
        ∑p∈upperPairs d,couplingExponent β c σ p.1 p.2*Complex.log (v p.2-v p.1) := by
    calc
      _=∑p∈upperPairs d,(couplingExponent β c σ p.1 p.2*(Real.log r:ℂ)+
        couplingExponent β c σ p.1 p.2*Complex.log (v p.2-v p.1)) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hg p hp,mul_add]
      _=_ := by
        rw [Finset.sum_add_distrib,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro p hp
        ring
  rw [hp,hs]
  ring

/-- Exact norm formula for the quotient of two genuine branch factors. -/
theorem norm_generalBranch_quotient_scale (β : ℂ) (c : Fin d → ℂ)
    (σ τ : Fin d → Sign) (v : Point d) (hv : CollisionFree v) {r : ℝ} (hr : 0<r) :
    ‖generalBranch β c τ (fun i=>(r:ℂ)*v i)/generalBranch β c σ (fun i=>(r:ℂ)*v i)‖=
      Real.exp ((generalRayLogCoefficient β c τ v-generalRayLogCoefficient β c σ v).re)*
        r^((generalRayDegree β c τ-generalRayDegree β c σ).re)*
        Real.exp (r*(generalRayPhase c τ v-generalRayPhase c σ v).re) := by
  unfold generalBranch
  rw [←Complex.exp_sub,Complex.norm_exp,generalBranchLog_scale β c τ v hv hr,
    generalBranchLog_scale β c σ v hv hr,Real.rpow_def_of_pos hr]
  rw [←Real.exp_add,←Real.exp_add]
  congr 1
  simp only [Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  ring

/-- Every strictly lower exponential phase is suppressed, regardless of
its real (nonintegral) logarithmic power. -/
theorem tendsto_generalBranch_quotient_zero (β : ℂ) (c : Fin d → ℂ)
    (σ τ : Fin d → Sign) (v : Point d) (hv : CollisionFree v)
    (hrate : (generalRayPhase c τ v).re<(generalRayPhase c σ v).re) :
    Tendsto (fun r : ℝ=>generalBranch β c τ (fun i=>(r:ℂ)*v i)/
      generalBranch β c σ (fun i=>(r:ℂ)*v i)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  let p := (generalRayDegree β c τ-generalRayDegree β c σ).re
  let b := (generalRayPhase c σ v).re-(generalRayPhase c τ v).re
  have hb : 0<b := sub_pos.mpr hrate
  have hl := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p b hb).const_mul
    (Real.exp ((generalRayLogCoefficient β c τ v-generalRayLogCoefficient β c σ v).re))
  simp only [mul_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  rw [norm_generalBranch_quotient_scale β c σ τ v hv hr]
  simp only [p,b,Complex.sub_re,mul_assoc]
  congr 2
  congr 1
  ring

end BourgadeHuang.CMS
