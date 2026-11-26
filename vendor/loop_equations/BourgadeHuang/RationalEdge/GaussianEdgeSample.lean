import BourgadeHuang.RationalEdge.GaussianEdgeLoop
import BourgadeHuang.RationalBulk.GaussianBetaSample
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! All dimensions of the genuine Gaussian beta ensemble in soft-edge coordinates. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk

def gaussianEdgeScale (N : ℕ) : ℝ := (N+1:ℝ) ^ (1/3:ℝ)

theorem gaussianEdgeScale_pos (N : ℕ) : 0<gaussianEdgeScale N := by
  apply Real.rpow_pos_of_pos
  positivity

theorem gaussianEdgeScale_cube (N : ℕ) : gaussianEdgeScale N ^ 3 = (N+1:ℝ) := by
  unfold gaussianEdgeScale
  rw [←Real.rpow_mul_natCast (by positivity)]
  norm_num

theorem gaussianEdgeScale_tendsto : Tendsto gaussianEdgeScale atTop atTop := by
  exact (tendsto_rpow_atTop (show (0:ℝ)<1/3 by norm_num)).comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

theorem gaussianEdgeScale_inv_tendsto :
    Tendsto (fun N => (gaussianEdgeScale N)⁻¹) atTop (𝓝 0) :=
  gaussianEdgeScale_tendsto.inv_tendsto_atTop

def gaussianBetaEdgeState (N : ℕ) (ω : GaussianBetaSpace) : AnchoredCountingState :=
  finiteEdgeState (gaussianEdgeScale N) (ω N)

theorem measurable_gaussianBetaEdgeState (N : ℕ) : Measurable (gaussianBetaEdgeState N) :=
  (measurable_finiteEdgeState (N+1) (gaussianEdgeScale N)).comp (measurable_pi_apply N)

theorem gaussianBetaEdgeState_moment (β : ℝ) (hβ : 0<β) (N q : ℕ) :
    Integrable (fun ω => ‖(gaussianBetaEdgeState N ω).val.2‖^q) (gaussianBetaProduct β hβ) := by
  exact integrable_microscopicResolvent_norm_pow
    (fun i => ((measurable_pi_apply i).comp
      (measurable_edgeParticles (N+1) (gaussianEdgeScale N))).comp (measurable_pi_apply N))
    (-gaussianEdgeScale N) (by simp) q

/-- The point measure is exactly the reflected soft-edge rescaling of every
finite Gaussian beta particle, centered at 2(N+1). -/
@[simp] theorem gaussianBetaEdgeState_measure (N : ℕ) (ω : GaussianBetaSpace) :
    (gaussianBetaEdgeState N ω).val.1.measure =
      ∑ i,Measure.dirac ((ω N i - 2*((N+1:ℕ):ℝ))/gaussianEdgeScale N) := rfl

end BourgadeHuang.RationalEdge
