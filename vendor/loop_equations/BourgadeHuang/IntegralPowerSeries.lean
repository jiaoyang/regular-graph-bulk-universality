import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Integration of uniformly dominated genuine multivariate power series.
This supplies joint analyticity, rather than only coordinate derivatives. -/
noncomputable section
open scoped Topology BigOperators NNReal ENNReal
open MeasureTheory Filter
namespace BourgadeHuang

variable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure Ω}

def integralFormalMultilinearSeries (p : Ω → FormalMultilinearSeries ℂ E ℂ) :
    FormalMultilinearSeries ℂ E ℂ := fun n => ∫ ω, p ω n ∂μ

/-- A common geometric coefficient majorant can be integrated before choosing
the parameters. Both the convergence radius and the actual sum are proved. -/
theorem hasFPowerSeriesOnBall_integral
    (F : Ω → E → ℂ) (p : Ω → FormalMultilinearSeries ℂ E ℂ)
    (x : E) (r : ℝ≥0) (hr : 0 < r)
    (hp : ∀ ω, HasFPowerSeriesOnBall (F ω) (p ω) x r)
    (hi : ∀ n, Integrable (fun ω => p ω n) μ)
    (g : Ω → ℝ) (hg : Integrable g μ) (hg0 : ∀ ω, 0 ≤ g ω)
    (hb : ∀ ω n, ‖p ω n‖ ≤ g ω / (r : ℝ)^n) :
    HasFPowerSeriesOnBall (fun z => ∫ ω, F ω z ∂μ)
      (integralFormalMultilinearSeries (μ := μ) p) x r := by
  have hr' : (0 : ℝ) < r := hr
  have hnorm (n : ℕ) : ‖∫ ω, p ω n ∂μ‖ ≤ (∫ ω, g ω ∂μ)/(r : ℝ)^n := by
    calc
      _ ≤ ∫ ω, ‖p ω n‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, g ω/(r : ℝ)^n ∂μ := integral_mono (hi n).norm (hg.div_const _) (fun ω => hb ω n)
      _ = _ := integral_div _ _
  refine ⟨?_, by exact_mod_cast hr, ?_⟩
  · apply FormalMultilinearSeries.le_radius_of_bound _ (∫ ω, g ω ∂μ)
    intro n
    exact (mul_le_mul_of_nonneg_right (hnorm n) (pow_nonneg hr'.le _)).trans_eq
      (div_mul_cancel₀ _ (pow_ne_zero _ hr'.ne'))
  · intro y hy
    have hyr : ‖y‖ < (r : ℝ) := by
      simpa only [Metric.emetric_ball_nnreal, Metric.mem_ball, dist_zero_right] using hy
    let a : ℝ := ‖y‖/(r : ℝ)
    have ha0 : 0 ≤ a := div_nonneg (norm_nonneg _) hr'.le
    have ha1 : a < 1 := (div_lt_one hr').mpr hyr
    let T : ℕ → Ω → ℂ := fun n ω => p ω n (fun _ => y)
    have hT (n : ℕ) : Integrable (T n) μ :=
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) ℂ (fun _ => y)).integrable_comp (hi n)
    have hTb (n : ℕ) (ω : Ω) : ‖T n ω‖ ≤ g ω*a^n := by
      calc
        _ ≤ ‖p ω n‖*‖y‖^n := by simpa [T] using (p ω n).le_opNorm (fun _ => y)
        _ ≤ (g ω/(r : ℝ)^n)*‖y‖^n :=
          mul_le_mul_of_nonneg_right (hb ω n) (pow_nonneg (norm_nonneg _) _)
        _ = _ := by dsimp [a]; rw [div_pow]; ring
    have hsum : Summable (fun n => ∫ ω, ‖T n ω‖ ∂μ) := by
      apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun ω => norm_nonneg _))
        (fun n => ?_) ((summable_geometric_of_lt_one ha0 ha1).mul_left (∫ ω, g ω ∂μ))
      calc
        _ ≤ ∫ ω, g ω*a^n ∂μ := integral_mono (hT n).norm (hg.mul_const _) (hTb n)
        _ = _ := integral_mul_const _ _
    have hs := hasSum_integral_of_summable_integral_norm hT hsum
    have he (ω : Ω) : (∑' n, T n ω) = F ω (x+y) := (hp ω).hasSum hy |>.tsum_eq
    simp_rw [he] at hs
    convert hs using 1
    funext n
    exact ContinuousMultilinearMap.integral_apply (hi n) (fun _ => y)

theorem analyticAt_integral_of_powerSeries
    (F : Ω → E → ℂ) (p : Ω → FormalMultilinearSeries ℂ E ℂ)
    (x : E) (r : ℝ≥0) (hr : 0 < r)
    (hp : ∀ ω, HasFPowerSeriesOnBall (F ω) (p ω) x r)
    (hi : ∀ n, Integrable (fun ω => p ω n) μ)
    (g : Ω → ℝ) (hg : Integrable g μ) (hg0 : ∀ ω, 0 ≤ g ω)
    (hb : ∀ ω n, ‖p ω n‖ ≤ g ω / (r : ℝ)^n) :
    AnalyticAt ℂ (fun z => ∫ ω, F ω z ∂μ) x :=
  ⟨integralFormalMultilinearSeries (μ := μ) p, r,
    hasFPowerSeriesOnBall_integral F p x r hr hp hi g hg hg0 hb⟩

end BourgadeHuang
