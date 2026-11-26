import BourgadeHuang.IntegralPowerSeries

/-! Pulling genuine power series back by contractive linear parameter maps
preserves a common convergence radius, coefficient bounds, and measurability. -/
noncomputable section
open scoped Topology BigOperators NNReal ENNReal
open MeasureTheory
namespace BourgadeHuang

variable {E F G Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Contractive linear pullback cannot increase any multilinear coefficient. -/
theorem norm_powerSeries_pullback_le (p : FormalMultilinearSeries ℂ F G)
    (L : E →L[ℂ] F) (hL : ‖L‖ ≤ 1) (n : ℕ) :
    ‖p.compContinuousLinearMap L n‖ ≤ ‖p n‖ := by
  calc
    _ ≤ ‖p n‖ * ‖L‖^n := by
      simpa [FormalMultilinearSeries.compContinuousLinearMap] using
        (p n).norm_compContinuousLinearMap_le (fun _ : Fin n => L)
    _ ≤ ‖p n‖ * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (norm_nonneg _) hL) (norm_nonneg _)
    _ = _ := mul_one _

/-- The full scalar or vector series pulls back on the same ball. -/
theorem hasFPowerSeriesOnBall_pullback {f : F → G}
    {p : FormalMultilinearSeries ℂ F G} (L : E →L[ℂ] F) (hL : ‖L‖ ≤ 1)
    (x : E) (r : ℝ≥0) (hp : HasFPowerSeriesOnBall f p (L x) r) :
    HasFPowerSeriesOnBall (fun z => f (L z)) (p.compContinuousLinearMap L) x r := by
  refine ⟨hp.r_le.trans (FormalMultilinearSeries.radius_le_of_le
    (norm_powerSeries_pullback_le p L hL)), hp.r_pos, ?_⟩
  intro y hy
  have hyr : ‖y‖ < (r : ℝ) := by
    simpa only [Metric.emetric_ball_nnreal, Metric.mem_ball, dist_zero_right] using hy
  have hLy : ‖L y‖ ≤ ‖y‖ :=
    (L.le_opNorm y).trans (by simpa using mul_le_mul_of_nonneg_right hL (norm_nonneg y))
  have hyL : L y ∈ EMetric.ball (0 : F) (r : ℝ≥0∞) := by
    simpa only [Metric.emetric_ball_nnreal, Metric.mem_ball, dist_zero_right] using hLy.trans_lt hyr
  simpa only [FormalMultilinearSeries.compContinuousLinearMap_apply, Function.comp_def, map_add]
    using hp.hasSum hyL

/-- A geometric coefficient majorant survives every contractive pullback. -/
theorem norm_powerSeries_pullback_le_div_pow (p : FormalMultilinearSeries ℂ F G)
    (L : E →L[ℂ] F) (hL : ‖L‖ ≤ 1) (C r : ℝ)
    (hb : ∀ n, ‖p n‖ ≤ C/r^n) (n : ℕ) :
    ‖p.compContinuousLinearMap L n‖ ≤ C/r^n :=
  (norm_powerSeries_pullback_le p L hL n).trans (hb n)

/-- Coefficient pullback is a continuous linear operation, so state measurability
is retained without any Borel-space assumption on multilinear maps. -/
theorem stronglyMeasurable_powerSeries_pullback [MeasurableSpace Ω]
    (p : Ω → FormalMultilinearSeries ℂ F G) (L : E →L[ℂ] F) (n : ℕ)
    (hp : StronglyMeasurable (fun ω => p ω n)) :
    StronglyMeasurable (fun ω => (p ω).compContinuousLinearMap L n) :=
  (ContinuousMultilinearMap.compContinuousLinearMapL
    (G := G) (fun _ : Fin n => L)).continuous.comp_stronglyMeasurable hp

/-- The same operation preserves Bochner coefficient integrability. -/
theorem integrable_powerSeries_pullback [MeasurableSpace Ω] {μ : Measure Ω}
    (p : Ω → FormalMultilinearSeries ℂ F G) (L : E →L[ℂ] F) (n : ℕ)
    (hp : Integrable (fun ω => p ω n) μ) :
    Integrable (fun ω => (p ω).compContinuousLinearMap L n) μ :=
  (ContinuousMultilinearMap.compContinuousLinearMapL
    (G := G) (fun _ : Fin n => L)).integrable_comp hp

/-- Shrinking a positive geometric radius retains the same coefficient constant. -/
theorem norm_powerSeries_le_div_pow_of_radius_le (p : FormalMultilinearSeries ℂ F G)
    {C r R : ℝ} (hC : 0 ≤ C) (hr : 0 < r) (hrR : r ≤ R)
    (hb : ∀ n, ‖p n‖ ≤ C/R^n) (n : ℕ) : ‖p n‖ ≤ C/r^n :=
  (hb n).trans (div_le_div_of_nonneg_left hC (pow_pos hr n)
    (pow_le_pow_left₀ hr.le hrR n))

/-- A neighborhood identity uniform in the state allows every series in the
family to be replaced on one common smaller radius. -/
theorem exists_common_powerSeries_congr {F₁ F₂ : Ω → E → G}
    {p : Ω → FormalMultilinearSeries ℂ E G} {x : E} {r : ℝ≥0}
    (hr : 0 < r) (hp : ∀ ω, HasFPowerSeriesOnBall (F₁ ω) (p ω) x r)
    (heq : ∀ᶠ z in nhds x, ∀ ω, F₁ ω z = F₂ ω z) :
    ∃ r' : ℝ≥0, 0 < r' ∧ r' ≤ r ∧
      ∀ ω, HasFPowerSeriesOnBall (F₂ ω) (p ω) x r' := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp heq
  let r' : ℝ≥0 := min r ⟨ε,hε.le⟩
  have hr' : 0 < r' := lt_min hr hε
  have hr'r : r' ≤ r := min_le_left _ _
  refine ⟨r',hr',hr'r,fun ω => ?_⟩
  apply ((hp ω).mono (by exact_mod_cast hr') (by exact_mod_cast hr'r)).congr
  intro z hz
  apply hball _ ω
  have hz' : z ∈ Metric.ball x (r' : ℝ) := by
    simpa only [Metric.emetric_ball_nnreal] using hz
  exact Metric.ball_subset_ball (show (r' : ℝ) ≤ ε from min_le_right _ _) hz'

end BourgadeHuang
