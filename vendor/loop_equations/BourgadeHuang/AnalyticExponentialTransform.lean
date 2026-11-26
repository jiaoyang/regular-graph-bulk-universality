import BourgadeHuang.MultivariateExponentialLoop

/-!
# Entire generating transforms of the reconstructed law

Polynomial insertions and arbitrary finite linear sources define genuine entire
functions. Differentiation under expectation is proved using the exponential
anchor bound, and inserts the corresponding resolvent factor.
-/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- An exponential source with a polynomial insertion. -/
def anchoredExponentialTransform (ν : Measure AnchoredCountingState)
    (F Y X : AnchoredCountingState → ℂ) (t : ℂ) : ℂ :=
  ∫ s, F s * Complex.exp (Y s + t * X s) ∂ν

/-- Absolute integrability of polynomial insertions against a complex exponential source. -/
theorem integrable_growth_mul_exp
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    (F Y : AnchoredCountingState → ℂ) (hF : Continuous F) (hY : Continuous Y)
    {d : ℕ} (hFg : AnchoredGrowth F d) (hYg : AnchoredGrowth Y 1) :
    Integrable (fun s => F s * Complex.exp (Y s)) ν := by
  apply (integrable_growth_norm_mul_exp_norm ν ha he F Y hF hY hFg hYg).mono'
    (hF.mul (Complex.continuous_exp.comp hY)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro s
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (Complex.norm_exp_le_exp_norm _) (norm_nonneg _)

/-- Differentiating a generating transform inserts its source observable. -/
theorem hasDerivAt_anchoredExponentialTransform
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    (F Y X : AnchoredCountingState → ℂ) (hF : Continuous F) (hY : Continuous Y) (hX : Continuous X)
    {d : ℕ} (hFg : AnchoredGrowth F d) (hYg : AnchoredGrowth Y 1) (hXg : AnchoredGrowth X 1)
    (t : ℂ) : HasDerivAt (anchoredExponentialTransform ν F Y X)
      (anchoredExponentialTransform ν (fun s => F s * X s) Y X t) t := by
  obtain ⟨C, hC, hb⟩ := hFg.mul hXg
  obtain ⟨D, hD, hd⟩ := hYg
  obtain ⟨E, hE, hEbound⟩ := hXg
  have hYg : AnchoredGrowth Y 1 := ⟨D, hD, hd⟩
  have hXg : AnchoredGrowth X 1 := ⟨E, hE, hEbound⟩
  let L : ℝ := D + (‖t‖ + 1) * E
  let B := fun s : AnchoredCountingState =>
    C * Real.exp L * (1 + ‖s.val.2‖) ^ (d + 1) * Real.exp (L * ‖s.val.2‖)
  have hB : Integrable B ν := integrable_anchor_polynomial_exp ν ha he
    (mul_nonneg hC (Real.exp_nonneg _)) (d + 1) L
  have hkernel (u : ℂ) : Continuous (fun s => F s * Complex.exp (Y s + u * X s)) :=
    hF.mul (Complex.continuous_exp.comp (hY.add (continuous_const.mul hX)))
  have hdKernel (s : AnchoredCountingState) (u : ℂ) :
      HasDerivAt (fun v : ℂ => F s * Complex.exp (Y s + v * X s))
        (F s * X s * Complex.exp (Y s + u * X s)) u := by
    have hh := ((Complex.hasDerivAt_exp (Y s + u * X s)).comp u
      ((hasDerivAt_const u (Y s)).add ((hasDerivAt_id u).mul_const (X s)))).const_mul (F s)
    convert hh using 1
    simp only [zero_add, one_mul, id_eq]
    ring
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u s => F s * Complex.exp (Y s + u * X s))
    (F' := fun u s => F s * X s * Complex.exp (Y s + u * X s))
    (bound := B) (show (0 : ℝ) < 1 by norm_num)
    (Filter.Eventually.of_forall (fun u => (hkernel u).aestronglyMeasurable))
    (integrable_growth_mul_exp ν ha he F (fun s => Y s + t * X s) hF
      (hY.add (continuous_const.mul hX)) hFg (hYg.add (AnchoredGrowth.const_mul t hXg)))
    ((hF.mul hX).mul (Complex.continuous_exp.comp (hY.add (continuous_const.mul hX)))).aestronglyMeasurable
    ?_ hB (Filter.Eventually.of_forall (fun s u _ => hdKernel s u))).2
  apply Filter.Eventually.of_forall
  intro s u hu
  have hu' : ‖u - t‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hu
  have hnormu : ‖u‖ ≤ ‖t‖ + 1 := by
    have hh : ‖u‖ ≤ ‖u - t‖ + ‖t‖ := by
      simpa only [sub_add_cancel] using norm_add_le (u - t) t
    linarith
  have harg : ‖Y s + u * X s‖ ≤ L * (1 + ‖s.val.2‖) := by
    calc
      _ ≤ ‖Y s‖ + ‖u‖ * ‖X s‖ := by simpa only [norm_mul] using norm_add_le (Y s) (u * X s)
      _ ≤ D * (1 + ‖s.val.2‖) + (‖t‖ + 1) * (E * (1 + ‖s.val.2‖)) :=
        add_le_add (by simpa only [pow_one] using hd s)
          (mul_le_mul hnormu (by simpa only [pow_one] using hEbound s) (norm_nonneg _) (by positivity))
      _ = L * (1 + ‖s.val.2‖) := by dsimp [L]; ring
  calc
    ‖F s * X s * Complex.exp (Y s + u * X s)‖ ≤
        (C * (1 + ‖s.val.2‖) ^ (d + 1)) * Real.exp (L * (1 + ‖s.val.2‖)) := by
      rw [norm_mul]
      exact mul_le_mul (hb s)
        ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr harg))
        (norm_nonneg _) (by positivity)
    _ = B s := by
      dsimp [B]
      rw [mul_add L, mul_one, Real.exp_add]
      ring

/-- The generating transform is entire in every finite linear-source direction. -/
theorem analyticAt_anchoredExponentialTransform
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    (F Y X : AnchoredCountingState → ℂ) (hF : Continuous F) (hY : Continuous Y) (hX : Continuous X)
    {d : ℕ} (hFg : AnchoredGrowth F d) (hYg : AnchoredGrowth Y 1) (hXg : AnchoredGrowth X 1)
    (t : ℂ) : AnalyticAt ℂ (anchoredExponentialTransform ν F Y X) t := by
  have hd : DifferentiableOn ℂ (anchoredExponentialTransform ν F Y X) Set.univ :=
    fun z _ => (hasDerivAt_anchoredExponentialTransform ν ha he F Y X hF hY hX hFg hYg hXg z).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (Filter.univ_mem : Set.univ ∈ 𝓝 t)

/-- A second source derivative inserts its square, with no formal interchange. -/
theorem hasDerivAt_deriv_anchoredExponentialTransform
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    (F Y X : AnchoredCountingState → ℂ) (hF : Continuous F) (hY : Continuous Y) (hX : Continuous X)
    {d : ℕ} (hFg : AnchoredGrowth F d) (hYg : AnchoredGrowth Y 1) (hXg : AnchoredGrowth X 1)
    (t : ℂ) : HasDerivAt (deriv (anchoredExponentialTransform ν F Y X))
      (anchoredExponentialTransform ν (fun s => F s * X s ^ 2) Y X t) t := by
  have hdeq : deriv (anchoredExponentialTransform ν F Y X) =
      anchoredExponentialTransform ν (fun s => F s * X s) Y X := by
    funext u
    exact (hasDerivAt_anchoredExponentialTransform ν ha he F Y X hF hY hX hFg hYg hXg u).deriv
  rw [hdeq]
  convert hasDerivAt_anchoredExponentialTransform ν ha he (fun s => F s * X s) Y X
    (hF.mul hX) hY hX (hFg.mul hXg) hYg hXg t using 1
  congr 1
  funext s
  ring

end BourgadeHuang
