import BourgadeHuang.MultivariateExponentialLoop

/-! Dominated stability of exponentially tilted loop identities under source approximation. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- Uniform linear anchor bounds justify passing exponential loop identities
through pointwise source limits. Integrability of the limiting identity is proved. -/
theorem exponential_loop_identity_of_source_limits
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    (H : AnchoredCountingState → ℂ) (hH : AnchoredGrowth H 2)
    (Xn Jn : ℕ → AnchoredCountingState → ℂ) (X J : AnchoredCountingState → ℂ)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hXn : ∀ n s, ‖Xn n s‖ ≤ C * (1 + ‖s.val.2‖))
    (hJn : ∀ n s, ‖Jn n s‖ ≤ D * (1 + ‖s.val.2‖))
    (hX : ∀ s, Tendsto (fun n => Xn n s) atTop (𝓝 (X s)))
    (hJ : ∀ s, Tendsto (fun n => Jn n s) atTop (𝓝 (J s)))
    (hz : ∀ n, Integrable (fun s => (H s + Jn n s) * Complex.exp (Xn n s)) ν ∧
      (∫ s, (H s + Jn n s) * Complex.exp (Xn n s) ∂ν) = 0) :
    Integrable (fun s => (H s + J s) * Complex.exp (X s)) ν ∧
      (∫ s, (H s + J s) * Complex.exp (X s) ∂ν) = 0 := by
  obtain ⟨A, hA, hAb⟩ := hH
  let F := fun n s => (H s + Jn n s) * Complex.exp (Xn n s)
  let G := fun s => (H s + J s) * Complex.exp (X s)
  let B := fun s : AnchoredCountingState =>
    ((A + D) * Real.exp C) * (1 + ‖s.val.2‖) ^ 2 * Real.exp (C * ‖s.val.2‖)
  have hB : Integrable B ν := integrable_anchor_polynomial_exp ν ha he
    (mul_nonneg (add_nonneg hA hD) (Real.exp_nonneg C)) 2 C
  have hb (n : ℕ) (s : AnchoredCountingState) : ‖F n s‖ ≤ B s := by
    have hpow : 1 + ‖s.val.2‖ ≤ (1 + ‖s.val.2‖) ^ 2 := by nlinarith [norm_nonneg s.val.2]
    have hhead : ‖H s + Jn n s‖ ≤ (A + D) * (1 + ‖s.val.2‖) ^ 2 :=
      (norm_add_le _ _).trans ((add_le_add (hAb s)
        ((hJn n s).trans (mul_le_mul_of_nonneg_left hpow hD))).trans_eq (by ring))
    calc
      ‖F n s‖ ≤ ((A + D) * (1 + ‖s.val.2‖) ^ 2) * Real.exp (C * (1 + ‖s.val.2‖)) := by
        dsimp only [F]
        rw [norm_mul]
        exact mul_le_mul hhead ((Complex.norm_exp_le_exp_norm _).trans
          (Real.exp_le_exp.mpr (hXn n s))) (norm_nonneg _) (by positivity)
      _ = B s := by dsimp [B]; rw [mul_add C, mul_one, Real.exp_add]; ring
  have hlim (s : AnchoredCountingState) : Tendsto (fun n => F n s) atTop (𝓝 (G s)) :=
    (tendsto_const_nhds.add (hJ s)).mul (Complex.continuous_exp.tendsto _ |>.comp (hX s))
  have hmeas : AEStronglyMeasurable G ν := aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (hz n).1.aestronglyMeasurable) (Filter.Eventually.of_forall hlim)
  have hGi : Integrable G ν := hB.mono' hmeas (Filter.Eventually.of_forall (fun s =>
    le_of_tendsto (hlim s).norm (Filter.Eventually.of_forall (fun n => hb n s))))
  have hi := tendsto_integral_of_dominated_convergence B (fun n => (hz n).1.aestronglyMeasurable)
    hB (fun n => Filter.Eventually.of_forall (hb n)) (Filter.Eventually.of_forall hlim)
  have hzero (n : ℕ) : (∫ s, F n s ∂ν) = 0 := (hz n).2
  change Tendsto (fun n => ∫ s, F n s ∂ν) atTop (𝓝 (∫ s, G s ∂ν)) at hi
  simp only [hzero] at hi
  exact ⟨hGi, tendsto_nhds_unique hi tendsto_const_nhds⟩

/-- The finite-source exponential equation is independent of the chosen finite index type. -/
theorem multivariate_exponential_tilted_loop_identity_fintype
    {ι : Type*} [Fintype ι]
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    {w : ℂ} {v : ι → ℂ} (hw : w.im ≠ 0) (hv : ∀ i, (v i).im ≠ 0) (c : ι → ℂ) :
    Integrable (fun s => (anchoredLoopHead β s w +
      ∑ i, c i * ((2 / β.value) * anchoredInteraction s w (v i))) *
        Complex.exp (∑ i, c i * anchoredNevanlinna s (v i))) ν ∧
    (∫ s, (anchoredLoopHead β s w + ∑ i, c i * ((2 / β.value) * anchoredInteraction s w (v i))) *
      Complex.exp (∑ i, c i * anchoredNevanlinna s (v i)) ∂ν) = 0 := by
  let e := (Fintype.equivFin ι).symm
  have h := multivariate_exponential_tilted_loop_identity ν β hh ha he hw
    (fun i => hv (e i)) (fun i => c (e i))
  have hX (s : AnchoredCountingState) : (∑ i, c (e i) * anchoredNevanlinna s (v (e i))) =
      ∑ i, c i * anchoredNevanlinna s (v i) := e.sum_comp (fun i => c i * anchoredNevanlinna s (v i))
  have hJ (s : AnchoredCountingState) : (∑ i, c (e i) * ((2 / β.value) * anchoredInteraction s w (v (e i)))) =
      ∑ i, c i * ((2 / β.value) * anchoredInteraction s w (v i)) :=
    e.sum_comp (fun i => c i * ((2 / β.value) * anchoredInteraction s w (v i)))
  simpa only [hX, hJ] using h

end BourgadeHuang
