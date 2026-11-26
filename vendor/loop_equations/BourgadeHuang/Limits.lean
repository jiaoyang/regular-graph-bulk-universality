import BourgadeHuang.PointProcessModel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open scoped Topology
open Filter MeasureTheory

namespace BourgadeHuang

def VanishingHierarchy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (β : Beta) (x : (N : ℕ) → Ω → Fin N → ℝ) (center : ℝ) : Prop :=
  ∀ n : ℕ, ∀ K : Set ℂ, IsCompact K → (∀ w ∈ K, w.im ≠ 0) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ w ∈ K, ∀ aux : Fin n → ℂ,
      (∀ a, aux a ∈ K) → ‖∫ ω, loopIntegrand β (x N ω) center w aux ∂μ‖ < ε

/-- The quantitative hierarchy rate really tends to zero. This does not prove the
characterization theorem or any rate of point-process convergence. -/
theorem tendsto_zero_of_polynomial_rate (f : ℕ → ℂ) {c C : ℝ} (hc : 0 < c)
    (h : ∀ᶠ N in atTop, ‖f N‖ ≤ C * (N : ℝ) ^ (-c)) :
    Tendsto f atTop (𝓝 0) := by
  apply squeeze_zero_norm' h
  simpa using ((tendsto_rpow_neg_atTop hc).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)).const_mul C

/-- A concrete fixed-parameter consequence of the compact-uniform hierarchy (4.50).
Coincident parameters and mixed half-planes are permitted by the hypotheses. -/
theorem hierarchy_expectation_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (β : Beta)
    (x : (N : ℕ) → Ω → Fin N → ℝ) (center : ℝ)
    (h : ApproximateHierarchy μ β x center)
    {n : ℕ} {K : Set ℂ} (hK : IsCompact K) (hKoff : ∀ w ∈ K, w.im ≠ 0)
    {w : ℂ} (hw : w ∈ K) (aux : Fin n → ℂ) (haux : ∀ a, aux a ∈ K) :
    Tendsto (fun N => ∫ ω, loopIntegrand β (x N ω) center w aux ∂μ) atTop (𝓝 0) := by
  obtain ⟨C, _hC, hbound⟩ := h n K hK hKoff (1 / 12) (by norm_num) (by norm_num)
  apply tendsto_zero_of_polynomial_rate _ (show (0 : ℝ) < 1 / 12 by norm_num)
  filter_upwards [hbound] with N hN
  exact hN w hw aux haux

/-- Uniform vanishing of the full hierarchy, as required by the external characterization. -/
theorem hierarchy_vanishing {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (β : Beta) (x : (N : ℕ) → Ω → Fin N → ℝ) (center : ℝ)
    (h : ApproximateHierarchy μ β x center) : VanishingHierarchy μ β x center := by
  intro n K hK hoff ε hε
  obtain ⟨C, _hC, hbound⟩ := h n K hK hoff (1 / 12) (by norm_num) (by norm_num)
  have hz : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(1 / 12 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 12 by norm_num)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)).const_mul C
  have hsmall := hz.eventually (gt_mem_nhds hε)
  filter_upwards [hbound, hsmall] with N hN hsmallN
  intro w hw aux haux
  exact lt_of_le_of_lt (hN w hw aux haux) hsmallN

end BourgadeHuang
