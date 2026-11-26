import GeneralizedBulk.Graph.SpectralLogPotential

/-! The actual HY rigidity event controls the finite logarithmic-potential
replacement error uniformly in the spectral energy. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Spectral
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

/-- The exceptional trivial eigenvalue is explicitly omitted, exactly as in
HY's rigidity theorem. No claim about the quantile law is assumed here. -/
theorem HY_regularizedLog_nontrivial {P : Measure Ω} [IsProbabilityMeasure P]
    {quantile : ∀ n, Fin (N n) → ℝ} (H : HYCoarseInput D P quantile)
    (n : ℕ) (hn : H.events.threshold ≤ n) (ω : Ω) (hω : ω ∈ H.events.good n)
    (E eta : ℝ) (heta : 0 < eta) :
    |((∑ i : Fin (N n) with i.val ≠ 0, regularizedLog E eta (D.eigenvalue n ω i)) -
       ∑ i : Fin (N n) with i.val ≠ 0, regularizedLog E eta (quantile n i)) / (N n : ℝ)| ≤
      (N n : ℝ) ^ (-H.rigidity_exponent) / eta := by
  let s : Finset (Fin (N n)) := Finset.univ.filter (fun i => i.val ≠ 0)
  have hh := regularizedLog_sum_comparison s (D.eigenvalue n ω) (quantile n)
    E eta ((N n : ℝ) ^ (-H.rigidity_exponent)) heta (fun i hi =>
      H.rigidity n hn ω hω i (Finset.mem_filter.mp hi).2)
  have hcard : (s.card : ℝ) ≤ N n := by
    have hc : s.card ≤ N n := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_le_card (Finset.filter_subset (fun i : Fin (N n) => i.val ≠ 0) Finset.univ))
    exact_mod_cast hc
  have hN : (0 : ℝ) < N n := Nat.cast_pos.mpr (D.size_pos n)
  have hr : 0 ≤ (N n : ℝ) ^ (-H.rigidity_exponent) / eta := by positivity
  change |(_ - _) / (N n : ℝ)| ≤ _
  rw [abs_div, abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hcard hr])

end GeneralizedBulk.External.RegularSpectralData
