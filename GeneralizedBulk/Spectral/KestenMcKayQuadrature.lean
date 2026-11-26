import GeneralizedBulk.Spectral.KestenMcKayFiniteQuantile
import GeneralizedBulk.Spectral.QuantileQuadrature
import GeneralizedBulk.Graph.SpectralLogPotential

/-! Actual Kesten–McKay quantile quadrature for the regularized logarithmic
potential, with a polynomially sufficient explicit mesoscopic error. -/
noncomputable section
open scoped BigOperators
open Set MeasureTheory
namespace GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Spectral

def regularizedPotential (d E eta : ℝ) : ℝ :=
  ∫ x in -radius d..radius d, regularizedLog E eta x * rawDensity d x

theorem finiteQuantile_sum_reflect (d : ℝ) (hd : 3 ≤ d) (N : ℕ) (hN : 0 < N) (f : ℝ → ℝ) :
    (∑ j : Fin N, f (finiteQuantile d hd N hN j)) =
      ∑ j ∈ Finset.range N, f (quantileNode d hd N hN (j + 1)) := by
  change (∑ j : Fin N, f (quantileNode d hd N hN (N - j.val))) = _
  rw [Fin.sum_univ_eq_sum_range (fun j => f (quantileNode d hd N hN (N - j))) N]
  calc
    _ = ∑ j ∈ Finset.range N, f (quantileNode d hd N hN (N - 1 - j + 1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have heq : N - j = N - 1 - j + 1 := by have hj' := Finset.mem_range.mp hj; omega
      rw [heq]
    _ = _ := Finset.sum_range_reflect (fun j => f (quantileNode d hd N hN (j + 1))) N

/-- Quantiles are constructed from the actual density. The error is O(1/(N eta));
there is no quantile quadrature assumption in this theorem. -/
theorem regularizedPotential_quantile_error (d : ℝ) (hd : 3 ≤ d)
    (N : ℕ) (hN : 0 < N) (E eta : ℝ) (heta : 0 < eta) :
    |regularizedPotential d E eta - (∑ j : Fin N, regularizedLog E eta (finiteQuantile d hd N hN j)) / (N : ℝ)| ≤
      4 * radius d / ((N : ℝ) * eta) := by
  have hf : Continuous (regularizedLog E eta) := continuous_iff_continuousAt.mpr
    (fun x => (regularizedLog_hasDerivAt E eta heta x).continuousAt)
  have hh := quantile_quadrature_right (rawDensity d) (regularizedLog E eta)
    (quantileNode d hd N hN) (monotone_quantileNode d hd N hN) N hN eta⁻¹ (inv_nonneg.mpr heta.le)
    (by simpa only [quantileNode_lower, quantileNode_upper] using continuousOn_rawDensity d hd)
    (fun x hx => rawDensity_nonneg d hd (by simpa only [quantileNode_lower, quantileNode_upper] using hx))
    hf.continuousOn
    (fun x _ y _ => regularizedLog_lipschitz E eta heta x y)
    (quantileNode_cell_mass d hd N hN)
  rw [quantileNode_lower, quantileNode_upper] at hh
  rw [finiteQuantile_sum_reflect]
  change |(∫ x in -radius d..radius d, regularizedLog E eta x * rawDensity d x) - _| ≤ _
  convert hh using 1 <;> ring

end GeneralizedBulk.KestenMcKay
