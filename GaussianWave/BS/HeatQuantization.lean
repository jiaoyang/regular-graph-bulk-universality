import GaussianWave.BS.HeatTranslationKL
import GaussianWave.BS.HeatRegularity
import GaussianWave.BS.Reused.Entropy.GridEntropyError
import GaussianWave.BS.Reused.Entropy.GridMoments
import GaussianWave.BS.Reused.Entropy.GridClippingLoss

/-! Actual uniform-grid entropy approximation for arbitrary Gaussian convolutions.
The translation estimate is proved from the Gaussian kernel, not assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace GaussianWave.BS
open Reused.Entropy

private theorem coordinateL1_le_card_add_squareRadius {I : Type*} [Fintype I] (x : I → ℝ) :
    Reused.Entropy.Mehler.coordinateL1 x ≤ (Fintype.card I : ℝ) + squareRadius x := by
  calc
    _ ≤ ∑ i, (1 + x i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [sq_abs (x i), sq_nonneg (|x i| - 1)]
    _ = _ := by simp [Reused.Entropy.Mehler.coordinateL1, squareRadius, Finset.sum_add_distrib]

private theorem integrable_heatDensity_mul_coordinateL1
    {I : Type*} [Fintype I] (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => heatDensity μ t x * Reused.Entropy.Mehler.coordinateL1 x) := by
  apply (((integrable_heatDensity μ ht).mul_const (Fintype.card I : ℝ)).add
    (integrable_heatDensity_mul_squareRadius μ hμ ht)).mono'
      (((measurable_heatDensity μ t).mul Reused.Entropy.Mehler.continuous_coordinateL1.measurable).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatDensity_nonneg _ _ _) (Reused.Entropy.Mehler.coordinateL1_nonneg _))]
  change heatDensity μ t x * Reused.Entropy.Mehler.coordinateL1 x ≤
    heatDensity μ t x * (Fintype.card I : ℝ) + heatDensity μ t x * squareRadius x
  simpa only [mul_add] using mul_le_mul_of_nonneg_left
    (coordinateL1_le_card_add_squareRadius x) (heatDensity_nonneg μ t x)

/-- Unclipped grid entropy differs from actual heat differential entropy by
an explicit error tending to zero with the mesh. -/
theorem heatDensity_grid_entropy_error {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin m)) μ) {t : ℝ} (ht : 0 < t)
    (a : ℝ) (ha : 0 < a) :
    0 ≤ countableEntropy (gridMass a (heatDensity μ t)) + (m : ℝ) * Real.log a -
      densityEntropy volume (heatDensity μ t) ∧
    countableEntropy (gridMass a (heatDensity μ t)) + (m : ℝ) * Real.log a -
      densityEntropy volume (heatDensity μ t) ≤ ((2 : ℝ)^m / 2) * (1 / (2*t)) * m * a^2 := by
  have hH := summable_grid_entropy a ha (heatDensity μ t) (measurable_heatDensity μ t)
    (heatDensity_nonneg μ t) (integrable_heatDensity μ ht) (integral_heatDensity μ ht)
    (integrable_heatDensity_mul_coordinateL1 μ hμ ht)
  have h := grid_entropy_error_bound a ha (heatDensity μ t) (continuous_heatDensity μ ht)
    (heatDensity_pos μ ht) (integrable_heatDensity μ ht) (integrable_heatDensity_log μ hμ ht)
    (integral_heatDensity μ ht) hH (1 / (2*t)) (by positivity)
    (fun h => (heatDensity_symmetric_translation_entropy μ ht h).1)
    (fun h => by simpa only [symmetrizedDensityPair, squareRadius, div_eq_inv_mul, mul_one] using
      (heatDensity_symmetric_translation_entropy μ ht h).2)
  simp only [Fintype.card_fin] at h
  have he : (2 * a ^ m)⁻¹ * ((1 / (2*t)) * m * a^2) * (2*a)^m =
      ((2 : ℝ)^m / 2) * (1 / (2*t)) * m * a^2 := by
    rw [mul_pow]
    field_simp
    <;> ring
  rw [he] at h
  simpa only [densityEntropy, sub_neg_eq_add] using h

/-- The renormalized countable-grid entropy converges to actual differential
entropy of any finite-second-moment input heated for positive time. -/
theorem tendsto_heatDensity_grid_entropy {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin m)) μ) {t : ℝ} (ht : 0 < t)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => countableEntropy (gridMass (a n) (heatDensity μ t)) +
      (m : ℝ) * Real.log (a n)) atTop (𝓝 (densityEntropy volume (heatDensity μ t))) := by
  have hb : Tendsto (fun n => ((2 : ℝ)^m / 2) * (1 / (2*t)) * m * (a n)^2) atTop (𝓝 0) := by
    simpa using (ha0.pow 2).const_mul (((2 : ℝ)^m / 2) * (1 / (2*t)) * m)
  have hg : Tendsto (fun n => countableEntropy (gridMass (a n) (heatDensity μ t)) +
      (m : ℝ) * Real.log (a n) - densityEntropy volume (heatDensity μ t)) atTop (𝓝 0) :=
    squeeze_zero (fun n => (heatDensity_grid_entropy_error μ hμ ht (a n) (ha n)).1)
      (fun n => (heatDensity_grid_entropy_error μ hμ ht (a n) (ha n)).2) hb
  have hh := hg.add_const (densityEntropy volume (heatDensity μ t))
  simpa only [sub_add_cancel, zero_add] using hh

/-- Cell masses are literal masses of the actual quantizer law. -/
theorem lawMass_withDensity_gridLabel {I : Type*} [Fintype I]
    (a : ℝ) (ha : 0 < a) (f : (I → ℝ) → ℝ)
    (hf : Integrable f) (hp : ∀ x, 0 ≤ f x) (j : I → ℤ) :
    lawMass (volume.withDensity (fun x => ENNReal.ofReal (f x))) (gridLabel a) j = gridMass a f j := by
  rw [lawMass, measureReal_def, ← gridCell_eq_fiber a ha j,
    withDensity_apply _ (measurableSet_gridCell a j)]
  rw [← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_of_all _ hp)]
  exact ENNReal.toReal_ofReal (integral_nonneg hp)

theorem lawMass_heatedLaw_gridLabel {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (a : ℝ) (ha : 0 < a) :
    lawMass (heatedLaw μ t) (gridLabel a) = gridMass a (heatDensity μ t) := by
  funext j
  rw [heatedLaw_eq_withDensity μ ht]
  exact lawMass_withDensity_gridLabel a ha _ (integrable_heatDensity μ ht) (heatDensity_nonneg μ t) j

end GaussianWave.BS
