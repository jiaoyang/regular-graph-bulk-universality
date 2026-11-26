import GaussianWave.BS.ColoredLogDensityRigidity
import GaussianWave.BS.SteinFactorization
import GaussianWave.BS.ColoredRootStationarity

/-! Genuine all-direction multichannel characteristic factorization, derived
from actual whole-edge Fisher equality and the full transverse score. -/
noncomputable section
open MeasureTheory
open scoped Topology BigOperators
namespace GaussianWave.BS

theorem colored_star_characteristic_transverse_factorization_of_fisherDefect_zero
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (ColoredSpace d r)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin r × Fin d)) μ)
    (hmom : HasIdentitySecondMoments μ) {t : ℝ} (ht : 0 < t)
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ)
    (hzero : heatFrameFisherDefect μ (coloredStarEdgeProjection d r c) t = 0)
    (hperm : ∀ p : Equiv.Perm (Fin d),
      Measure.map (fun x : ColoredSpace d r => fun q => x (q.1, p q.2)) μ = μ)
    (w : ColoredSpace d r) (hw : ∀ a, ∑ j, w (a, j) = 0)
    (hunit : squareRadius w = 1) (a : Fin r → ℝ) (s : ℝ) :
    characteristicIntegral (heatedLaw μ t) (coloredRootLift d r a + s • w) =
      characteristicIntegral (Measure.map (coloredStarRootForm d r) (heatedLaw μ t)) a *
        Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (1 + 2 * t) * s ^ 2)) := by
  have hscore := colored_heatDirectionalScore_of_fisherDefect_zero
    d r hd c hbulk μ hμ hmom ht hrev hzero hperm w hw
  have hq : finiteLinearForm (coloredRootLift d r a) w = 0 := by
    simp only [finiteLinearForm, Fintype.sum_prod_type, coloredRootLift_apply,
      starRootDirection, mul_assoc, ← Finset.mul_sum, hw, mul_zero, Finset.sum_const_zero]
  have hfactor := characteristicIntegral_transverse_factorization μ hμ ht w hunit
    (1 + 2 * t) (by positivity) hscore (coloredRootLift d r a) hq s
  have hroot : characteristicIntegral (heatedLaw μ t) (coloredRootLift d r a) =
      characteristicIntegral (Measure.map (coloredStarRootForm d r) (heatedLaw μ t)) a := by
    change (∫ x, linearCharacteristic (coloredRootLift d r a) x ∂heatedLaw μ t) =
      ∫ x, linearCharacteristic a x ∂Measure.map (coloredStarRootForm d r) (heatedLaw μ t)
    rw [integral_map (continuous_coloredStarRootForm d r).measurable.aemeasurable
        (linearCharacteristic a).continuous.measurable.aestronglyMeasurable]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      change Complex.exp ((finiteLinearForm (coloredRootLift d r a) x : ℂ) * Complex.I) = _
      rw [finiteLinearForm_coloredRootLift]
      rfl)
  rw [hfactor, hroot]
  congr 2
  push_cast
  ring

end GaussianWave.BS
