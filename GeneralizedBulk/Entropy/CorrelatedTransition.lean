import GeneralizedBulk.Gaussian.CoordinateLaw
import GeneralizedBulk.Entropy.GaussianTransition

/-! Actual coordinate transition probabilities for the actual correlated
Gaussian law, uniformly over every deterministic signal shift. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal

namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem correlated_coordinate_transition_probability_le (A : Matrix I J ℝ) (a : I → ℝ) (i : I)
    (v₀ : ℝ) (hv₀ : 0 < v₀) (hvar : v₀ ≤ coordinateVariance A i)
    (F : Finset ℝ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    (linearImageGaussian A).real {x | a i+x i ∈ transitionIntervals F ℓ} ≤
      (F.card : ℝ)*(4*ℓ)/Real.sqrt (2*Real.pi*v₀) := by
  have hm : Measurable (fun x : I → ℝ => a i+x i) := by fun_prop
  have hT := measurableSet_transitionIntervals F ℓ
  change (linearImageGaussian A ((fun x : I → ℝ => a i+x i) ⁻¹' transitionIntervals F ℓ)).toReal ≤ _
  rw [← Measure.map_apply hm hT,linearImageGaussian_shifted_coordinate]
  exact gaussianReal_transition_probability_le_of_variance_lower_bound _ _ v₀ hv₀ hvar F ℓ hℓ

end GeneralizedBulk.Entropy
