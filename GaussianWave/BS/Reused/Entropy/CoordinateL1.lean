import Mathlib

/-! Elementary coordinate norm used by the lower quantization estimates. -/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS.Reused.Entropy.Mehler
variable {I : Type*} [Fintype I]
def coordinateL1 (z : I → ℝ) : ℝ := ∑ i, |z i|
theorem coordinateL1_nonneg (z : I → ℝ) : 0 ≤ coordinateL1 z :=
  Finset.sum_nonneg (fun i _ => abs_nonneg _)
theorem continuous_coordinateL1 : Continuous (coordinateL1 : (I → ℝ) → ℝ) := by
  unfold coordinateL1
  fun_prop
end GaussianWave.BS.Reused.Entropy.Mehler
