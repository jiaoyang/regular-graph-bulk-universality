import GeneralizedBulk.Entropy.GridClippingLoss
import GeneralizedBulk.Entropy.CorrelatedTail

/-! Explicit entropy clipping loss for an actual correlated Gaussian vector.
Only marginal mean/variance bounds are used, so the noise may be fully
correlated across vertices. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal

namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian

set_option maxHeartbeats 1500000 in
theorem correlated_gaussian_grid_clipping_loss {m : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix (Fin m) J ℝ) (mean : Fin m → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hmean : ∀ i,|mean i| ≤ M)
    (c : ℝ≥0) (hc : 0 < c) (hvar : ∀ i,coordinateVariance A i ≤ c)
    (a : ℝ) (ha : 0 < a) (K : ℕ) (hK : 0 < K) (hR : M ≤ (K : ℝ)*a) :
    countableEntropy (lawMass (linearImageGaussian A) (fun x => gridLabel a (mean+x)))-
      Finite.entropy (lawMass (linearImageGaussian A)
        (fun x => codedClipIntegerVector K hK (gridLabel a (mean+x)))) ≤
      gridClippingLossConstant m a (M^2+(c : ℝ))*
        Real.sqrt (2*(m : ℝ)*Real.exp (-((K : ℝ)*a-M)^2/(2*(c : ℝ)))) := by
  let μ := linearImageGaussian A
  let X : (Fin m → ℝ) → Fin m → ℝ := fun x => mean+x
  have hm : Measurable X := by fun_prop
  have hcoord (i : Fin m) : MemLp (fun x => X x i) 2 μ :=
    gaussianLaw_memLp_two μ (fun x => mean i+x i) (by fun_prop) (mean i) (coordinateVariance A i)
      (linearImageGaussian_shifted_coordinate A mean i)
  have hB (i : Fin m) : (∫ x,X x i^2 ∂μ) ≤ M^2+(c : ℝ) := by
    change (∫ x,(mean i+x i)^2 ∂μ) ≤ _
    rw [gaussianLaw_second_moment μ (fun x => mean i+x i) (mean i) (coordinateVariance A i)
      (linearImageGaussian_shifted_coordinate A mean i)]
    have hv : (coordinateVariance A i : ℝ) ≤ c := by exact_mod_cast hvar i
    have hs : (mean i)^2 ≤ M^2 := by
      have hi := hmean i
      have hh := mul_self_le_mul_self (abs_nonneg (mean i)) hi
      simpa only [← pow_two,sq_abs] using hh
    linarith
  have h := grid_clipping_entropy_loss_le μ X hm hcoord (M^2+(c : ℝ)) hB a ha K hK
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (gridClippingLossConstant_nonneg m a _)
  apply Real.sqrt_le_sqrt
  exact correlated_grid_clipping_probability_le A mean M hmean c hc hvar a ha K hR

end GeneralizedBulk.Entropy
