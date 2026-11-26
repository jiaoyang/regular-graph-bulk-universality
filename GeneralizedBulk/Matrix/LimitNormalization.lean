import GeneralizedBulk.Graph.EntryObstruction
import GeneralizedBulk.Analysis.QuadraticProducts
import GeneralizedBulk.Analysis.UpperHalfNormalization

/-!
# Inverse-free normalization of a limiting marked resolvent

The switching residual is controlled by forward and reverse fluctuations.
Second moments suffice for their products, including correlated couplings.
The calibrated common polynomial then selects the normalized upper root.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Graph
open GeneralizedSwitching Exterior Analysis

/-- The inverse-free switching identity gives the explicit perturbation
bound at a genuine matrix entry, without a concentration event. -/
theorem switchingResidual_entry_le_errors
    (H M Mtilde : Mat) (h x y : ℝ)
    (hH : EntryBound H h) (hX : EntryBound (M - H) x)
    (hY : EntryBound (endpointPermutation * (Mtilde - H) * endpointPermutation) y)
    (hshift : (1 + M * switchIncrement) *
      (endpointPermutation * Mtilde * endpointPermutation) = M) :
    ‖switchingResidual H 0 1‖ ≤ x + y + 16 * h * y + 16 * x * h + 16 * x * y := by
  let X := M - H
  let Y := (endpointPermutation : Mat) * (Mtilde - H) * endpointPermutation
  have hM : H + X = M := by dsimp [X]; abel
  have hMY : endpointPermutation * H * endpointPermutation + Y =
      endpointPermutation * Mtilde * (endpointPermutation : Mat) := by
    dsimp [Y]
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hR : switchingResidual H = X - Y - H * switchIncrement * Y -
      X * switchIncrement * endpointPermutation * H * endpointPermutation - X * switchIncrement * Y := by
    have hs : (1 + (H + X) * switchIncrement) *
        (endpointPermutation * H * endpointPermutation + Y) = H + X := by
      rw [hM,hMY]
      exact hshift
    have hid := switchingResidual_perturbation_identity H X Y hs
    have hexpand : (1 + H * switchIncrement) * Y = Y + H * switchIncrement * Y := by
      rw [Matrix.add_mul,one_mul]
    rw [hexpand] at hid
    apply sub_eq_zero.mp
    calc
      _ = switchingResidual H + (Y + H * switchIncrement * Y) +
        X * switchIncrement * endpointPermutation * H * endpointPermutation +
          X * switchIncrement * Y - X := by abel
      _ = 0 := hid
  have hHY := (hH.mul entryBound_switchIncrement).mul hY
  have hXH := (hX.mul entryBound_switchIncrement).mul hH.conjugate
  have hXY := (hX.mul entryBound_switchIncrement).mul hY
  have hXH' : EntryBound (X * switchIncrement * endpointPermutation * H * endpointPermutation)
      (4 * (4 * x * 1) * h) := by
    simpa only [Matrix.mul_assoc] using hXH
  have hb := ((((hX.sub hY).sub hHY).sub hXH').sub hXY) 0 1
  rw [← hR] at hb
  convert hb using 1 <;> ring

/-- The deterministic limiting mean with the calibrated scalar coordinate. -/
def calibratedMean (parameters : Parameters) (s : ℂ) : Mat :=
  meanMatrix ((parameters.center : ℂ) + (parameters.scale : ℂ) * s)
    ((parameters.p : ℂ) * ((parameters.center : ℂ) + (parameters.scale : ℂ) * s) + parameters.r) 0

theorem calibratedMean_residual (parameters : Parameters) (s : ℂ) :
    switchingResidual (calibratedMean parameters s) =
      ((parameters.scale : ℂ) ^ 2 * (1 - (parameters.p : ℂ) ^ 2) * (s ^ 2 + 1)) •
        (switchIncrement : Mat) := by
  rw [switchingResidual,calibratedMean,common_switching_polynomial,
    parameters.complex_scalar_polynomial]

/-- A literal residual entry detects the scalar quadratic normalization. -/
theorem calibratedMean_residual_entry_norm (parameters : Parameters) (s : ℂ) :
    ‖switchingResidual (calibratedMean parameters s) 0 1‖ =
      (parameters.scale ^ 2 * (1 - parameters.p ^ 2)) * ‖s ^ 2 + 1‖ := by
  rw [calibratedMean_residual,switchIncrement_eq]
  change ‖((parameters.scale : ℂ) ^ 2 * (1 - (parameters.p : ℂ) ^ 2) * (s ^ 2 + 1)) * (-1)‖ = _
  rw [mul_neg_one,norm_neg]
  have hcoef : 0 ≤ parameters.scale ^ 2 * (1 - parameters.p ^ 2) := by
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr parameters.p_sq_lt_one.le)
  have heq : (parameters.scale : ℂ) ^ 2 * (1 - (parameters.p : ℂ) ^ 2) =
      ((parameters.scale ^ 2 * (1 - parameters.p ^ 2) : ℝ) : ℂ) := by push_cast; rfl
  rw [heq,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hcoef]

/-- Vanishing expected matrix residual gives the actual positive scalar
normalization in L1. Integrability of the residual is not assumed separately. -/
theorem integral_normalization_of_calibrated_residual
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (parameters : Parameters)
    (s : ℕ → Ω → ℂ) (hs : ∀ n, AEStronglyMeasurable (s n) P)
    (hupper : ∀ n, ∀ᵐ x ∂P, 0 ≤ (s n x).im)
    (hpoly : ∀ n, Integrable (fun x => s n x ^ 2 + 1) P)
    (hzero : Tendsto (fun n => ∫ x,
      ‖switchingResidual (calibratedMean parameters (s n x)) 0 1‖ ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖s n x - Complex.I‖ ∂P) atTop (𝓝 0) := by
  apply integral_norm_sub_I_tendsto_zero_of_quadratic P s hs hupper hpoly
  let k := parameters.scale ^ 2 * (1 - parameters.p ^ 2)
  have hk : k ≠ 0 := ne_of_gt (mul_pos (sq_pos_of_pos parameters.scale_pos)
    (sub_pos.mpr parameters.p_sq_lt_one))
  have heq (n : ℕ) : (∫ x,
      ‖switchingResidual (calibratedMean parameters (s n x)) 0 1‖ ∂P) / k =
      ∫ x, ‖s n x ^ 2 + 1‖ ∂P := by
    simp_rw [calibratedMean_residual_entry_norm]
    rw [integral_const_mul]
    exact mul_div_cancel_left₀ _ hk
  simpa only [heq,zero_div] using hzero.div_const k

end GeneralizedBulk.Graph
