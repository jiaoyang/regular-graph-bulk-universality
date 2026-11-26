import GeneralizedBulk.Gaussian.ParticleKernels

/-! Literal horizontal finite-difference errors for finite resolvent sums.
The dominating mass uses the same Nevanlinna weight as scalar-state
compactness. -/
noncomputable section
open BourgadeHuang
open scoped BigOperators
namespace GeneralizedBulk.Analysis

def reciprocalSquareEnvelope (w : ℂ) : ℝ :=
  1 + (2 * ‖w‖) * (1 / |w.im|) + ‖1 + w^2‖ * (1 / |w.im|)^2

theorem reciprocalSquareEnvelope_nonneg (w : ℂ) : 0 ≤ reciprocalSquareEnvelope w := by
  unfold reciprocalSquareEnvelope
  positivity

theorem reciprocal_horizontal_error (x : ℝ) (w : ℂ) (hw : w.im ≠ 0)
    (h : ℝ) (hh : h ≠ 0) :
    ((x : ℂ)-w)⁻¹^2 - (h : ℂ)⁻¹ *
      (((x : ℂ)-(w+(h : ℂ)))⁻¹ - ((x : ℂ)-w)⁻¹) =
      -(h : ℂ) * ((x : ℂ)-w)⁻¹^2 * ((x : ℂ)-(w+(h : ℂ)))⁻¹ := by
  have hw' : (w+(h : ℂ)).im ≠ 0 := by simpa using hw
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  field_simp [real_sub_ne_zero x hw,real_sub_ne_zero x hw',hh']
  ring

theorem norm_reciprocal_horizontal_error_le (x : ℝ) (w : ℂ) (hw : w.im ≠ 0)
    (h : ℝ) (hh : h ≠ 0) :
    ‖((x : ℂ)-w)⁻¹^2 - (h : ℂ)⁻¹ *
      (((x : ℂ)-(w+(h : ℂ)))⁻¹ - ((x : ℂ)-w)⁻¹)‖ ≤
      |h| * (reciprocalSquareEnvelope w / |w.im|) * nevanlinnaWeight x := by
  rw [reciprocal_horizontal_error x w hw h hh,norm_mul,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs]
  have hw' : (w+(h : ℂ)).im ≠ 0 := by simpa using hw
  have hb := norm_reciprocal_le_im x hw'
  simp only [Complex.add_im,Complex.ofReal_im,add_zero] at hb
  have hs := norm_reciprocal_sq_le_weight x hw
  change ‖((x : ℂ)-w)⁻¹^2‖ ≤ reciprocalSquareEnvelope w * nevanlinnaWeight x at hs
  have henv := reciprocalSquareEnvelope_nonneg w
  have hweight := nevanlinnaWeight_nonneg x
  calc
    _ ≤ |h| * (reciprocalSquareEnvelope w * nevanlinnaWeight x) * (1 / |w.im|) := by
      gcongr
    _ = _ := by ring

def finiteResolvent {L : Type*} [Fintype L] (x : L → ℝ) (q : L → ℂ) (w : ℂ) : ℂ :=
  ∑ i,((x i : ℂ)-w)⁻¹ * q i

def finiteResolventDerivative {L : Type*} [Fintype L] (x : L → ℝ) (q : L → ℂ) (w : ℂ) : ℂ :=
  ∑ i,((x i : ℂ)-w)⁻¹^2 * q i

theorem finiteResolvent_derivative_error_le {L : Type*} [Fintype L]
    (x : L → ℝ) (q : L → ℂ) (w : ℂ) (hw : w.im ≠ 0) (h : ℝ) (hh : h ≠ 0) :
    ‖finiteResolventDerivative x q w - (h : ℂ)⁻¹ *
      (finiteResolvent x q (w+(h : ℂ)) - finiteResolvent x q w)‖ ≤
      |h| * (reciprocalSquareEnvelope w / |w.im|) *
        ∑ i,nevanlinnaWeight (x i) * ‖q i‖ := by
  have he : finiteResolventDerivative x q w - (h : ℂ)⁻¹ *
      (finiteResolvent x q (w+(h : ℂ)) - finiteResolvent x q w) =
      ∑ i,(((x i : ℂ)-w)⁻¹^2 - (h : ℂ)⁻¹ *
        (((x i : ℂ)-(w+(h : ℂ)))⁻¹ - ((x i : ℂ)-w)⁻¹)) * q i := by
    simp only [finiteResolventDerivative,finiteResolvent,← Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  calc
    _ ≤ ∑ i,‖(((x i : ℂ)-w)⁻¹^2 - (h : ℂ)⁻¹ *
        (((x i : ℂ)-(w+(h : ℂ)))⁻¹ - ((x i : ℂ)-w)⁻¹)) * q i‖ := norm_sum_le _ _
    _ ≤ ∑ i,(|h| * (reciprocalSquareEnvelope w / |w.im|) *
        nevanlinnaWeight (x i)) * ‖q i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_reciprocal_horizontal_error_le _ _ hw h hh) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring

end GeneralizedBulk.Analysis
