import GeneralizedBulk.MatrixGeometry
import GeneralizedBulk.Parameters

/-!
# Fiberwise contractions from explicit entry covariance

The measure represents one conditional fiber of the full scalar state.
The entry covariance remains to be derived from the Gaussian marked series.
The trace contractions are proved by integrable finite-sum calculations.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk

abbrev EndpointMatrix := Matrix (Fin 4) (Fin 4) ℂ

/-- The diagonal signs of the trace observable. -/
def endpointSign : Fin 4 → ℂ := ![-1, 1, 1, -1]

/-- Concrete entrywise Wick covariance, bilinear without conjugation. -/
structure EntryWickCovariance {ι Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (p sigma : ℂ) (kernel : ι → ι → ℂ)
    (X : ι → Ω → EndpointMatrix) : Prop where
  integrable_entry : ∀ w i j, Integrable (fun ω => X w ω i j) ν
  mean_zero : ∀ w i j, (∫ ω, X w ω i j ∂ν) = 0
  integrable_product : ∀ w u i j a b,
    Integrable (fun ω => X w ω i j * X u ω a b) ν
  covariance : ∀ w u i j a b,
    (∫ ω, X w ω i j * X u ω a b ∂ν) =
      sigma ^ 2 * (covarianceMatrix p i a * covarianceMatrix p j b +
        covarianceMatrix p i b * covarianceMatrix p j a) * kernel w u

theorem trace_sign_eq_sum (A : EndpointMatrix) :
    Matrix.trace (signMatrix * A) = ∑ i, endpointSign i * A i i := by
  rw [trace_sign_apply]
  norm_num [endpointSign, Fin.sum_univ_succ]
  simp only [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
  ring

theorem trace_sign_mul_trace_sign (A B : EndpointMatrix) :
    Matrix.trace (signMatrix * A) * Matrix.trace (signMatrix * B) =
      ∑ i, ∑ j, (endpointSign i * endpointSign j) * (A i i * B j j) := by
  norm_num [trace_sign_apply, endpointSign, Fin.sum_univ_succ]
  simp only [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
  ring

set_option maxHeartbeats 2000000 in
theorem trace_sign_product_eq_sum (A B : EndpointMatrix) :
    Matrix.trace (signMatrix * A * signMatrix * B) =
      ∑ i, ∑ j, (endpointSign i * endpointSign j) * (A i j * B j i) := by
  norm_num [Matrix.trace, signMatrix, endpointSign, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  ring

private theorem integral_double_sum {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f : Fin 4 → Fin 4 → Ω → ℂ)
    (hf : ∀ i j, Integrable (f i j) ν) :
    (∫ ω, ∑ i, ∑ j, f i j ω ∂ν) = ∑ i, ∑ j, ∫ ω, f i j ω ∂ν := by
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_finset_sum _ (fun j hj => hf i j)
  · intro i hi
    exact integrable_finset_sum _ (fun j hj => hf i j)

namespace EntryWickCovariance

variable {ι Ω : Type*} [MeasurableSpace Ω]
variable {ν : Measure Ω} {p sigma : ℂ} {kernel : ι → ι → ℂ}
variable {X : ι → Ω → EndpointMatrix}
variable (h : EntryWickCovariance ν p sigma kernel X)
include h

theorem integrable_sign_trace (w : ι) :
    Integrable (fun ω => Matrix.trace (signMatrix * X w ω)) ν := by
  simp_rw [trace_sign_eq_sum]
  exact integrable_finset_sum _ (fun i hi => (h.integrable_entry w i i).const_mul _)

theorem sign_trace_mean_zero (w : ι) :
    (∫ ω, Matrix.trace (signMatrix * X w ω) ∂ν) = 0 := by
  simp_rw [trace_sign_eq_sum]
  rw [integral_finset_sum _ (fun i hi => (h.integrable_entry w i i).const_mul _)]
  simp_rw [integral_const_mul, h.mean_zero]
  simp

theorem integrable_sign_trace_product (w u : ι) :
    Integrable (fun ω => Matrix.trace (signMatrix * X w ω) *
      Matrix.trace (signMatrix * X u ω)) ν := by
  simp_rw [trace_sign_mul_trace_sign]
  exact integrable_finset_sum _ (fun i hi => integrable_finset_sum _
    (fun j hj => (h.integrable_product w u i i j j).const_mul _))

theorem integrable_quadratic_trace (w u : ι) :
    Integrable (fun ω => Matrix.trace (signMatrix * X w ω * signMatrix * X u ω)) ν := by
  simp_rw [trace_sign_product_eq_sum]
  exact integrable_finset_sum _ (fun i hi => integrable_finset_sum _
    (fun j hj => (h.integrable_product w u i j j i).const_mul _))

/-- Wick covariance gives the coefficient `8 sigma² (1-p²)`. -/
theorem sign_trace_covariance (w u : ι) :
    (∫ ω, Matrix.trace (signMatrix * X w ω) *
      Matrix.trace (signMatrix * X u ω) ∂ν) =
      (8 * sigma ^ 2 * (1 - p ^ 2)) * kernel w u := by
  simp_rw [trace_sign_mul_trace_sign]
  rw [integral_double_sum ν _ (fun i j =>
    (h.integrable_product w u i i j j).const_mul _)]
  simp_rw [integral_const_mul, h.covariance]
  rw [covarianceMatrix_eq]
  norm_num [endpointSign, Fin.sum_univ_succ]
  ring

/-- The quadratic trace has coefficient `4 sigma² (1-p²)`. -/
theorem quadratic_trace_covariance (w u : ι) :
    (∫ ω, Matrix.trace (signMatrix * X w ω * signMatrix * X u ω) ∂ν) =
      (4 * sigma ^ 2 * (1 - p ^ 2)) * kernel w u := by
  simp_rw [trace_sign_product_eq_sum]
  rw [integral_double_sum ν _ (fun i j =>
    (h.integrable_product w u i j j i).const_mul _)]
  simp_rw [integral_const_mul, h.covariance]
  rw [covarianceMatrix_eq]
  norm_num [endpointSign, Fin.sum_univ_succ]
  ring

omit [MeasurableSpace Ω] h in
private theorem trace_mul_eq_sum (A B : EndpointMatrix) :
    Matrix.trace (A * B) = ∑ i, ∑ j, A i j * B j i := rfl

/-- Every fixed linear trace of the centered matrix has a genuine zero mean. -/
theorem integrable_linear_trace (A : EndpointMatrix) (w : ι) :
    Integrable (fun ω => Matrix.trace (A * X w ω)) ν := by
  simp_rw [trace_mul_eq_sum]
  exact integrable_finset_sum _ (fun i hi => integrable_finset_sum _
    (fun j hj => (h.integrable_entry w j i).const_mul _))

theorem linear_trace_mean_zero (A : EndpointMatrix) (w : ι) :
    (∫ ω, Matrix.trace (A * X w ω) ∂ν) = 0 := by
  simp_rw [trace_mul_eq_sum]
  rw [integral_double_sum ν _ (fun i j => (h.integrable_entry w j i).const_mul _)]
  simp_rw [integral_const_mul, h.mean_zero]
  simp

omit [MeasurableSpace Ω] h in
private theorem trace_shifted_product (H A B : EndpointMatrix) :
    Matrix.trace (signMatrix * (H + A) * signMatrix * (H + B)) =
      Matrix.trace (signMatrix * H * signMatrix * H) +
      Matrix.trace ((signMatrix * H * signMatrix) * A) +
      Matrix.trace ((signMatrix * H * signMatrix) * B) +
      Matrix.trace (signMatrix * A * signMatrix * B) := by
  have hcross : Matrix.trace (signMatrix * A * signMatrix * H) =
      Matrix.trace ((signMatrix * H * signMatrix) * A) := by
    calc
      _ = Matrix.trace ((signMatrix * A) * (signMatrix * H)) := by
        rw [Matrix.mul_assoc]
      _ = Matrix.trace ((signMatrix * H) * (signMatrix * A)) := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  simp only [mul_add, add_mul, Matrix.trace_add]
  rw [hcross]
  ring

theorem integrable_shifted_quadratic_trace [IsProbabilityMeasure ν]
    (g b : ℂ) (w u : ι) :
    Integrable (fun ω => Matrix.trace (signMatrix *
      (GeneralizedSwitching.meanMatrix g b 0 + X w ω) * signMatrix *
      (GeneralizedSwitching.meanMatrix g b 0 + X u ω))) ν := by
  let H := GeneralizedSwitching.meanMatrix g b 0
  have hc : Integrable (fun _ : Ω => Matrix.trace (signMatrix * H * signMatrix * H)) ν :=
    integrable_const _
  have hw := h.integrable_linear_trace (signMatrix * H * signMatrix) w
  have hu := h.integrable_linear_trace (signMatrix * H * signMatrix) u
  have hq := h.integrable_quadratic_trace w u
  simp_rw [trace_shifted_product]
  exact ((hc.add hw).add hu).add hq

/-- Translation by the deterministic Gaussian mean retains only its square
and the Wick quadratic contraction; the two cross terms have zero mean. -/
theorem shifted_quadratic_trace [IsProbabilityMeasure ν] (g b : ℂ) (w u : ι) :
    (∫ ω, Matrix.trace (signMatrix * (GeneralizedSwitching.meanMatrix g b 0 + X w ω) *
      signMatrix * (GeneralizedSwitching.meanMatrix g b 0 + X u ω)) ∂ν) =
      4 * (g ^ 2 - b ^ 2) + (4 * sigma ^ 2 * (1 - p ^ 2)) * kernel w u := by
  let H := GeneralizedSwitching.meanMatrix g b 0
  have hc : Integrable (fun _ : Ω => Matrix.trace (signMatrix * H * signMatrix * H)) ν :=
    integrable_const _
  have hw := h.integrable_linear_trace (signMatrix * H * signMatrix) w
  have hu := h.integrable_linear_trace (signMatrix * H * signMatrix) u
  have hq := h.integrable_quadratic_trace w u
  simp_rw [trace_shifted_product]
  have hi1 := integral_add hc hw
  have hi2 := integral_add (hc.add hw) hu
  have hi3 := integral_add ((hc.add hw).add hu) hq
  simp only [Pi.add_apply] at hi1 hi2 hi3
  rw [hi3, hi2, hi1, h.linear_trace_mean_zero, h.linear_trace_mean_zero,
    h.quadratic_trace_covariance]
  simp [H, trace_sign_mean_product]

/-- The full polynomial drift is integrable, independently of the convention
for a nonintegrable Bochner integral. -/
theorem integrable_shifted_drift [IsProbabilityMeasure ν] (g b : ℂ) (w : ι) :
    Integrable (fun ω => Matrix.trace (signMatrix * matrixResponse
      (GeneralizedSwitching.meanMatrix g b 0 + X w ω))) ν := by
  let H := GeneralizedSwitching.meanMatrix g b 0
  have hl : Integrable (fun ω => Matrix.trace (GeneralizedSwitching.edgeMatrix *
      (H + X w ω))) ν := by
    simp_rw [mul_add, Matrix.trace_add]
    exact (integrable_const _).add (h.integrable_linear_trace _ w)
  have hq := h.integrable_shifted_quadratic_trace g b w w
  simp_rw [trace_matrixResponse]
  exact (hl.const_mul 2).add (hq.const_mul 2)

/-- Wick entry covariance and zero means determine the full polynomial drift. -/
theorem shifted_drift [IsProbabilityMeasure ν] (g b : ℂ) (w : ι) :
    (∫ ω, Matrix.trace (signMatrix * matrixResponse
      (GeneralizedSwitching.meanMatrix g b 0 + X w ω)) ∂ν) =
      8 * (g ^ 2 - b ^ 2 + b) + (8 * sigma ^ 2 * (1 - p ^ 2)) * kernel w w := by
  let H := GeneralizedSwitching.meanMatrix g b 0
  have hl : Integrable (fun ω => Matrix.trace (GeneralizedSwitching.edgeMatrix *
      (H + X w ω))) ν := by
    simp_rw [mul_add, Matrix.trace_add]
    exact (integrable_const _).add (h.integrable_linear_trace _ w)
  have hq := h.integrable_shifted_quadratic_trace g b w w
  have hmean : (∫ ω, Matrix.trace (GeneralizedSwitching.edgeMatrix *
      (H + X w ω)) ∂ν) = 4 * b := by
    simp_rw [mul_add, Matrix.trace_add]
    rw [integral_add (integrable_const _) (h.integrable_linear_trace _ w),
      h.linear_trace_mean_zero]
    simp [H, trace_edge_mean]
  simp_rw [trace_matrixResponse]
  rw [integral_add (hl.const_mul 2) (hq.const_mul 2), integral_const_mul,
    integral_const_mul, hmean, h.shifted_quadratic_trace]
  ring

end EntryWickCovariance
/-- The concrete closed-form parameters turn the computed Wick drift into
`κ (kernel(w,w) + v² + 1)`, the conditional scalar loop drift. -/
theorem calibrated_wick_drift {ι Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] (P : Parameters)
    {kernel : ι → ι → ℂ} {X : ι → Ω → EndpointMatrix}
    (h : EntryWickCovariance ν (P.p : ℂ) (P.scale : ℂ) kernel X)
    (v : ℂ) (w : ι) :
    (∫ ω, Matrix.trace (signMatrix * matrixResponse
      (GeneralizedSwitching.meanMatrix
        ((P.center : ℂ) + (P.scale : ℂ) * v)
        ((P.p : ℂ) * ((P.center : ℂ) + (P.scale : ℂ) * v) + (P.r : ℂ)) 0 +
        X w ω)) ∂ν) =
      (P.contractionCoefficient : ℂ) * (kernel w w + v ^ 2 + 1) := by
  rw [h.shifted_drift, P.complex_scalar_polynomial]
  unfold Parameters.contractionCoefficient
  push_cast
  ring

end GeneralizedBulk
