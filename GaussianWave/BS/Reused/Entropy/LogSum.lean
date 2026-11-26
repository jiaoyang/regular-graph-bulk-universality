import Mathlib

/-! Finite log-sum convexity and its nonnegative relative-entropy integrand. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS.Reused.Entropy
variable {S : Type*} [Fintype S]

theorem positive_weighted_sum (weight f : S → ℝ) (hw : ∀ s, 0 ≤ weight s)
    (htotal : ∑ s, weight s = 1) (hf : ∀ s, 0 < f s) : 0 < ∑ s, weight s * f s := by
  have hex : ∃ s, 0 < weight s := by
    by_contra h
    push_neg at h
    have hh : (∑ s, weight s) ≤ 0 := Finset.sum_nonpos (fun s _ => h s)
    linarith
  obtain ⟨s, hs⟩ := hex
  exact Finset.sum_pos' (fun t _ => mul_nonneg (hw t) (hf t).le)
    ⟨s, Finset.mem_univ s, mul_pos hs (hf s)⟩

/-- The finite log-sum inequality, including zero mixture weights, derived
from the elementary logarithm bound. Component densities remain positive. -/
theorem log_sum_inequality (weight f g : S → ℝ) (hw : ∀ s, 0 ≤ weight s)
    (htotal : ∑ s, weight s = 1) (hf : ∀ s, 0 < f s) (hg : ∀ s, 0 < g s) :
    (∑ s, weight s * f s) * Real.log ((∑ s, weight s * f s) / (∑ s, weight s * g s)) ≤
      ∑ s, weight s * f s * Real.log (f s / g s) := by
  let A := ∑ s, weight s * f s
  let B := ∑ s, weight s * g s
  have hA : 0 < A := positive_weighted_sum weight f hw htotal hf
  have hB : 0 < B := positive_weighted_sum weight g hw htotal hg
  have hlog (s : S) : Real.log (g s * A / (f s * B)) =
      -Real.log (f s / g s) + Real.log (A / B) := by
    rw [Real.log_div (ne_of_gt (mul_pos (hg s) hA)) (ne_of_gt (mul_pos (hf s) hB)),
      Real.log_mul (ne_of_gt (hg s)) (ne_of_gt hA),
      Real.log_mul (ne_of_gt (hf s)) (ne_of_gt hB),
      Real.log_div (ne_of_gt (hf s)) (ne_of_gt (hg s)),
      Real.log_div (ne_of_gt hA) (ne_of_gt hB)]
    ring
  have hs (s : S) : weight s * f s * (-Real.log (f s / g s) + Real.log (A / B)) ≤
      (A / B) * (weight s * g s) - weight s * f s := by
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (mul_pos (hg s) hA) (mul_pos (hf s) hB)))
      (mul_nonneg (hw s) (hf s).le)
    rw [hlog] at h
    convert h using 1
    field_simp [ne_of_gt (hf s), ne_of_gt hB]
    ring
  have h := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hs s)
  have hleft : (∑ s, weight s * f s * (-Real.log (f s / g s) + Real.log (A / B))) =
      -(∑ s, weight s * f s * Real.log (f s / g s)) + A * Real.log (A / B) := by
    simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul]
    rfl
  have hright : (∑ s, ((A / B) * (weight s * g s) - weight s * f s)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    change A / B * B - A = 0
    field_simp
  rw [hleft, hright] at h
  change A * Real.log (A / B) ≤ _
  linarith

def klIntegrand (f g : ℝ) : ℝ := f * Real.log (f / g) - f + g

theorem klIntegrand_nonneg (f g : ℝ) (hf : 0 < f) (hg : 0 < g) : 0 ≤ klIntegrand f g := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hg hf)) hf.le
  have he : Real.log (g / f) = -Real.log (f / g) := by
    rw [Real.log_div (ne_of_gt hg) (ne_of_gt hf), Real.log_div (ne_of_gt hf) (ne_of_gt hg)]
    ring
  rw [he] at h
  have hr : f * (g / f - 1) = g - f := by field_simp
  rw [hr] at h
  unfold klIntegrand
  linarith

theorem klIntegrand_mixture_le (weight f g : S → ℝ) (hw : ∀ s, 0 ≤ weight s)
    (htotal : ∑ s, weight s = 1) (hf : ∀ s, 0 < f s) (hg : ∀ s, 0 < g s) :
    klIntegrand (∑ s, weight s * f s) (∑ s, weight s * g s) ≤
      ∑ s, weight s * klIntegrand (f s) (g s) := by
  have h := log_sum_inequality weight f g hw htotal hf hg
  simp only [mul_assoc] at h
  unfold klIntegrand
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linarith

/-- Joint convexity for actual positive density functions. Integrability of
the mixed divergence is obtained from the proved nonnegative pointwise bound. -/
theorem integral_kl_mixture_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (weight : S → ℝ) (f g : S → X → ℝ) (hw : ∀ s, 0 ≤ weight s)
    (htotal : ∑ s, weight s = 1) (hf : ∀ s x, 0 < f s x) (hg : ∀ s x, 0 < g s x)
    (hmf : ∀ s, Measurable (f s)) (hmg : ∀ s, Measurable (g s))
    (hInt : ∀ s, Integrable (fun x => klIntegrand (f s x) (g s x)) μ) :
    Integrable (fun x => klIntegrand (∑ s, weight s * f s x) (∑ s, weight s * g s x)) μ ∧
      (∫ x, klIntegrand (∑ s, weight s * f s x) (∑ s, weight s * g s x) ∂μ) ≤
        ∑ s, weight s * ∫ x, klIntegrand (f s x) (g s x) ∂μ := by
  have hF : Measurable (fun x => ∑ s, weight s * f s x) :=
    Finset.measurable_sum _ (fun s _ => measurable_const.mul (hmf s))
  have hG : Measurable (fun x => ∑ s, weight s * g s x) :=
    Finset.measurable_sum _ (fun s _ => measurable_const.mul (hmg s))
  have hM : Measurable (fun x => klIntegrand (∑ s, weight s * f s x) (∑ s, weight s * g s x)) :=
    ((hF.mul (hF.div hG).log).sub hF).add hG
  have hmajor : Integrable (fun x => ∑ s, weight s * klIntegrand (f s x) (g s x)) μ :=
    integrable_finset_sum _ (fun s _ => (hInt s).const_mul (weight s))
  have hbound (x : X) : klIntegrand (∑ s, weight s * f s x) (∑ s, weight s * g s x) ≤
      ∑ s, weight s * klIntegrand (f s x) (g s x) :=
    klIntegrand_mixture_le weight (fun s => f s x) (fun s => g s x) hw htotal
      (fun s => hf s x) (fun s => hg s x)
  have hmix : Integrable (fun x => klIntegrand (∑ s, weight s * f s x) (∑ s, weight s * g s x)) μ := by
    apply hmajor.mono' hM.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (klIntegrand_nonneg _ _
      (positive_weighted_sum weight _ hw htotal (fun s => hf s x))
      (positive_weighted_sum weight _ hw htotal (fun s => hg s x)))]
    exact hbound x
  refine ⟨hmix, ?_⟩
  calc
    _ ≤ ∫ x, ∑ s, weight s * klIntegrand (f s x) (g s x) ∂μ := integral_mono hmix hmajor hbound
    _ = _ := by
      rw [integral_finset_sum _ (fun s _ => (hInt s).const_mul (weight s))]
      simp_rw [integral_const_mul]

end GaussianWave.BS.Reused.Entropy

namespace GaussianWave.BS.Reused.Entropy

/-- The log-sum inequality for arbitrary integrable positive functions.
This is proved directly from the logarithm tangent inequality. -/
theorem integral_log_sum_inequality
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (f g : Y → ℝ)
    (hf : ∀ y, 0 < f y) (hg : ∀ y, 0 < g y)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hlog : Integrable (fun y => f y * Real.log (f y / g y)) μ)
    (hA : 0 < ∫ y, f y ∂μ) (hB : 0 < ∫ y, g y ∂μ) :
    (∫ y, f y ∂μ) * Real.log ((∫ y, f y ∂μ) / (∫ y, g y ∂μ)) ≤
      ∫ y, f y * Real.log (f y / g y) ∂μ := by
  let A := ∫ y, f y ∂μ
  let B := ∫ y, g y ∂μ
  have hp (y : Y) :
      -(f y * Real.log (f y / g y)) + f y * Real.log (A / B) ≤
        (A / B) * g y - f y := by
    have hl := Real.log_le_sub_one_of_pos
      (div_pos (mul_pos (hg y) hA) (mul_pos (hf y) hB))
    have he : Real.log (g y * A / (f y * B)) =
        -Real.log (f y / g y) + Real.log (A / B) := by
      rw [Real.log_div (mul_pos (hg y) hA).ne' (mul_pos (hf y) hB).ne',
        Real.log_mul (hg y).ne' hA.ne', Real.log_mul (hf y).ne' hB.ne',
        Real.log_div (hf y).ne' (hg y).ne', Real.log_div hA.ne' hB.ne']
      ring
    have hh := mul_le_mul_of_nonneg_left hl (hf y).le
    rw [he] at hh
    convert hh using 1
    · ring
    · field_simp [(hf y).ne', hB.ne']
      <;> ring
  have hi := integral_mono (hlog.neg.add (hfi.mul_const _))
    ((hgi.const_mul _).sub hfi) hp
  change (∫ y, -(f y * Real.log (f y / g y)) + f y * Real.log (A / B) ∂μ) ≤
    ∫ y, (A / B) * g y - f y ∂μ at hi
  rw [integral_add (f := fun y => -(f y * Real.log (f y / g y)))
      hlog.neg (hfi.mul_const _), integral_neg, integral_mul_const,
    integral_sub (f := fun y => (A / B) * g y) (hgi.const_mul _) hfi,
    integral_const_mul] at hi
  change -(∫ y, f y * Real.log (f y / g y) ∂μ) + A * Real.log (A / B) ≤
    A / B * B - A at hi
  rw [div_mul_cancel₀ A hB.ne'] at hi
  linarith

/-- Joint convexity of corrected relative-entropy integrands under an
arbitrary integral, without a finite-mixture restriction. -/
theorem klIntegrand_integral_le
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (f g : Y → ℝ)
    (hf : ∀ y, 0 < f y) (hg : ∀ y, 0 < g y)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hlog : Integrable (fun y => f y * Real.log (f y / g y)) μ)
    (hA : 0 < ∫ y, f y ∂μ) (hB : 0 < ∫ y, g y ∂μ) :
    klIntegrand (∫ y, f y ∂μ) (∫ y, g y ∂μ) ≤
      ∫ y, klIntegrand (f y) (g y) ∂μ := by
  have h := integral_log_sum_inequality μ f g hf hg hfi hgi hlog hA hB
  unfold klIntegrand
  rw [integral_add (f := fun y => f y * Real.log (f y / g y) - f y)
    (hlog.sub hfi) hgi,
    integral_sub (f := fun y => f y * Real.log (f y / g y)) hlog hfi]
  linarith

end GaussianWave.BS.Reused.Entropy
