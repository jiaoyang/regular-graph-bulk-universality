import Mathlib

/-! Uniform scalar Gaussian probabilities of finite quantizer-transition
intervals. The mean is arbitrary and the variance lower bound is explicit. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal ENNReal

namespace GeneralizedBulk.Entropy

theorem gaussianPDFReal_uniform_le (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v x ≤ (Real.sqrt (2*Real.pi*v))⁻¹ := by
  have he : Real.exp (-(x-m)^2/(2*(v : ℝ))) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  exact (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (Real.sqrt (2*Real.pi*v))⁻¹)).trans_eq (mul_one _)

theorem gaussianReal_real_le_density_bound (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (s : Set ℝ) (hs : volume s < ⊤) :
    (gaussianReal m v).real s ≤ (Real.sqrt (2*Real.pi*v))⁻¹*volume.real s := by
  rw [measureReal_def,gaussianReal_apply_eq_integral m hv,ENNReal.toReal_ofReal
    (integral_nonneg (fun x => gaussianPDFReal_nonneg m v x))]
  have hc : IntegrableOn (fun _x : ℝ => (Real.sqrt (2*Real.pi*v))⁻¹) s volume :=
    integrableOn_const.mpr (Or.inr hs)
  have h := integral_mono_ae (integrable_gaussianPDFReal m v).restrict hc
    (Filter.Eventually.of_forall (gaussianPDFReal_uniform_le m v))
  simpa only [setIntegral_const,smul_eq_mul,mul_comm] using h

theorem gaussianReal_interval_probability_le (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (a b : ℝ) (hab : a ≤ b) :
    (gaussianReal m v).real (Set.Icc a b) ≤ (b-a)/(Real.sqrt (2*Real.pi*v)) := by
  have h := gaussianReal_real_le_density_bound m v hv (Set.Icc a b) isCompact_Icc.measure_lt_top
  rw [Real.volume_real_Icc_of_le hab] at h
  simpa only [div_eq_mul_inv,mul_comm] using h

def transitionIntervals (F : Finset ℝ) (ℓ : ℝ) : Set ℝ :=
  ⋃ b ∈ F,Set.Icc (b-2*ℓ) (b+2*ℓ)

theorem measurableSet_transitionIntervals (F : Finset ℝ) (ℓ : ℝ) : MeasurableSet (transitionIntervals F ℓ) :=
  MeasurableSet.biUnion F.countable_toSet (fun b hb => measurableSet_Icc)

set_option maxHeartbeats 1000000 in
theorem gaussianReal_transition_probability_le (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (F : Finset ℝ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    (gaussianReal m v).real (transitionIntervals F ℓ) ≤
      (F.card : ℝ)*(4*ℓ)/(Real.sqrt (2*Real.pi*v)) := by
  apply (measureReal_biUnion_finset_le F (fun b => Set.Icc (b-2*ℓ) (b+2*ℓ))).trans
  calc
    _ ≤ ∑ _b ∈ F,(4*ℓ)/(Real.sqrt (2*Real.pi*v)) := by
      apply Finset.sum_le_sum
      intro b hb
      have h := gaussianReal_interval_probability_le m v hv (b-2*ℓ) (b+2*ℓ) (by linarith)
      convert h using 1 <;> ring
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem gaussianReal_transition_probability_le_of_variance_lower_bound
    (m : ℝ) (v : ℝ≥0) (v₀ : ℝ) (hv₀ : 0 < v₀) (hvar : v₀ ≤ v)
    (F : Finset ℝ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    (gaussianReal m v).real (transitionIntervals F ℓ) ≤
      (F.card : ℝ)*(4*ℓ)/(Real.sqrt (2*Real.pi*v₀)) := by
  have hv : v ≠ 0 := by intro he; simp only [he,NNReal.coe_zero] at hvar; linarith
  apply (gaussianReal_transition_probability_le m v hv F ℓ hℓ).trans
  apply div_le_div_of_nonneg_left (by positivity)
    (Real.sqrt_pos.mpr (by positivity))
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hvar (by positivity))

end GeneralizedBulk.Entropy
