import Mathlib

/-! Box smoothing of actual bounded measurable scalar functions. -/
noncomputable section
open MeasureTheory
open scoped Topology

namespace GeneralizedBulk.Entropy

def boxAverage (f : ℝ → ℝ) (ℓ x : ℝ) : ℝ :=
  (2*ℓ)⁻¹ * ∫ z in (x-ℓ)..(x+ℓ),f z

theorem intervalIntegrable_of_unit_bounded (f : ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) (hf1 : ∀ x,f x ≤ 1) (a b : ℝ) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff']
  apply Measure.integrableOn_of_bounded isCompact_uIcc.measure_ne_top hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hf0 x)]; exact hf1 x)

theorem boxAverage_nonneg (f : ℝ → ℝ) (ℓ : ℝ) (hℓ : 0 < ℓ) (hf0 : ∀ x,0 ≤ f x) (x : ℝ) :
    0 ≤ boxAverage f ℓ x := by
  apply mul_nonneg (by positivity)
  exact intervalIntegral.integral_nonneg (by linarith) (fun z hz => hf0 z)

theorem boxAverage_le_one (f : ℝ → ℝ) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hf : Measurable f) (hf0 : ∀ x,0 ≤ f x) (hf1 : ∀ x,f x ≤ 1) (x : ℝ) :
    boxAverage f ℓ x ≤ 1 := by
  have hI := intervalIntegral.integral_mono (show x-ℓ ≤ x+ℓ by linarith)
    (intervalIntegrable_of_unit_bounded f hf hf0 hf1 _ _) intervalIntegrable_const hf1
  simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one] at hI
  have hpos : 0 < 2*ℓ := by positivity
  dsimp only [boxAverage]
  have h := mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hpos.le)
  have he : (2*ℓ)⁻¹*((x+ℓ)-(x-ℓ)) = 1 := by field_simp; ring
  rwa [he] at h

theorem boxAverage_abs_sub_le (f : ℝ → ℝ) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hf : Measurable f) (hf0 : ∀ x,0 ≤ f x) (hf1 : ∀ x,f x ≤ 1) (x y : ℝ) :
    |boxAverage f ℓ x-boxAverage f ℓ y| ≤ ℓ⁻¹*|x-y| := by
  have hi (a b : ℝ) : IntervalIntegrable f volume a b := intervalIntegrable_of_unit_bounded f hf hf0 hf1 a b
  have hnorm (a b : ℝ) : |∫ z in a..b,f z| ≤ |b-a| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (a := a) (b := b)
      (fun z hz => by rw [Real.norm_eq_abs,abs_of_nonneg (hf0 z)]; exact hf1 z)
    rw [Real.norm_eq_abs,one_mul] at h
    exact h
  have hsub := intervalIntegral.integral_interval_sub_interval_comm
    (hi (x-ℓ) (x+ℓ)) (hi (y-ℓ) (y+ℓ)) (hi (x-ℓ) (y-ℓ))
  have hA := hnorm (x-ℓ) (y-ℓ)
  have hB := hnorm (x+ℓ) (y+ℓ)
  have hlen1 : (y-ℓ)-(x-ℓ) = y-x := by ring
  have hlen2 : (y+ℓ)-(x+ℓ) = y-x := by ring
  rw [hlen1] at hA
  rw [hlen2] at hB
  dsimp only [boxAverage]
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (2*ℓ)⁻¹),hsub]
  calc
    _ ≤ (2*ℓ)⁻¹*(|∫ z in (x-ℓ)..(y-ℓ),f z|+|∫ z in (x+ℓ)..(y+ℓ),f z|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
    _ ≤ (2*ℓ)⁻¹*(|y-x|+|y-x|) := mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
    _ = _ := by rw [abs_sub_comm y x]; field_simp; ring

theorem boxAverage_lipschitz (f : ℝ → ℝ) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hf : Measurable f) (hf0 : ∀ x,0 ≤ f x) (hf1 : ∀ x,f x ≤ 1) :
    LipschitzWith ⟨ℓ⁻¹,by positivity⟩ (boxAverage f ℓ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact boxAverage_abs_sub_le f ℓ hℓ hf hf0 hf1 x y

theorem boxAverage_eq_primitive (f : ℝ → ℝ) (hf : Continuous f) (ℓ x : ℝ) :
    boxAverage f ℓ x = (2*ℓ)⁻¹*((∫ z in (0 : ℝ)..(x+ℓ),f z)-(∫ z in (0 : ℝ)..(x-ℓ),f z)) := by
  rw [intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable 0 (x+ℓ)) (hf.intervalIntegrable 0 (x-ℓ))]
  rfl

theorem hasDerivAt_boxAverage (f : ℝ → ℝ) (hf : Continuous f) (ℓ x : ℝ) :
    HasDerivAt (boxAverage f ℓ) ((2*ℓ)⁻¹*(f (x+ℓ)-f (x-ℓ))) x := by
  have hp := intervalIntegral.integral_hasDerivAt_right
    (a := 0) (b := x+ℓ) (hf.intervalIntegrable 0 (x+ℓ)) hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hm := intervalIntegral.integral_hasDerivAt_right
    (a := 0) (b := x-ℓ) (hf.intervalIntegrable 0 (x-ℓ)) hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have h := ((hp.comp x ((hasDerivAt_id x).add_const ℓ)).sub
    (hm.comp x ((hasDerivAt_id x).sub_const ℓ))).const_mul ((2*ℓ)⁻¹)
  have he : boxAverage f ℓ = fun y => (2*ℓ)⁻¹*((∫ z in (0 : ℝ)..(y+ℓ),f z)-(∫ z in (0 : ℝ)..(y-ℓ),f z)) :=
    funext (boxAverage_eq_primitive f hf ℓ)
  rw [he]
  simpa only [mul_one,Function.comp_def,id_eq] using h

theorem contDiff_one_boxAverage (f : ℝ → ℝ) (hf : Continuous f) (ℓ : ℝ) :
    ContDiff ℝ 1 (boxAverage f ℓ) := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun x => (hasDerivAt_boxAverage f hf ℓ x).differentiableAt
  · have he : deriv (boxAverage f ℓ) = fun x => (2*ℓ)⁻¹*(f (x+ℓ)-f (x-ℓ)) :=
      funext (fun x => (hasDerivAt_boxAverage f hf ℓ x).deriv)
    rw [he]
    fun_prop

end GeneralizedBulk.Entropy
