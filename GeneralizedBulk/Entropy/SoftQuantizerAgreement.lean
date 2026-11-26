import GeneralizedBulk.Entropy.SoftQuantizer

/-! Double-box smoothing agrees exactly with a hard label away from
quantizer transitions within distance 2ℓ. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy

theorem boxAverage_eq_const_of_local (f : ℝ → ℝ) (ℓ : ℝ) (hℓ : 0 < ℓ) (x c : ℝ)
    (hf : ∀ z ∈ Set.Icc (x-ℓ) (x+ℓ),f z = c) : boxAverage f ℓ x = c := by
  have hle : x-ℓ ≤ x+ℓ := by linarith
  have he := intervalIntegral.integral_congr (μ := volume) (f := f) (g := fun _ => c) (a := x-ℓ) (b := x+ℓ)
    (by simpa only [Set.uIcc_of_le hle] using hf)
  rw [boxAverage,he,intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  have hlen : (x+ℓ)-(x-ℓ) = 2*ℓ := by ring
  rw [hlen,← mul_assoc,inv_mul_cancel₀ (by positivity),one_mul]

variable {B : Type*} [Fintype B] [DecidableEq B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem softLabel_eq_hard_of_local_const (J : ℝ → B) (ℓ : ℝ) (hℓ : 0 < ℓ) (b : B) (x : ℝ)
    (hJ : ∀ z ∈ Set.Icc (x-2*ℓ) (x+2*ℓ),J z = J x) :
    softLabel J ℓ b x = hardLabel J b x := by
  apply boxAverage_eq_const_of_local _ ℓ hℓ x
  intro z hz
  apply boxAverage_eq_const_of_local _ ℓ hℓ z
  intro u hu
  have humem : u ∈ Set.Icc (x-2*ℓ) (x+2*ℓ) := by
    constructor <;> linarith [hz.1,hz.2,hu.1,hu.2]
  unfold hardLabel
  rw [hJ u humem]

def quantizerTransition (J : ℝ → B) (ℓ x : ℝ) : Prop :=
  ∃ z ∈ Set.Icc (x-2*ℓ) (x+2*ℓ),J z ≠ J x

theorem softLabel_eq_hard_of_no_transition (J : ℝ → B) (ℓ : ℝ) (hℓ : 0 < ℓ) (b : B) (x : ℝ)
    (hJ : ¬ quantizerTransition J ℓ x) : softLabel J ℓ b x = hardLabel J b x := by
  apply softLabel_eq_hard_of_local_const J ℓ hℓ b x
  intro z hz
  by_contra he
  exact hJ ⟨z,hz,he⟩

theorem softLabel_hard_l1_le_two (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ) (x : ℝ) :
    (∑ b,|hardLabel J b x-softLabel J ℓ b x|) ≤ 2 := by
  calc
    _ ≤ ∑ b,(hardLabel J b x+softLabel J ℓ b x) := by
      apply Finset.sum_le_sum
      intro b hb
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (hardLabel_nonneg J b x),abs_of_nonneg (softLabel_nonneg J ℓ hℓ b x)])
    _ = _ := by rw [Finset.sum_add_distrib,hardLabel_sum,softLabel_sum J hJ ℓ hℓ]; norm_num

set_option maxHeartbeats 1000000 in
theorem softLabel_hard_l1_le_transition (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ) (x : ℝ) :
    (∑ b,|hardLabel J b x-softLabel J ℓ b x|) ≤
      2*(if quantizerTransition J ℓ x then (1 : ℝ) else 0) := by
  classical
  by_cases ht : quantizerTransition J ℓ x
  · simpa only [if_pos ht,mul_one] using softLabel_hard_l1_le_two J hJ ℓ hℓ x
  · simp only [if_neg ht,mul_zero]
    simp_rw [softLabel_eq_hard_of_no_transition J ℓ hℓ _ x ht,sub_self,abs_zero]
    simp

end GeneralizedBulk.Entropy
