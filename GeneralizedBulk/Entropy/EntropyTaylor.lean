import Mathlib

/-! A global cubic entropy remainder, including densities that vanish. -/
noncomputable section
open Set MeasureTheory

namespace GeneralizedBulk.Entropy

def entropyRemainder (x : ℝ) : ℝ :=
  x * Real.log x - (x - 1) - (x - 1) ^ 2 / 2

@[simp] theorem entropyRemainder_zero : entropyRemainder 0 = 1 / 2 := by
  norm_num [entropyRemainder]
@[simp] theorem entropyRemainder_one : entropyRemainder 1 = 0 := by
  norm_num [entropyRemainder]

theorem continuous_entropyRemainder : Continuous entropyRemainder := by
  exact Real.continuous_mul_log.sub (continuous_id.sub continuous_const) |>.sub
    ((continuous_id.sub continuous_const).pow 2 |>.div_const 2)

theorem hasDerivAt_entropyRemainder {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt entropyRemainder (Real.log x - x + 1) x := by
  convert ((Real.hasDerivAt_mul_log hx).sub ((hasDerivAt_id x).sub_const 1)).sub
    (((hasDerivAt_id x).sub_const 1).pow 2 |>.div_const 2) using 1 <;>
    dsimp [entropyRemainder] <;> ring

theorem entropyRemainder_antitone : AntitoneOn entropyRemainder (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    continuous_entropyRemainder.continuousOn
  · intro x hx
    simp only [interior_Ici, mem_Ioi] at hx
    exact (hasDerivAt_entropyRemainder (ne_of_gt hx)).hasDerivWithinAt
  · intro x hx
    simp only [interior_Ici, mem_Ioi] at hx
    linarith [Real.log_le_sub_one_of_pos hx]

def entropyRemainderBarrier (x : ℝ) : ℝ := entropyRemainder x + 4 * (x - 1) ^ 3

theorem entropyRemainderBarrier_monotone :
    MonotoneOn entropyRemainderBarrier (Ici (1 / 2)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (1 / 2))
    (continuous_entropyRemainder.add (continuous_const.mul
      ((continuous_id.sub continuous_const).pow 3))).continuousOn
  · intro x hx
    simp only [interior_Ici, mem_Ioi] at hx
    have hx0 : x ≠ 0 := by linarith
    convert ((hasDerivAt_entropyRemainder hx0).add
      ((((hasDerivAt_id x).sub_const 1).pow 3).const_mul 4)).hasDerivWithinAt using 1
  · intro x hx
    simp only [interior_Ici, mem_Ioi] at hx
    have hxpos : 0 < x := by linarith
    have hlog := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hxpos) hxpos.le
    have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hxpos)
    have hprod := mul_nonneg (show 0 ≤ 12 * x - 1 by linarith) (sq_nonneg (x - 1))
    dsimp
    nlinarith

/-- A uniform remainder bound for `x log x`, with the convention `0 log 0=0`.
In particular, no pointwise smallness condition on a density is required. -/
theorem entropyRemainder_abs_le (x : ℝ) (hx : 0 ≤ x) :
    |entropyRemainder x| ≤ 4 * |x - 1| ^ 3 := by
  by_cases hx1 : x ≤ 1
  · have hr0 : 0 ≤ entropyRemainder x := by
      simpa only [entropyRemainder_one] using
        entropyRemainder_antitone hx (by norm_num : (0 : ℝ) ≤ 1) hx1
    rw [abs_of_nonneg hr0, abs_of_nonpos (by linarith : x - 1 ≤ 0)]
    by_cases hxhalf : 1 / 2 ≤ x
    · have hb := entropyRemainderBarrier_monotone hxhalf (by norm_num : (1 / 2 : ℝ) ≤ 1) hx1
      dsimp [entropyRemainderBarrier] at hb
      rw [entropyRemainder_one] at hb
      nlinarith
    · have hbound := entropyRemainder_antitone (by norm_num : (0 : ℝ) ≤ 0) hx hx
      rw [entropyRemainder_zero] at hbound
      have hp : (1 / 2 : ℝ) ^ 3 ≤ (-(x - 1)) ^ 3 := by
        gcongr
        linarith
      norm_num at hp
      linarith
  · have hx1' : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
    have hr0 : entropyRemainder x ≤ 0 := by
      simpa only [entropyRemainder_one] using
        entropyRemainder_antitone (by norm_num : (0 : ℝ) ≤ 1) hx hx1'
    rw [abs_of_nonpos hr0, abs_of_nonneg (by linarith : 0 ≤ x - 1)]
    have hb := entropyRemainderBarrier_monotone (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (show 1 / 2 ≤ x by linarith) hx1'
    dsimp [entropyRemainderBarrier] at hb
    rw [entropyRemainder_one] at hb
    nlinarith

theorem entropy_taylor_abs_le (t : ℝ) (ht : -1 ≤ t) :
    |(1 + t) * Real.log (1 + t) - t - t ^ 2 / 2| ≤ 4 * |t| ^ 3 := by
  simpa [entropyRemainder] using entropyRemainder_abs_le (1 + t) (by linarith)

def relativeEntropy {S : Type*} [MeasurableSpace S] (μ : Measure S) (f : S → ℝ) : ℝ :=
  ∫ x, f x * Real.log (f x) ∂μ

/-- The global scalar remainder integrates for any nonnegative density with
finite third centered moment. Zeros of the density need no special exclusion. -/
theorem relativeEntropy_quadratic_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (f : S → ℝ) (hf : AEStronglyMeasurable f μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hu1 : Integrable (fun x => f x - 1) μ)
    (hu2 : Integrable (fun x => (f x - 1) ^ 2) μ)
    (hu3 : Integrable (fun x => |f x - 1| ^ 3) μ)
    (hzero : ∫ x, f x - 1 ∂μ = 0) :
    Integrable (fun x => f x * Real.log (f x)) μ ∧
      |relativeEntropy μ f - (1 / 2 : ℝ) * ∫ x, (f x - 1) ^ 2 ∂μ| ≤
        4 * ∫ x, |f x - 1| ^ 3 ∂μ := by
  have hbound : ∀ᵐ x ∂μ, ‖entropyRemainder (f x)‖ ≤ 4 * |f x - 1| ^ 3 :=
    hpos.mono (fun x hx => entropyRemainder_abs_le (f x) hx)
  have hR : Integrable (fun x => entropyRemainder (f x)) μ :=
    (hu3.const_mul 4).mono'
      (continuous_entropyRemainder.comp_aestronglyMeasurable hf) hbound
  have hInt : Integrable (fun x => f x * Real.log (f x)) μ := by
    convert hR.add (hu1.add (hu2.div_const 2)) using 1
    funext x
    dsimp [entropyRemainder]
    ring
  refine ⟨hInt, ?_⟩
  have hidentity : (∫ x, entropyRemainder (f x) ∂μ) =
      relativeEntropy μ f - (1 / 2 : ℝ) * ∫ x, (f x - 1) ^ 2 ∂μ := by
    calc
      _ = (∫ x, f x * Real.log (f x) - (f x - 1) ∂μ) -
          ∫ x, (f x - 1) ^ 2 / 2 ∂μ := integral_sub (hInt.sub hu1) (hu2.div_const 2)
      _ = _ := by
        rw [integral_sub hInt hu1, integral_div, hzero]
        unfold relativeEntropy
        ring
  rw [← hidentity]
  have h := norm_integral_le_of_norm_le (hu3.const_mul 4) hbound
  simpa only [Real.norm_eq_abs, integral_const_mul] using h

theorem relativeEntropy_quadratic_bound_of_memLp_three {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] (f : S → ℝ)
    (hu : MemLp (fun x => f x - 1) 3 μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hzero : ∫ x, f x - 1 ∂μ = 0) :
    Integrable (fun x => f x * Real.log (f x)) μ ∧
      |relativeEntropy μ f - (1 / 2 : ℝ) * ∫ x, (f x - 1) ^ 2 ∂μ| ≤
        4 * ∫ x, |f x - 1| ^ 3 ∂μ := by
  have hf : AEStronglyMeasurable f μ := by
    have hconst : AEStronglyMeasurable (fun _ : S => (1 : ℝ)) μ := aestronglyMeasurable_const
    convert hu.aestronglyMeasurable.add hconst using 1
    funext x
    simp only [Pi.add_apply]
    ring
  have hu2 : Integrable (fun x => (f x - 1) ^ 2) μ :=
    (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mp
      (hu.mono_exponent (by norm_num))
  have hu3 : Integrable (fun x => |f x - 1| ^ 3) μ := by
    simpa only [Real.norm_eq_abs] using hu.integrable_norm_pow (by decide : (3 : ℕ) ≠ 0)
  exact relativeEntropy_quadratic_bound μ f hf hpos
    (MemLp.integrable (by norm_num) hu) hu2 hu3 hzero

end GeneralizedBulk.Entropy
