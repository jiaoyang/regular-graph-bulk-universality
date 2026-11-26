import BourgadeHuang.PointProcessModel
import Mathlib.Tactic.GCongr

/-!
# Counting estimates from particle resolvents

The count is over particle labels, so repeated eigenvalues have their full multiplicity.
The deterministic estimate is (4.57).  Its integrated version transfers a uniform
resolvent moment bound to the counting moment bound used in the last section.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace BourgadeHuang

def particleCount {N : ℕ} (x : Fin N → ℝ) (a b : ℝ) : ℝ :=
  ∑ i, if x i ∈ Set.Icc a b then 1 else 0

theorem particleCount_nonneg {N : ℕ} (x : Fin N → ℝ) (a b : ℝ) :
    0 ≤ particleCount x a b := by
  unfold particleCount
  exact Finset.sum_nonneg fun i _ => by split <;> norm_num

theorem particleCount_le_card {N : ℕ} (x : Fin N → ℝ) (a b : ℝ) :
    particleCount x a b ≤ N := by
  calc
    particleCount x a b ≤ ∑ _i : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      split <;> norm_num
    _ = N := by simp

theorem finite_dirac_count {N : ℕ} (x : Fin N → ℝ) (a b : ℝ) :
    ((∑ i, Measure.dirac (x i)) (Set.Icc a b)).toReal = particleCount x a b := by
  classical
  rw [Measure.finset_sum_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases h : x i ∈ Set.Icc a b <;> simp [Measure.dirac_apply, h]
  · intro i _
    by_cases h : x i ∈ Set.Icc a b <;> simp [Measure.dirac_apply, h]

theorem particleCount_le_resolvent {N : ℕ} (x : Fin N → ℝ) (center a b R : ℝ)
    (_hR : 0 ≤ R) (ha : -R ≤ a) (hb : b ≤ R) :
    particleCount x a b ≤ (1 + R ^ 2) * ‖microscopicResolvent x center Complex.I‖ := by
  have hpoint (i : Fin N) :
      (if x i ∈ Set.Icc a b then (1 : ℝ) else 0) ≤
        (1 + R ^ 2) * (Complex.normSq ((x i : ℂ) - Complex.I))⁻¹ := by
    have hnorm : Complex.normSq ((x i : ℂ) - Complex.I) = 1 + x i ^ 2 := by
      simp [Complex.normSq_apply, pow_two]
      ring
    rw [hnorm]
    by_cases h : x i ∈ Set.Icc a b
    · rw [if_pos h]
      have hx : |x i| ≤ R := abs_le.mpr ⟨ha.trans h.1, h.2.trans hb⟩
      have hs : x i ^ 2 ≤ R ^ 2 := by
        have hp := mul_nonneg (sub_nonneg.mpr (abs_le.mp hx).2)
          (show 0 ≤ R + x i by linarith [(abs_le.mp hx).1])
        nlinarith
      have hd : 0 < 1 + x i ^ 2 := by positivity
      rw [← div_eq_mul_inv, le_div_iff₀ hd]
      nlinarith
    · rw [if_neg h]
      positivity
  calc
    particleCount x a b ≤
        ∑ i, (1 + R ^ 2) * (Complex.normSq ((x i : ℂ) - Complex.I))⁻¹ :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = (1 + R ^ 2) * (microscopicResolvent x center Complex.I).im := by
      rw [microscopicResolvent_im_eq]
      simp [Finset.mul_sum]
    _ ≤ (1 + R ^ 2) * ‖microscopicResolvent x center Complex.I‖ := by
      exact mul_le_mul_of_nonneg_left (Complex.im_le_norm _) (by positivity)

theorem measurable_particleCount {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i)) (a b : ℝ) :
    Measurable (fun ω => particleCount (x ω) a b) := by
  classical
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_Icc.preimage (hx i)) measurable_const measurable_const

theorem integrable_particleCount_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {N : ℕ}
    (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i)) (a b : ℝ) (q : ℕ) :
    Integrable (fun ω => particleCount (x ω) a b ^ q) μ := by
  apply (integrable_const ((N : ℝ) ^ q)).mono'
    ((measurable_particleCount x hx a b).pow_const q).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (particleCount_nonneg _ _ _) _)]
    exact pow_le_pow_left₀ (particleCount_nonneg _ _ _) (particleCount_le_card _ _ _) _

theorem integral_particleCount_pow_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {N : ℕ}
    (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (center a b R : ℝ) (hR : 0 ≤ R) (ha : -R ≤ a) (hb : b ≤ R) (q : ℕ)
    (hmoment : Integrable (fun ω => ‖microscopicResolvent (x ω) center Complex.I‖ ^ q) μ) :
    (∫ ω, particleCount (x ω) a b ^ q ∂μ) ≤
      (1 + R ^ 2) ^ q * ∫ ω, ‖microscopicResolvent (x ω) center Complex.I‖ ^ q ∂μ := by
  rw [← integral_const_mul]
  apply integral_mono (integrable_particleCount_pow μ x hx a b q)
    (hmoment.const_mul _)
  intro ω
  dsimp only
  rw [← mul_pow]
  exact pow_le_pow_left₀ (particleCount_nonneg _ _ _)
    (particleCount_le_resolvent (x ω) center a b R hR ha hb) _

end BourgadeHuang
