import Mathlib

/-! A finite dependency bound proved from actual pair independence. It will
be applied to edge indicators of the literal independent recoloring law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
set_option maxHeartbeats 600000

namespace GaussianWave.BS.Lower

variable {Ω I : Type*} [MeasurableSpace Ω] [Finite Ω] [MeasurableSingletonClass Ω]
  [Fintype I] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A sum of `[0,1]` observations with at most `B` dependent partners per
observation has centered second moment at most `|I| B`. No concentration
conclusion is supplied as an assumption. -/
theorem integral_centered_sum_sq_le (X : I → Ω → ℝ)
    (hX0 : ∀ i ω,0 ≤ X i ω) (hX1 : ∀ i ω,X i ω ≤ 1)
    (bad : I → Finset I) (B : ℕ) (hbad : ∀ i,(bad i).card ≤ B)
    (hindep : ∀ i j,j ∉ bad i → IndepFun (X i) (X j) μ) :
    (∫ ω,(∑ i,(X i ω-(∫ z,X i z ∂μ)))^2 ∂μ) ≤ (Fintype.card I : ℝ)*B := by
  let E (i : I) := ∫ ω,X i ω ∂μ
  let Y (i : I) (ω : Ω) := X i ω-E i
  have hE0 (i : I) : 0 ≤ E i := integral_nonneg (hX0 i)
  have hE1 (i : I) : E i ≤ 1 := by
    have h := integral_mono (Integrable.of_finite : Integrable (X i) μ)
      (integrable_const (1 : ℝ)) (hX1 i)
    simpa only [integral_const,measureReal_univ_eq_one,one_smul] using h
  have hYabs (i : I) (ω : Ω) : |Y i ω| ≤ 1 := by
    apply abs_le.mpr
    dsimp [Y]
    constructor <;> linarith [hX0 i ω,hX1 i ω,hE0 i,hE1 i]
  have hYmean (i : I) : (∫ ω,Y i ω ∂μ) = 0 := by
    dsimp only [Y]
    rw [integral_sub Integrable.of_finite (integrable_const _),integral_const]
    simp only [measureReal_univ_eq_one,one_smul,E,sub_self]
  have hcov0 (i j : I) (hji : j ∉ bad i) : (∫ ω,Y i ω*Y j ω ∂μ) = 0 := by
    have hYij : IndepFun (Y i) (Y j) μ :=
      (hindep i j hji).comp (measurable_id.sub_const (E i)) (measurable_id.sub_const (E j))
    have h := hYij.integral_mul_of_integrable Integrable.of_finite Integrable.of_finite
    simpa only [Pi.mul_apply,hYmean,mul_zero] using h
  have hcov1 (i j : I) : (∫ ω,Y i ω*Y j ω ∂μ) ≤ 1 := by
    have hpoint (ω : Ω) : Y i ω*Y j ω ≤ 1 := by
      calc
        _ ≤ |Y i ω*Y j ω| := le_abs_self _
        _ = |Y i ω| * |Y j ω| := abs_mul _ _
        _ ≤ 1*1 := mul_le_mul (hYabs i ω) (hYabs j ω) (abs_nonneg _) (by norm_num)
        _ = _ := by norm_num
    have h := integral_mono (Integrable.of_finite : Integrable (fun ω => Y i ω*Y j ω) μ)
      (integrable_const (1 : ℝ)) hpoint
    simpa only [integral_const,measureReal_univ_eq_one,one_smul] using h
  have hcov (i j : I) : (∫ ω,Y i ω*Y j ω ∂μ) ≤ if j ∈ bad i then (1 : ℝ) else 0 := by
    by_cases hji : j ∈ bad i
    · simpa only [if_pos hji] using hcov1 i j
    · simp only [if_neg hji,hcov0 i j hji,le_refl]
  have hsq (ω : Ω) : (∑ i,Y i ω)^2 = ∑ i,∑ j,Y i ω*Y j ω := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  change (∫ ω,(∑ i,Y i ω)^2 ∂μ) ≤ _
  simp_rw [hsq]
  rw [integral_finset_sum _ (fun i _ => Integrable.of_finite)]
  simp_rw [integral_finset_sum _ (fun j _ => Integrable.of_finite)]
  calc
    _ ≤ ∑ i : I,∑ j : I,if j ∈ bad i then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcov i j))
    _ = ∑ i : I,((bad i).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [← Finset.sum_filter]
      simp
    _ ≤ ∑ _i : I,(B : ℝ) := Finset.sum_le_sum (fun i _ => by exact_mod_cast hbad i)
    _ = _ := by simp

end GaussianWave.BS.Lower
