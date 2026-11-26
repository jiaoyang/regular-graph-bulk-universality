import Mathlib

/-! Finite dependency variance for bounded observations on an arbitrary
probability space, including Gaussian product spaces. Integrability is
derived from actual almost-everywhere bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
set_option maxHeartbeats 1000000
namespace GaussianWave.BS.Lower

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem integral_centered_sum_sq_le_of_ae_bounded (X : I → Ω → ℝ)
    (hXm : ∀ i,AEMeasurable (X i) μ)
    (hX : ∀ i,∀ᵐ ω ∂μ,0 ≤ X i ω ∧ X i ω ≤ 1)
    (bad : I → Finset I) (D : ℕ) (hbad : ∀ i,(bad i).card ≤ D)
    (hindep : ∀ i j,j ∉ bad i → IndepFun (X i) (X j) μ) :
    (∫ ω,(∑ i,(X i ω-(∫ z,X i z ∂μ)))^2 ∂μ) ≤ (Fintype.card I : ℝ)*D := by
  have hiX (i : I) : Integrable (X i) μ :=
    (MemLp.of_bound (p := (1 : ENNReal)) (hXm i).aestronglyMeasurable 1
      ((hX i).mono (fun ω hω => by rw [Real.norm_eq_abs,abs_of_nonneg hω.1]; exact hω.2))).integrable (by norm_num)
  let E (i : I) := ∫ ω,X i ω ∂μ
  let Y (i : I) (ω : Ω) := X i ω-E i
  have hE0 (i : I) : 0 ≤ E i := integral_nonneg_of_ae ((hX i).mono (fun _ h => h.1))
  have hE1 (i : I) : E i ≤ 1 := by
    have h := integral_mono_ae (hiX i) (integrable_const (1 : ℝ)) ((hX i).mono (fun _ h => h.2))
    simpa only [integral_const,measureReal_univ_eq_one,one_smul] using h
  have hYabs (i : I) : ∀ᵐ ω ∂μ,|Y i ω| ≤ 1 := (hX i).mono (fun ω hω => by
    apply abs_le.mpr
    dsimp [Y]
    constructor <;> linarith [hω.1,hω.2,hE0 i,hE1 i])
  have hiY (i : I) : Integrable (Y i) μ := (hiX i).sub (integrable_const _)
  have hiProd (i j : I) : Integrable (fun ω => Y i ω*Y j ω) μ := by
    apply (MemLp.of_bound (p := (1 : ENNReal)) ((hiY i).aestronglyMeasurable.mul (hiY j).aestronglyMeasurable) 1 _).integrable (by norm_num)
    filter_upwards [hYabs i,hYabs j] with ω hi hj
    change ‖Y i ω*Y j ω‖ ≤ 1
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul hi hj (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hYmean (i : I) : (∫ ω,Y i ω ∂μ)=0 := by
    dsimp only [Y]
    rw [integral_sub (hiX i) (integrable_const _),integral_const]
    simp only [measureReal_univ_eq_one,one_smul,E,sub_self]
  have hcov0 (i j : I) (hji : j ∉ bad i) : (∫ ω,Y i ω*Y j ω ∂μ)=0 := by
    have hYij : IndepFun (Y i) (Y j) μ :=
      (hindep i j hji).comp (measurable_id.sub_const (E i)) (measurable_id.sub_const (E j))
    have h := hYij.integral_mul_of_integrable (hiY i) (hiY j)
    simpa only [Pi.mul_apply,hYmean,mul_zero] using h
  have hcov1 (i j : I) : (∫ ω,Y i ω*Y j ω ∂μ) ≤ 1 := by
    have hpoint : ∀ᵐ ω ∂μ,Y i ω*Y j ω ≤ 1 := by
      filter_upwards [hYabs i,hYabs j] with ω hi hj
      calc
        _ ≤ |Y i ω*Y j ω| := le_abs_self _
        _ = |Y i ω| * |Y j ω| := abs_mul _ _
        _ ≤ 1*1 := mul_le_mul hi hj (abs_nonneg _) (by norm_num)
        _ = _ := by norm_num
    have h := integral_mono_ae (hiProd i j) (integrable_const (1 : ℝ)) hpoint
    simpa only [integral_const,measureReal_univ_eq_one,one_smul] using h
  have hcov (i j : I) : (∫ ω,Y i ω*Y j ω ∂μ) ≤ if j ∈ bad i then (1 : ℝ) else 0 := by
    by_cases hji : j ∈ bad i
    · simpa only [if_pos hji] using hcov1 i j
    · simp only [if_neg hji,hcov0 i j hji,le_refl]
  have hsq (ω : Ω) : (∑ i,Y i ω)^2=∑ i,∑ j,Y i ω*Y j ω := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  change (∫ ω,(∑ i,Y i ω)^2 ∂μ) ≤ _
  simp_rw [hsq]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hiProd i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hiProd _ j)]
  calc
    _ ≤ ∑ i : I,∑ j : I,if j ∈ bad i then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcov i j))
    _ = ∑ i : I,((bad i).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [← Finset.sum_filter]
      simp
    _ ≤ ∑ _i : I,(D : ℝ) := Finset.sum_le_sum (fun i _ => by exact_mod_cast hbad i)
    _ = _ := by simp

/-- Normalized empirical variance on an arbitrary probability space. -/
theorem integral_centered_average_sq_le_of_ae_bounded (hI : 0 < Fintype.card I)
    (X : I → Ω → ℝ) (hXm : ∀ i,AEMeasurable (X i) μ)
    (hX : ∀ i,∀ᵐ ω ∂μ,0 ≤ X i ω ∧ X i ω ≤ 1)
    (bad : I → Finset I) (D : ℕ) (hbad : ∀ i,(bad i).card ≤ D)
    (hindep : ∀ i j,j ∉ bad i → IndepFun (X i) (X j) μ) :
    (∫ ω,((Fintype.card I : ℝ)⁻¹*(∑ i,X i ω)-
      ∫ z,(Fintype.card I : ℝ)⁻¹*(∑ i,X i z) ∂μ)^2 ∂μ) ≤ (D : ℝ)/(Fintype.card I : ℝ) := by
  have hiX (i : I) : Integrable (X i) μ :=
    (MemLp.of_bound (p := (1 : ENNReal)) (hXm i).aestronglyMeasurable 1
      ((hX i).mono (fun ω hω => by rw [Real.norm_eq_abs,abs_of_nonneg hω.1]; exact hω.2))).integrable (by norm_num)
  have hmean : (∫ z,(Fintype.card I : ℝ)⁻¹*(∑ i,X i z) ∂μ)=
      (Fintype.card I : ℝ)⁻¹*(∑ i,∫ z,X i z ∂μ) := by
    rw [integral_const_mul,integral_finset_sum _ (fun i _ => hiX i)]
  have hpoint (ω : Ω) : ((Fintype.card I : ℝ)⁻¹*(∑ i,X i ω)-
      ∫ z,(Fintype.card I : ℝ)⁻¹*(∑ i,X i z) ∂μ)^2=
      ((Fintype.card I : ℝ)⁻¹)^2*(∑ i,(X i ω-∫ z,X i z ∂μ))^2 := by
    rw [hmean,Finset.sum_sub_distrib]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left
    (integral_centered_sum_sq_le_of_ae_bounded μ X hXm hX bad D hbad hindep)
    (sq_nonneg ((Fintype.card I : ℝ)⁻¹))
  apply hb.trans_eq
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hI)
  field_simp
  ring

end GaussianWave.BS.Lower
