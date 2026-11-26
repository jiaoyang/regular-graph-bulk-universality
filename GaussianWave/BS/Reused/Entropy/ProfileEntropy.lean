import GaussianWave.BS.Reused.Entropy.FiniteHolder
import GaussianWave.BS.Reused.Entropy.ProfileConcentration

/-! Entropy of empirical probability profiles: integral Jensen and an
explicit concentration-to-entropy error, for arbitrary correlated laws. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Entropy

variable {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]

theorem profile_coordinate_le_one (P : A → ℝ) (hp : ∀ a,0 ≤ P a) (hs : ∑ a,P a = 1) (a : A) :
    P a ≤ 1 := (Finset.single_le_sum (fun b hb => hp b) (Finset.mem_univ a)).trans_eq hs

theorem profile_coordinate_memLp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Ω → A → ℝ) (hm : ∀ a,Measurable (fun x => P x a))
    (hp : ∀ x a,0 ≤ P x a) (hs : ∀ x,∑ a,P x a = 1) (a : A) (q : ENNReal) :
    MemLp (fun x => P x a) q μ :=
  MemLp.of_bound (hm a).aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hp x a)]
    exact profile_coordinate_le_one (P x) (hp x) (hs x) a))

theorem integrable_profile_entropy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Ω → A → ℝ) (hm : ∀ a,Measurable (fun x => P x a))
    (hp : ∀ x a,0 ≤ P x a) (hs : ∀ x,∑ a,P x a = 1) :
    Integrable (fun x => Finite.entropy (P x)) μ := by
  apply integrable_finset_sum
  intro a ha
  apply (MemLp.of_bound (p := (1 : ENNReal))
    (Real.continuous_negMulLog.measurable.comp (hm a)).aestronglyMeasurable 1 _).integrable (by norm_num)
  filter_upwards [] with x
  change |Real.negMulLog (P x a)| ≤ 1
  rw [abs_of_nonneg (Real.negMulLog_nonneg (hp x a)
    (profile_coordinate_le_one (P x) (hp x) (hs x) a))]
  exact (Finite.negMulLog_le_one_sub _ (hp x a)).trans (by linarith [hp x a])

theorem meanProfile_nonneg (μ : Measure Ω) (P : Ω → A → ℝ) (hp : ∀ x a,0 ≤ P x a) (a : A) :
    0 ≤ meanProfile μ P a := integral_nonneg (fun x => hp x a)

theorem meanProfile_sum (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Ω → A → ℝ) (hm : ∀ a,Measurable (fun x => P x a))
    (hp : ∀ x a,0 ≤ P x a) (hs : ∀ x,∑ a,P x a = 1) :
    (∑ a,meanProfile μ P a) = 1 := by
  change (∑ a,∫ x,P x a ∂μ) = 1
  rw [← integral_finset_sum (f := fun a x => P x a) Finset.univ
    (fun a ha => (profile_coordinate_memLp μ P hm hp hs a 1).integrable (by norm_num))]
  simp only [hs,integral_const,measureReal_univ_eq_one,one_smul]

set_option maxHeartbeats 1000000 in
theorem integral_profile_entropy_le_mean (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Ω → A → ℝ) (hm : ∀ a,Measurable (fun x => P x a))
    (hp : ∀ x a,0 ≤ P x a) (hs : ∀ x,∑ a,P x a = 1) :
    (∫ x,Finite.entropy (P x) ∂μ) ≤ Finite.entropy (meanProfile μ P) := by
  have hneg (a : A) : Integrable (fun x => Real.negMulLog (P x a)) μ := by
    apply (MemLp.of_bound (p := (1 : ENNReal))
      (Real.continuous_negMulLog.measurable.comp (hm a)).aestronglyMeasurable 1 _).integrable (by norm_num)
    filter_upwards [] with x
    change |Real.negMulLog (P x a)| ≤ 1
    rw [abs_of_nonneg (Real.negMulLog_nonneg (hp x a)
      (profile_coordinate_le_one (P x) (hp x) (hs x) a))]
    exact (Finite.negMulLog_le_one_sub _ (hp x a)).trans (by linarith [hp x a])
  change (∫ x,∑ a,Real.negMulLog (P x a) ∂μ) ≤ ∑ a,Real.negMulLog (meanProfile μ P a)
  rw [integral_finset_sum (f := fun a x => Real.negMulLog (P x a)) Finset.univ (fun a ha => hneg a)]
  apply Finset.sum_le_sum
  intro a ha
  exact Real.concaveOn_negMulLog.le_map_integral Real.continuous_negMulLog.continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun x => hp x a))
    ((profile_coordinate_memLp μ P hm hp hs a 1).integrable (by norm_num)) (hneg a)

set_option maxHeartbeats 1500000 in
theorem entropy_mean_sub_integral_le_holder (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Ω → A → ℝ) (hm : ∀ a,Measurable (fun x => P x a))
    (hp : ∀ x a,0 ≤ P x a) (hs : ∀ x,∑ a,P x a = 1) :
    Finite.entropy (meanProfile μ P)-(∫ x,Finite.entropy (P x) ∂μ) ≤
      (3+Real.log (Fintype.card A))*
        Real.sqrt (∫ x,Finite.totalVariation (P x) (meanProfile μ P) ∂μ) := by
  let TV : Ω → ℝ := fun x => Finite.totalVariation (P x) (meanProfile μ P)
  have hTVm : Measurable TV := by unfold TV Finite.totalVariation; fun_prop
  have hTV0 (x) : 0 ≤ TV x := Finite.totalVariation_nonneg _ _
  have hTV1 (x) : TV x ≤ 1 := Finite.totalVariation_le_one _ _ (hp x)
    (meanProfile_nonneg μ P hp) (hs x) (meanProfile_sum μ P hm hp hs)
  have hroot : MemLp (fun x => Real.sqrt (TV x)) 2 μ :=
    MemLp.of_bound (Real.continuous_sqrt.measurable.comp hTVm).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
        exact (Real.sqrt_le_sqrt (hTV1 x)).trans_eq Real.sqrt_one))
  have hr := integral_abs_le_sqrt_integral_sq μ (fun x => Real.sqrt (TV x)) hroot
  simp only [abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hTV0 _)] at hr
  let C : ℝ := 3+Real.log (Fintype.card A)
  have hC : 0 ≤ C := by dsimp [C]; linarith [Real.log_natCast_nonneg (Fintype.card A)]
  have hHi := integrable_profile_entropy μ P hm hp hs
  have hdiff := (integrable_const (Finite.entropy (meanProfile μ P))).sub hHi
  have hmono := integral_mono hdiff ((hroot.integrable (by norm_num)).const_mul C) (fun x => by
    have h := Finite.entropy_holder (meanProfile μ P) (P x) (meanProfile_nonneg μ P hp)
      (hp x) (meanProfile_sum μ P hm hp hs) (hs x)
    have he : Finite.totalVariation (meanProfile μ P) (P x) = TV x := by
      change (1/2 : ℝ)*(∑ a,|meanProfile μ P a-P x a|) = (1/2 : ℝ)*(∑ a,|P x a-meanProfile μ P a|)
      simp_rw [abs_sub_comm]
    rw [he] at h
    exact (le_abs_self _).trans h)
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub (integrable_const _) hHi,integral_const,integral_const_mul] at hmono
  simp only [measureReal_univ_eq_one,one_smul] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left hr hC)

end GaussianWave.BS.Reused.Entropy
