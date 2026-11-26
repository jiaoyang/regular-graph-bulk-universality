import Mathlib

/-! Finite probability-profile concentration bookkeeping without any
independence assumption on the underlying probability space. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Entropy

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]

def profileL1 (p q : I → ℝ) : ℝ := ∑ i,|p i-q i|

def meanProfile (μ : Measure Ω) (P : Ω → I → ℝ) (i : I) : ℝ := ∫ x,P x i ∂μ

theorem profileL1_comm (p q : I → ℝ) : profileL1 p q = profileL1 q p := by
  unfold profileL1
  simp_rw [abs_sub_comm]

theorem profileL1_triangle (p q r : I → ℝ) : profileL1 p r ≤ profileL1 p q+profileL1 q r := by
  rw [profileL1,profileL1,profileL1,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i hi => abs_sub_le (p i) (q i) (r i))

theorem integrable_profileL1 (μ : Measure Ω) (P Q : Ω → I → ℝ)
    (hP : ∀ i,Integrable (fun x => P x i) μ) (hQ : ∀ i,Integrable (fun x => Q x i) μ) :
    Integrable (fun x => profileL1 (P x) (Q x)) μ :=
  integrable_finset_sum _ (fun i hi => ((hP i).sub (hQ i)).abs)

theorem meanProfile_l1_le_integral (μ : Measure Ω) (P Q : Ω → I → ℝ)
    (hP : ∀ i,Integrable (fun x => P x i) μ) (hQ : ∀ i,Integrable (fun x => Q x i) μ) :
    profileL1 (meanProfile μ P) (meanProfile μ Q) ≤ ∫ x,profileL1 (P x) (Q x) ∂μ := by
  rw [profileL1,show (fun x => profileL1 (P x) (Q x)) = (fun x => ∑ i,|P x i-Q x i|) from rfl,
    integral_finset_sum (f := fun i x => |P x i-Q x i|) _ (fun i hi => ((hP i).sub (hQ i)).abs)]
  apply Finset.sum_le_sum
  intro i hi
  have h := norm_integral_le_integral_norm (fun x => P x i-Q x i) (μ := μ)
  simpa only [Real.norm_eq_abs,integral_sub (hP i) (hQ i),meanProfile] using h

theorem integral_abs_le_sqrt_integral_sq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    (∫ x,|f x| ∂μ) ≤ Real.sqrt (∫ x,(f x)^2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := memLp_const 1
  have h := integral_mul_norm_le_Lp_mul_Lq hpq hf' hg
  simpa only [Real.norm_eq_abs,abs_one,mul_one,Real.rpow_two,sq_abs,one_pow,
    integral_const,measureReal_univ_eq_one,smul_eq_mul,Real.one_rpow,← Real.sqrt_eq_rpow,Real.sqrt_one] using h

set_option maxHeartbeats 1000000 in
theorem integral_profileL1_mean_le_variance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Ω → I → ℝ) (hP : ∀ i,MemLp (fun x => P x i) 2 μ)
    (V : ℝ) (hV : ∀ i,(∫ x,(P x i-meanProfile μ P i)^2 ∂μ) ≤ V) :
    (∫ x,profileL1 (P x) (meanProfile μ P) ∂μ) ≤ (Fintype.card I : ℝ)*Real.sqrt V := by
  have hc (i : I) : MemLp (fun x => P x i-meanProfile μ P i) 2 μ := (hP i).sub (memLp_const _)
  rw [show (fun x => profileL1 (P x) (meanProfile μ P)) = (fun x => ∑ i,|P x i-meanProfile μ P i|) from rfl,
    integral_finset_sum (f := fun i x => |P x i-meanProfile μ P i|) _
      (fun i hi => ((hc i).integrable (by norm_num)).abs)]
  calc
    _ ≤ ∑ _i : I,Real.sqrt V := by
      apply Finset.sum_le_sum
      intro i hi
      exact (integral_abs_le_sqrt_integral_sq μ _ (hc i)).trans (Real.sqrt_le_sqrt (hV i))
    _ = _ := by simp

set_option maxHeartbeats 1000000 in
theorem integral_profileL1_mean_triangle (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P S : Ω → I → ℝ) (hP : ∀ i,Integrable (fun x => P x i) μ)
    (hS : ∀ i,Integrable (fun x => S x i) μ) :
    (∫ x,profileL1 (P x) (meanProfile μ P) ∂μ) ≤
      2*(∫ x,profileL1 (P x) (S x) ∂μ)+(∫ x,profileL1 (S x) (meanProfile μ S) ∂μ) := by
  have hPM : ∀ i,Integrable (fun _x : Ω => meanProfile μ P i) μ := fun i => integrable_const _
  have hSM : ∀ i,Integrable (fun _x : Ω => meanProfile μ S i) μ := fun i => integrable_const _
  have hPS := integrable_profileL1 μ P S hP hS
  have hSD := integrable_profileL1 μ S (fun _ => meanProfile μ S) hS hSM
  have hDM : Integrable (fun _x : Ω => profileL1 (meanProfile μ S) (meanProfile μ P)) μ := integrable_const _
  have hmean : profileL1 (meanProfile μ S) (meanProfile μ P) ≤ ∫ x,profileL1 (P x) (S x) ∂μ := by
    rw [profileL1_comm]
    exact meanProfile_l1_le_integral μ P S hP hS
  calc
    _ ≤ ∫ x,(profileL1 (P x) (S x)+profileL1 (S x) (meanProfile μ S)+
        profileL1 (meanProfile μ S) (meanProfile μ P)) ∂μ := by
      apply integral_mono (integrable_profileL1 μ P (fun _ => meanProfile μ P) hP hPM) ((hPS.add hSD).add hDM)
      intro x
      have h1 := profileL1_triangle (P x) (S x) (meanProfile μ P)
      have h2 := profileL1_triangle (S x) (meanProfile μ S) (meanProfile μ P)
      dsimp only [Pi.add_apply]
      linarith
    _ = (∫ x,profileL1 (P x) (S x) ∂μ)+(∫ x,profileL1 (S x) (meanProfile μ S) ∂μ)+
        profileL1 (meanProfile μ S) (meanProfile μ P) := by
      have hi1 := integral_add (hPS.add hSD) hDM
      have hi2 := integral_add hPS hSD
      simp only [Pi.add_apply] at hi1 hi2
      rw [hi2,integral_const] at hi1
      simpa only [measureReal_univ_eq_one,smul_eq_mul,one_mul] using hi1
    _ ≤ _ := by linarith

end GeneralizedBulk.Entropy
