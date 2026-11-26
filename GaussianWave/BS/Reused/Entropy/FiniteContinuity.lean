import GaussianWave.BS.Reused.Entropy.FiniteMixture

/-! A dimension-logarithmic finite-alphabet entropy continuity bound. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Entropy.Finite

variable {A : Type*} [Fintype A]

theorem vector_eq_zero_of_sum_zero (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (hsum : ∑ a,p a = 0) :
    p = 0 := by
  funext a
  have ha := Finset.single_le_sum (fun a ha => hp a) (Finset.mem_univ a)
  rw [hsum] at ha
  exact le_antisymm ha (hp a)

set_option maxHeartbeats 1000000 in
theorem entropy_common_mass_bound (c r s : A → ℝ)
    (hc : ∀ a,0 ≤ c a) (hr : ∀ a,0 ≤ r a) (hs : ∀ a,0 ≤ s a)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hcsum : ∑ a,c a = 1-δ) (hrsum : ∑ a,r a = δ) (hssum : ∑ a,s a = δ) :
    |entropy (fun a => c a+r a)-entropy (fun a => c a+s a)| ≤
      Real.binEntropy δ+δ*Real.log (Fintype.card A) := by
  by_cases hδ0 : δ = 0
  · have hr0 := vector_eq_zero_of_sum_zero r hr (hrsum.trans hδ0)
    have hs0 := vector_eq_zero_of_sum_zero s hs (hssum.trans hδ0)
    simp [hδ0,hr0,hs0]
  by_cases hδeq1 : δ = 1
  · have hc0 := vector_eq_zero_of_sum_zero c hc (by simpa only [hδeq1,sub_self] using hcsum)
    have hr1 : ∑ a,r a = 1 := hrsum.trans hδeq1
    have hs1 : ∑ a,s a = 1 := hssum.trans hδeq1
    have hrlo := entropy_nonneg r hr hr1
    have hslo := entropy_nonneg s hs hs1
    have hrhi := entropy_le_log_card r hr hr1
    have hshi := entropy_le_log_card s hs hs1
    simp only [hc0,Pi.zero_apply,zero_add,hδeq1,Real.binEntropy_one,one_mul,zero_add]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hδp : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
  have hαp : 0 < 1-δ := sub_pos.mpr (lt_of_le_of_ne hδ1 hδeq1)
  let C : A → ℝ := fun a => c a/(1-δ)
  let R : A → ℝ := fun a => r a/δ
  let S : A → ℝ := fun a => s a/δ
  have hC : ∀ a,0 ≤ C a := fun a => div_nonneg (hc a) hαp.le
  have hR : ∀ a,0 ≤ R a := fun a => div_nonneg (hr a) hδp.le
  have hS : ∀ a,0 ≤ S a := fun a => div_nonneg (hs a) hδp.le
  have hCsum : ∑ a,C a = 1 := by dsimp [C]; rw [← Finset.sum_div,hcsum,div_self (ne_of_gt hαp)]
  have hRsum : ∑ a,R a = 1 := by dsimp [R]; rw [← Finset.sum_div,hrsum,div_self (ne_of_gt hδp)]
  have hSsum : ∑ a,S a = 1 := by dsimp [S]; rw [← Finset.sum_div,hssum,div_self (ne_of_gt hδp)]
  have heR : (fun a => (1-δ)*C a+δ*R a) = (fun a => c a+r a) := by
    funext a; dsimp [C,R]; field_simp
  have heS : (fun a => (1-δ)*C a+δ*S a) = (fun a => c a+s a) := by
    funext a; dsimp [C,S]; field_simp
  have hupR := entropy_mixture_upper C R hC hR hCsum hRsum (1-δ) δ hαp.le hδ
  have hupS := entropy_mixture_upper C S hC hS hCsum hSsum (1-δ) δ hαp.le hδ
  have hloR := entropy_mixture_lower C R hC hR (1-δ) δ hαp.le hδ (by ring)
  have hloS := entropy_mixture_lower C S hC hS (1-δ) δ hαp.le hδ (by ring)
  rw [heR] at hupR hloR
  rw [heS] at hupS hloS
  have hrlo := entropy_nonneg R hR hRsum
  have hslo := entropy_nonneg S hS hSsum
  have hrhi := entropy_le_log_card R hR hRsum
  have hshi := entropy_le_log_card S hS hSsum
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  apply abs_le.mpr
  constructor <;> nlinarith

def totalVariation (p q : A → ℝ) : ℝ := (1/2 : ℝ)*∑ a,|p a-q a|

theorem totalVariation_common_mass (p q : A → ℝ)
    (hpsum : ∑ a,p a = 1) (hqsum : ∑ a,q a = 1) :
    ∑ a,min (p a) (q a) = 1-totalVariation p q := by
  have hpoint (a : A) : 2*min (p a) (q a)+|p a-q a| = p a+q a := by
    rcases le_total (p a) (q a) with h | h
    · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
  have h : (∑ a, (2*min (p a) (q a)+|p a-q a|)) = ∑ a,(p a+q a) :=
    Finset.sum_congr rfl (fun a ha => hpoint a)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,hpsum,hqsum] at h
  unfold totalVariation
  linarith

theorem totalVariation_nonneg (p q : A → ℝ) : 0 ≤ totalVariation p q := by
  unfold totalVariation
  positivity

theorem totalVariation_le_one (p q : A → ℝ) (hp : ∀ a,0 ≤ p a) (hq : ∀ a,0 ≤ q a)
    (hpsum : ∑ a,p a = 1) (hqsum : ∑ a,q a = 1) : totalVariation p q ≤ 1 := by
  have hc : (0 : ℝ) ≤ ∑ a,min (p a) (q a) :=
    Finset.sum_nonneg (fun a ha => le_min (hp a) (hq a))
  rw [totalVariation_common_mass p q hpsum hqsum] at hc
  linarith

set_option maxHeartbeats 1000000 in
theorem entropy_continuity (p q : A → ℝ) (hp : ∀ a,0 ≤ p a) (hq : ∀ a,0 ≤ q a)
    (hpsum : ∑ a,p a = 1) (hqsum : ∑ a,q a = 1) :
    |entropy p-entropy q| ≤ Real.binEntropy (totalVariation p q)+
      totalVariation p q*Real.log (Fintype.card A) := by
  let c : A → ℝ := fun a => min (p a) (q a)
  let r : A → ℝ := fun a => p a-c a
  let s : A → ℝ := fun a => q a-c a
  have hc : ∀ a,0 ≤ c a := fun a => le_min (hp a) (hq a)
  have hr : ∀ a,0 ≤ r a := fun a => sub_nonneg.mpr (min_le_left _ _)
  have hs : ∀ a,0 ≤ s a := fun a => sub_nonneg.mpr (min_le_right _ _)
  have hcsum : ∑ a,c a = 1-totalVariation p q := totalVariation_common_mass p q hpsum hqsum
  have hrsum : ∑ a,r a = totalVariation p q := by dsimp [r]; rw [Finset.sum_sub_distrib,hpsum,hcsum]; ring
  have hssum : ∑ a,s a = totalVariation p q := by dsimp [s]; rw [Finset.sum_sub_distrib,hqsum,hcsum]; ring
  have h := entropy_common_mass_bound c r s hc hr hs (totalVariation p q)
    (totalVariation_nonneg p q) (totalVariation_le_one p q hp hq hpsum hqsum) hcsum hrsum hssum
  have hep : (fun a => c a+r a) = p := by funext a; dsimp [r]; ring
  have heq : (fun a => c a+s a) = q := by funext a; dsimp [s]; ring
  rwa [hep,heq] at h

end GaussianWave.BS.Reused.Entropy.Finite
