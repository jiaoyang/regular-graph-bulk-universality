import GeneralizedBulk.Entropy.SoftEdgeGradient
import GeneralizedBulk.Entropy.SoftWordProbability

/-! Actual soft and hard oriented-edge probability profiles, with a
pointwise hard/soft error controlled by scalar transition occurrences. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy

variable {k N d : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
  [MeasurableSpace B] [MeasurableSingletonClass B]

def quantizedHardEdgeAverage (nb : Fin N → Fin d → Fin N) (J : ℝ → B)
    (a : Fin k × Fin N → ℝ) (word : Fin k × Fin 2 → B) : (Fin k × Fin N → ℝ) → ℝ :=
  softEdgeAverage nb (fun i => hardLabel J (word i)) a

theorem normalized_edge_word_sum {W : Type*} [Fintype W]
    (nb : Fin N → Fin d → Fin N) (hN : 0 < N) (hd : 0 < d)
    (P : Fin N → Fin N → W → ℝ) (hP : ∀ u v,∑ w,P u v w = 1) :
    (∑ w,((N*d : ℕ) : ℝ)⁻¹*∑ u,∑ j,P u (nb u j) w) = 1 := by
  rw [← Finset.mul_sum]
  have hs : (∑ w,∑ u,∑ j,P u (nb u j) w) = ∑ u,∑ j,∑ w,P u (nb u j) w := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    exact Finset.sum_comm
  rw [hs]
  simp_rw [hP]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_mul]
  exact inv_mul_cancel₀ (by positivity)

theorem quantizedSoftEdgeAverage_sum (nb : Fin N → Fin d → Fin N) (hN : 0 < N) (hd : 0 < d)
    (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ) (a x : Fin k × Fin N → ℝ) :
    (∑ word : Fin k × Fin 2 → B,quantizedSoftEdgeAverage nb J ℓ a word x) = 1 := by
  exact normalized_edge_word_sum (W := Fin k × Fin 2 → B) nb hN hd
    (fun u v word => softWordProbability J ℓ
      (fun i : Fin k × Fin 2 => (a+x) (i.1,if i.2 = 0 then u else v)) word)
    (fun u v => softWordProbability_sum J hJ ℓ hℓ _)


theorem quantizedHardEdgeAverage_nonneg (nb : Fin N → Fin d → Fin N) (J : ℝ → B)
    (a x : Fin k × Fin N → ℝ) (word : Fin k × Fin 2 → B) :
    0 ≤ quantizedHardEdgeAverage nb J a word x :=
  softEdgeAverage_nonneg nb _ (fun i => hardLabel_nonneg J (word i)) a x

theorem quantizedHardEdgeAverage_sum (nb : Fin N → Fin d → Fin N) (hN : 0 < N) (hd : 0 < d)
    (J : ℝ → B) (a x : Fin k × Fin N → ℝ) :
    (∑ word : Fin k × Fin 2 → B,quantizedHardEdgeAverage nb J a word x) = 1 := by
  exact normalized_edge_word_sum (W := Fin k × Fin 2 → B) nb hN hd
    (fun u v word => hardWordProbability J
      (fun i : Fin k × Fin 2 => (a+x) (i.1,if i.2 = 0 then u else v)) word)
    (fun u v => product_probability_sum
      (fun i : Fin k × Fin 2 => fun b : B => hardLabel J b ((a+x) (i.1,if i.2 = 0 then u else v)))
      (fun i => hardLabel_sum J _))


set_option maxHeartbeats 1000000 in
theorem normalized_edge_l1_distance_le {W : Type*} [Fintype W]
    (nb : Fin N → Fin d → Fin N) (P Q : Fin N → Fin N → W → ℝ) :
    (∑ w,|((N*d : ℕ) : ℝ)⁻¹*(∑ u,∑ j,P u (nb u j) w)-
      ((N*d : ℕ) : ℝ)⁻¹*(∑ u,∑ j,Q u (nb u j) w)|) ≤
      ((N*d : ℕ) : ℝ)⁻¹*(∑ u,∑ j,∑ w,|P u (nb u j) w-Q u (nb u j) w|) := by
  have h (w : W) : |((N*d : ℕ) : ℝ)⁻¹*(∑ u,∑ j,P u (nb u j) w)-
      ((N*d : ℕ) : ℝ)⁻¹*(∑ u,∑ j,Q u (nb u j) w)| ≤
      ((N*d : ℕ) : ℝ)⁻¹*(∑ u,∑ j,|P u (nb u j) w-Q u (nb u j) w|) := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0 ≤ ((N*d : ℕ) : ℝ)⁻¹),← Finset.sum_sub_distrib]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ ∑ u,|(∑ j,P u (nb u j) w)-(∑ j,Q u (nb u j) w)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u hu
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
  apply (Finset.sum_le_sum (fun w hw => h w)).trans_eq
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact Finset.sum_comm

set_option maxHeartbeats 1000000 in
theorem quantizedHardSoftEdge_l1_le_transitions (nb : Fin N → Fin d → Fin N)
    (hnb : ∀ f : Fin N → ℝ,(∑ u,∑ j,f (nb u j)) = (d : ℝ)*∑ v,f v)
    (hN : 0 < N) (hd : 0 < d) (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (a x : Fin k × Fin N → ℝ) :
    (∑ word : Fin k × Fin 2 → B,
      |quantizedHardEdgeAverage nb J a word x-quantizedSoftEdgeAverage nb J ℓ a word x|) ≤
        (4/(N : ℝ))*∑ i : Fin k × Fin N,if quantizerTransition J ℓ ((a+x) i) then (1 : ℝ) else 0 := by
  apply (normalized_edge_l1_distance_le nb
    (fun u v word => hardWordProbability J (fun i : Fin k × Fin 2 => (a+x) (i.1,if i.2 = 0 then u else v)) word)
    (fun u v word => softWordProbability J ℓ (fun i : Fin k × Fin 2 => (a+x) (i.1,if i.2 = 0 then u else v)) word)).trans
  calc
    _ ≤ ((N*d : ℕ) : ℝ)⁻¹*∑ u,∑ j,2*∑ i : Fin k × Fin 2,
        if quantizerTransition J ℓ ((a+x) (i.1,if i.2 = 0 then u else nb u j)) then (1 : ℝ) else 0 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro u hu
      exact Finset.sum_le_sum (fun j hj => hard_soft_word_l1_le_transitions J hJ ℓ hℓ _)
    _ = _ := by
      simp only [Fintype.sum_prod_type,Fin.sum_univ_two,Fin.zero_eta,Fin.isValue,ite_true,Fin.mk_one,Fin.reduceEq,ite_false]
      simp_rw [← Finset.mul_sum]
      rw [sum_edge_endpoint_terms nb hnb (fun r v => if quantizerTransition J ℓ ((a+x) (r,v)) then (1 : ℝ) else 0)]
      push_cast
      field_simp
      ring

end GeneralizedBulk.Entropy
