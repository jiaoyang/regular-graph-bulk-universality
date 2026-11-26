import BourgadeHuang.NevanlinnaLocalEstimates
import BourgadeHuang.ExponentialMomentControl

/-! Deterministic balanced moment estimates for arbitrary genuine anchored
Nevanlinna counting states, without a finite-particle restriction. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem anchoredNevanlinna_star (s : AnchoredCountingState) (w : ℂ) :
    anchoredNevanlinna s (star w) = star (anchoredNevanlinna s w) :=
  anchoredNevanlinna_conj s w

theorem norm_anchoredDerivative_le_norm (s : AnchoredCountingState)
    {w : ℂ} (hw : 0 < w.im) :
    ‖anchoredDerivative s w‖ ≤ ‖anchoredNevanlinna s w‖ / w.im := by
  apply (norm_anchoredDerivative_le_im s hw.ne').trans
  rw [abs_of_pos hw]
  exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) hw.le

theorem anchored_momentAux_product (s : AnchoredCountingState) (r : ℕ) (w : ℂ) :
    (∏ a, anchoredNevanlinna s (momentAux r w a)) =
      anchoredNevanlinna s w ^ r *
        star (anchoredNevanlinna s w) ^ (r + 2) := by
  rw [Fin.prod_univ_add]
  simp only [momentAux, Fin.addCases_left, Fin.addCases_right]
  rw [anchoredNevanlinna_star]
  simp

theorem anchored_momentAux_leading (s : AnchoredCountingState) (r : ℕ) (w : ℂ) :
    anchoredNevanlinna s w ^ 2 *
        (∏ a, anchoredNevanlinna s (momentAux r w a)) =
      (‖anchoredNevanlinna s w‖ ^ (2 * r + 4) : ℝ) := by
  rw [anchored_momentAux_product, balanced_power_identity]

theorem anchored_norm_momentAux_resolvent (s : AnchoredCountingState)
    (r : ℕ) (w : ℂ) (a : Fin (r + (r + 2))) :
    ‖anchoredNevanlinna s (momentAux r w a)‖ =
      ‖anchoredNevanlinna s w‖ := by
  rcases momentAux_eq_or r w a with h | h
  · rw [h]
  · rw [h, anchoredNevanlinna_star, norm_star]

theorem norm_anchored_momentAux_product (s : AnchoredCountingState)
    (r : ℕ) (w : ℂ) :
    ‖∏ a, anchoredNevanlinna s (momentAux r w a)‖ =
      ‖anchoredNevanlinna s w‖ ^ (2 * r + 2) := by
  rw [norm_prod]
  simp_rw [anchored_norm_momentAux_resolvent]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

theorem anchored_norm_momentAux_excludedProduct (s : AnchoredCountingState)
    (r : ℕ) (w : ℂ) (a : Fin (r + (r + 2))) :
    ‖excludedProduct (fun b => anchoredNevanlinna s (momentAux r w b)) a‖ =
      ‖anchoredNevanlinna s w‖ ^ (2 * r + 1) := by
  unfold excludedProduct
  rw [norm_prod]
  simp_rw [anchored_norm_momentAux_resolvent]
  simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ a),
    Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

theorem anchored_norm_loopIntegrand_remainder_adjacent (β : Beta) (s : AnchoredCountingState) (r : ℕ) {w : ℂ} (hw : 0 < w.im) :
    ‖anchoredLoopIntegrand β s w (momentAux r w) -
        ((‖anchoredNevanlinna s w‖ ^ (2 * r + 4) : ℝ) : ℂ)‖ ≤
      (1 / w.im) * ‖anchoredNevanlinna s w‖ ^ (2 * r + 3) +
        (1 + 2 * (r + (r + 2) : ℕ) / w.im ^ 2 : ℝ) *
          ‖anchoredNevanlinna s w‖ ^ (2 * r + 2) := by
  let S := anchoredNevanlinna s w
  let P := ∏ a, anchoredNevanlinna s (momentAux r w a)
  let T := ∑ a, anchoredInteraction s w (momentAux r w a) *
    excludedProduct (fun b => anchoredNevanlinna s (momentAux r w b)) a
  have hS : 0 ≤ ‖S‖ := norm_nonneg S
  have hcoef : ‖(2 - β.value) / β.value‖ ≤ 1 := by
    cases β <;> norm_num [Beta.value]
  have hcoef' : ‖2 / β.value‖ ≤ 2 := by
    cases β <;> norm_num [Beta.value]
  have hder : ‖anchoredDerivative s w‖ ≤ ‖S‖ / w.im :=
    norm_anchoredDerivative_le_norm s hw
  have hinter (a : Fin (r + (r + 2))) :
      ‖anchoredInteraction s w (momentAux r w a)‖ ≤ ‖S‖ / w.im ^ 2 := by
    simpa [S] using norm_anchoredInteraction_same_or_conj s hw
      (momentAux_eq_or r w a)
  have hP : ‖P‖ = ‖S‖ ^ (2 * r + 2) :=
    norm_anchored_momentAux_product s r w
  have hterm (a : Fin (r + (r + 2))) :
      ‖anchoredInteraction s w (momentAux r w a) *
          excludedProduct
            (fun b => anchoredNevanlinna s (momentAux r w b)) a‖ ≤
        ‖S‖ ^ (2 * r + 2) / w.im ^ 2 := by
    rw [norm_mul, anchored_norm_momentAux_excludedProduct]
    calc
      _ ≤ (‖S‖ / w.im ^ 2) * ‖S‖ ^ (2 * r + 1) :=
        mul_le_mul_of_nonneg_right (hinter a) (pow_nonneg hS _)
      _ = ‖S‖ ^ (2 * r + 2) / w.im ^ 2 := by
        simp only [pow_add, pow_one, pow_two]
        ring
  have hT : ‖T‖ ≤ (r + (r + 2) : ℕ) * (‖S‖ ^ (2 * r + 2) / w.im ^ 2) := by
    calc
      ‖T‖ ≤ ∑ a, ‖anchoredInteraction s w (momentAux r w a) *
          excludedProduct
            (fun b => anchoredNevanlinna s (momentAux r w b)) a‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _a : Fin (r + (r + 2)), ‖S‖ ^ (2 * r + 2) / w.im ^ 2 :=
        Finset.sum_le_sum (fun a _ => hterm a)
      _ = _ := by simp
  have hhead : ‖((2 - β.value) / β.value) * anchoredDerivative s w + 1‖ ≤
      ‖S‖ / w.im + 1 := by
    calc
      _ ≤ ‖((2 - β.value) / β.value) * anchoredDerivative s w‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
      _ = ‖(2 - β.value) / β.value‖ * ‖anchoredDerivative s w‖ + 1 := by
        rw [norm_mul, norm_one]
      _ ≤ 1 * (‖S‖ / w.im) + 1 :=
        add_le_add_right (mul_le_mul hcoef hder (norm_nonneg _) (by norm_num)) _
      _ = _ := by ring
  have heq : anchoredLoopIntegrand β s w (momentAux r w) -
      ((‖S‖ ^ (2 * r + 4) : ℝ) : ℂ) =
        (((2 - β.value) / β.value) * anchoredDerivative s w + 1) * P +
          (2 / β.value) * T := by
    have hlead := anchored_momentAux_leading s r w
    change S ^ 2 * P = ((‖S‖ ^ (2 * r + 4) : ℝ) : ℂ) at hlead
    rw [← hlead]
    unfold anchoredLoopIntegrand P T S
    ring
  rw [heq]
  calc
    _ ≤ ‖(((2 - β.value) / β.value) * anchoredDerivative s w + 1) * P‖ +
        ‖(2 / β.value) * T‖ := norm_add_le _ _
    _ = ‖((2 - β.value) / β.value) * anchoredDerivative s w + 1‖ *
        ‖S‖ ^ (2 * r + 2) + ‖2 / β.value‖ * ‖T‖ := by rw [norm_mul, norm_mul, hP]
    _ ≤ (‖S‖ / w.im + 1) * ‖S‖ ^ (2 * r + 2) +
        2 * ((r + (r + 2) : ℕ) * (‖S‖ ^ (2 * r + 2) / w.im ^ 2)) :=
      add_le_add (mul_le_mul_of_nonneg_right hhead (pow_nonneg hS _))
        (mul_le_mul hcoef' hT (norm_nonneg _) (by norm_num))
    _ = (1 / w.im) * ‖S‖ ^ (2 * r + 3) +
        (1 + 2 * (r + (r + 2) : ℕ) / w.im ^ 2 : ℝ) * ‖S‖ ^ (2 * r + 2) := by
      simp only [pow_add, pow_succ, pow_zero]
      push_cast
      ring

/-- Young's inequality preserves the neighboring even moment. -/
theorem anchored_norm_loopIntegrand_remainder_half_leading (β : Beta)
    (s : AnchoredCountingState) (r : ℕ) {w : ℂ} (hw : 0 < w.im) :
    ‖anchoredLoopIntegrand β s w (momentAux r w) -
        ((‖anchoredNevanlinna s w‖ ^ (2 * r + 4) : ℝ) : ℂ)‖ ≤
      (1 / 2 : ℝ) * ‖anchoredNevanlinna s w‖ ^ (2 * r + 4) +
        (1 + (2 * (r + (r + 2) : ℕ) + 1 / 2) / w.im ^ 2 : ℝ) *
          ‖anchoredNevanlinna s w‖ ^ (2 * r + 2) := by
  apply (anchored_norm_loopIntegrand_remainder_adjacent β s r hw).trans
  let t := ‖anchoredNevanlinna s w‖
  have hy : (1 / w.im) * t ≤ (1 / 2 : ℝ) * t ^ 2 + (1 / 2) / w.im ^ 2 := by
    calc
      _ ≤ (1 / 2 : ℝ) * t ^ 2 + (1 / 2) * (w.im⁻¹) ^ 2 := by
        rw [one_div]
        nlinarith [sq_nonneg (t - w.im⁻¹)]
      _ = _ := by simp only [inv_pow, div_eq_mul_inv]
  have hp := mul_le_mul_of_nonneg_right hy
    (pow_nonneg (norm_nonneg (anchoredNevanlinna s w)) (2 * r + 2))
  dsimp only [t] at hp
  have he3 : 2 * r + 3 = (2 * r + 2) + 1 := by omega
  have he4 : 2 * r + 4 = (2 * r + 2) + 2 := by omega
  simp only [he3, he4, pow_add, pow_one] at hp ⊢
  simp only [div_eq_mul_inv] at hp ⊢
  nlinarith [hp]


theorem anchored_norm_loopIntegrand_remainder_I (β : Beta)
    (s : AnchoredCountingState) (r : ℕ) :
    ‖anchoredLoopIntegrand β s Complex.I (momentAux r Complex.I) -
        ((‖s.val.2‖ ^ (2 * r + 4) : ℝ) : ℂ)‖ ≤
      (2 * (r + (r + 2) : ℕ) + 2 : ℝ) * (1 + ‖s.val.2‖ ^ (2 * r + 3)) := by
  have h := anchored_norm_loopIntegrand_remainder_adjacent β s r
    (show 0 < Complex.I.im by simp)
  simp only [anchoredNevanlinna_I,Complex.I_im,one_div_one,one_pow,div_one,one_mul] at h
  apply h.trans
  have hp := lower_pow_le_one_add (norm_nonneg s.val.2) (2*r+2)
  have hc : (0:ℝ) ≤ 1+2*(r+(r+2):ℕ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hp hc
  push_cast at hh ⊢
  nlinarith

end BourgadeHuang
