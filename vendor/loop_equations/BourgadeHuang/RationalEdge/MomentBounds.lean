import BourgadeHuang.RationalEdge.Foundation

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

theorem norm_loopIntegrand_remainder_adjacent (β : ℝ) (s : AnchoredCountingState) (r : ℕ) {w : ℂ} (hw : 0 < w.im) :
    ‖loopIntegrand β s w (momentAux r w) -
        ((‖anchoredNevanlinna s w‖ ^ (2 * r + 4) : ℝ) : ℂ)‖ ≤
      (coefficientBound β / w.im) * ‖anchoredNevanlinna s w‖ ^ (2 * r + 3) +
        (‖w‖ + coefficientBound β * (r + (r + 2) : ℕ) / w.im ^ 2 : ℝ) *
          ‖anchoredNevanlinna s w‖ ^ (2 * r + 2) := by
  let S := anchoredNevanlinna s w
  let P := ∏ a, anchoredNevanlinna s (momentAux r w a)
  let T := ∑ a, anchoredInteraction s w (momentAux r w a) *
    excludedProduct (fun b => anchoredNevanlinna s (momentAux r w b)) a
  have hS : 0 ≤ ‖S‖ := norm_nonneg S
  have hcoef : ‖(2 - (β : ℂ)) / (β : ℂ)‖ ≤ coefficientBound β := first_coefficient_le β
  have hcoef' : ‖2 / (β : ℂ)‖ ≤ coefficientBound β := second_coefficient_le β
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
  have hhead : ‖((2 - (β : ℂ)) / (β : ℂ)) * anchoredDerivative s w + (-w)‖ ≤
      coefficientBound β * (‖S‖ / w.im) + ‖w‖ := by
    calc
      _ ≤ ‖((2 - (β : ℂ)) / (β : ℂ)) * anchoredDerivative s w‖ + ‖(-w : ℂ)‖ :=
        norm_add_le _ _
      _ = ‖(2 - (β : ℂ)) / (β : ℂ)‖ * ‖anchoredDerivative s w‖ + ‖w‖ := by
        rw [norm_mul, norm_neg]
      _ ≤ coefficientBound β * (‖S‖ / w.im) + ‖w‖ :=
        add_le_add_right (mul_le_mul hcoef hder (norm_nonneg _) (coefficientBound_pos β).le) _
      _ = _ := by ring
  have heq : loopIntegrand β s w (momentAux r w) -
      ((‖S‖ ^ (2 * r + 4) : ℝ) : ℂ) =
        (((2 - (β : ℂ)) / (β : ℂ)) * anchoredDerivative s w + (-w)) * P +
          (2 / (β : ℂ)) * T := by
    have hlead := anchored_momentAux_leading s r w
    change S ^ 2 * P = ((‖S‖ ^ (2 * r + 4) : ℝ) : ℂ) at hlead
    rw [← hlead]
    unfold loopIntegrand P T S
    ring
  rw [heq]
  calc
    _ ≤ ‖(((2 - (β : ℂ)) / (β : ℂ)) * anchoredDerivative s w + (-w)) * P‖ +
        ‖(2 / (β : ℂ)) * T‖ := norm_add_le _ _
    _ = ‖((2 - (β : ℂ)) / (β : ℂ)) * anchoredDerivative s w + (-w)‖ *
        ‖S‖ ^ (2 * r + 2) + ‖2 / (β : ℂ)‖ * ‖T‖ := by rw [norm_mul, norm_mul, hP]
    _ ≤ (coefficientBound β * (‖S‖ / w.im) + ‖w‖) * ‖S‖ ^ (2 * r + 2) +
        coefficientBound β * ((r + (r + 2) : ℕ) * (‖S‖ ^ (2 * r + 2) / w.im ^ 2)) :=
      add_le_add (mul_le_mul_of_nonneg_right hhead (pow_nonneg hS _))
        (mul_le_mul hcoef' hT (norm_nonneg _) (coefficientBound_pos β).le)
    _ = (coefficientBound β / w.im) * ‖S‖ ^ (2 * r + 3) +
        (‖w‖ + coefficientBound β * (r + (r + 2) : ℕ) / w.im ^ 2 : ℝ) * ‖S‖ ^ (2 * r + 2) := by
      simp only [pow_add, pow_succ, pow_zero]
      push_cast
      ring

/-- Young's inequality preserves the neighboring even moment. -/
theorem norm_loopIntegrand_remainder_half_leading (β : ℝ)
    (s : AnchoredCountingState) (r : ℕ) {w : ℂ} (hw : 0 < w.im) :
    ‖loopIntegrand β s w (momentAux r w) -
        ((‖anchoredNevanlinna s w‖ ^ (2 * r + 4) : ℝ) : ℂ)‖ ≤
      (1 / 2 : ℝ) * ‖anchoredNevanlinna s w‖ ^ (2 * r + 4) +
        (‖w‖ + (coefficientBound β * (r + (r + 2) : ℕ) + (coefficientBound β)^2 / 2) / w.im ^ 2 : ℝ) *
          ‖anchoredNevanlinna s w‖ ^ (2 * r + 2) := by
  apply (norm_loopIntegrand_remainder_adjacent β s r hw).trans
  let t := ‖anchoredNevanlinna s w‖
  have hy : (coefficientBound β / w.im) * t ≤ (1 / 2 : ℝ) * t ^ 2 + ((coefficientBound β)^2 / 2) / w.im ^ 2 := by
    calc
      _ ≤ (1 / 2 : ℝ) * t ^ 2 + (1 / 2) * (coefficientBound β / w.im) ^ 2 := by
        nlinarith [sq_nonneg (t - coefficientBound β / w.im)]
      _ = _ := by ring
  have hp := mul_le_mul_of_nonneg_right hy
    (pow_nonneg (norm_nonneg (anchoredNevanlinna s w)) (2 * r + 2))
  dsimp only [t] at hp
  have he3 : 2 * r + 3 = (2 * r + 2) + 1 := by omega
  have he4 : 2 * r + 4 = (2 * r + 2) + 2 := by omega
  simp only [he3, he4, pow_add, pow_one] at hp ⊢
  simp only [div_eq_mul_inv] at hp ⊢
  nlinarith [hp]


theorem norm_loopIntegrand_remainder_I (β : ℝ)
    (s : AnchoredCountingState) (r : ℕ) :
    ‖loopIntegrand β s Complex.I (momentAux r Complex.I) -
        ((‖s.val.2‖ ^ (2 * r + 4) : ℝ) : ℂ)‖ ≤
      (coefficientBound β * (r + (r + 2) : ℕ) + coefficientBound β + 2 : ℝ) * (1 + ‖s.val.2‖ ^ (2 * r + 3)) := by
  have h := norm_loopIntegrand_remainder_adjacent β s r
    (show 0 < Complex.I.im by simp)
  simp only [anchoredNevanlinna_I,Complex.I_im,one_div_one,one_pow,div_one,one_mul, Complex.norm_I] at h
  apply h.trans
  have hp := lower_pow_le_one_add (norm_nonneg s.val.2) (2*r+2)
  have hc : (0:ℝ) ≤ 1+coefficientBound β*(r+(r+2):ℕ) := by have := (coefficientBound_pos β).le; positivity
  have hh := mul_le_mul_of_nonneg_left hp hc
  push_cast at hh ⊢
  nlinarith [coefficientBound_pos β, pow_nonneg (norm_nonneg s.val.2) (2*r+3)]

end BourgadeHuang.RationalEdge
