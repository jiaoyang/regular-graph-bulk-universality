import BourgadeHuang.MomentBounds
import BourgadeHuang.Integrability

/-!
# The lower-order terms of the moment loop equation

At the parameter `I`, the balanced auxiliary product isolates the positive
`(2r+4)`th resolvent moment. Every other term is bounded by a constant times
one plus the adjacent lower moment. This is the deterministic step in (4.56).
-/

noncomputable section
open scoped BigOperators

namespace BourgadeHuang

theorem norm_momentAux_resolvent {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (r : ℕ) (w : ℂ) (a : Fin (r + (r + 2))) :
    ‖microscopicResolvent x center (momentAux r w a)‖ =
      ‖microscopicResolvent x center w‖ := by
  rcases momentAux_eq_or r w a with h | h
  · rw [h]
  · rw [h, microscopicResolvent_reflection, norm_star]

theorem norm_momentAux_product {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (r : ℕ) (w : ℂ) :
    ‖∏ a, microscopicResolvent x center (momentAux r w a)‖ =
      ‖microscopicResolvent x center w‖ ^ (2 * r + 2) := by
  rw [norm_prod]
  simp_rw [norm_momentAux_resolvent]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

theorem norm_momentAux_excludedProduct {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (r : ℕ) (w : ℂ) (a : Fin (r + (r + 2))) :
    ‖excludedProduct (fun b => microscopicResolvent x center (momentAux r w b)) a‖ =
      ‖microscopicResolvent x center w‖ ^ (2 * r + 1) := by
  unfold excludedProduct
  rw [norm_prod]
  simp_rw [norm_momentAux_resolvent]
  simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ a),
    Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- The explicit deterministic remainder bound underlying (4.56), with `w = I`.
No large-N hypothesis or expectation estimate is assumed. -/
theorem norm_loopIntegrand_remainder {N : ℕ} (β : Beta) (x : Fin N → ℝ)
    (center : ℝ) (r : ℕ) :
    ‖loopIntegrand β x center Complex.I (momentAux r Complex.I) -
        ((‖microscopicResolvent x center Complex.I‖ ^ (2 * r + 4) : ℝ) : ℂ)‖ ≤
      (2 * (r + (r + 2) : ℕ) + 2 : ℝ) *
        (1 + ‖microscopicResolvent x center Complex.I‖ ^ (2 * r + 3)) := by
  let S := microscopicResolvent x center Complex.I
  let P := ∏ a, microscopicResolvent x center (momentAux r Complex.I a)
  let T := ∑ a, interaction x Complex.I (momentAux r Complex.I a) *
    excludedProduct (fun b => microscopicResolvent x center (momentAux r Complex.I b)) a
  have hS : 0 ≤ ‖S‖ := norm_nonneg S
  have hcoef : ‖(2 - β.value) / β.value‖ ≤ 1 := by
    cases β <;> norm_num [Beta.value]
  have hcoef' : ‖2 / β.value‖ ≤ 2 := by
    cases β <;> norm_num [Beta.value]
  have hder : ‖resolventDerivative x Complex.I‖ ≤ ‖S‖ := by
    simpa [S] using norm_resolventDerivative_le_norm x center (w := Complex.I) (by simp)
  have hinter (a : Fin (r + (r + 2))) :
      ‖interaction x Complex.I (momentAux r Complex.I a)‖ ≤ ‖S‖ := by
    simpa [S] using norm_interaction_le x center (w := Complex.I) (by simp)
      (momentAux_eq_or r Complex.I a)
  have hP : ‖P‖ = ‖S‖ ^ (2 * r + 2) :=
    norm_momentAux_product x center r Complex.I
  have hterm (a : Fin (r + (r + 2))) :
      ‖interaction x Complex.I (momentAux r Complex.I a) *
          excludedProduct
            (fun b => microscopicResolvent x center (momentAux r Complex.I b)) a‖ ≤
        ‖S‖ ^ (2 * r + 2) := by
    rw [norm_mul, norm_momentAux_excludedProduct]
    calc
      _ ≤ ‖S‖ * ‖S‖ ^ (2 * r + 1) :=
        mul_le_mul_of_nonneg_right (hinter a) (pow_nonneg hS _)
      _ = ‖S‖ ^ (2 * r + 2) := by
        simp only [pow_add, pow_one, pow_two]
        ring
  have hT : ‖T‖ ≤ (r + (r + 2) : ℕ) * ‖S‖ ^ (2 * r + 2) := by
    calc
      ‖T‖ ≤ ∑ a, ‖interaction x Complex.I (momentAux r Complex.I a) *
          excludedProduct
            (fun b => microscopicResolvent x center (momentAux r Complex.I b)) a‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _a : Fin (r + (r + 2)), ‖S‖ ^ (2 * r + 2) :=
        Finset.sum_le_sum (fun a _ => hterm a)
      _ = _ := by simp
  have hhead : ‖((2 - β.value) / β.value) * resolventDerivative x Complex.I + 1‖ ≤
      ‖S‖ + 1 := by
    calc
      _ ≤ ‖((2 - β.value) / β.value) * resolventDerivative x Complex.I‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
      _ = ‖(2 - β.value) / β.value‖ * ‖resolventDerivative x Complex.I‖ + 1 := by
        rw [norm_mul, norm_one]
      _ ≤ 1 * ‖S‖ + 1 :=
        add_le_add_right (mul_le_mul hcoef hder (norm_nonneg _) (by norm_num)) _
      _ = _ := by ring
  have heq : loopIntegrand β x center Complex.I (momentAux r Complex.I) -
      ((‖S‖ ^ (2 * r + 4) : ℝ) : ℂ) =
        (((2 - β.value) / β.value) * resolventDerivative x Complex.I + 1) * P +
          (2 / β.value) * T := by
    have hlead := momentAux_leading x center r Complex.I
    change S ^ 2 * P = ((‖S‖ ^ (2 * r + 4) : ℝ) : ℂ) at hlead
    rw [← hlead]
    unfold loopIntegrand P T S
    ring
  rw [heq]
  calc
    _ ≤ ‖(((2 - β.value) / β.value) * resolventDerivative x Complex.I + 1) * P‖ +
        ‖(2 / β.value) * T‖ := norm_add_le _ _
    _ = ‖((2 - β.value) / β.value) * resolventDerivative x Complex.I + 1‖ *
        ‖S‖ ^ (2 * r + 2) + ‖2 / β.value‖ * ‖T‖ := by rw [norm_mul, norm_mul, hP]
    _ ≤ (‖S‖ + 1) * ‖S‖ ^ (2 * r + 2) +
        2 * ((r + (r + 2) : ℕ) * ‖S‖ ^ (2 * r + 2)) :=
      add_le_add (mul_le_mul_of_nonneg_right hhead (pow_nonneg hS _))
        (mul_le_mul hcoef' hT (norm_nonneg _) (by norm_num))
    _ = ‖S‖ ^ (2 * r + 3) + (2 * (r + (r + 2) : ℕ) + 1 : ℝ) *
        ‖S‖ ^ (2 * r + 2) := by
      rw [show 2 * r + 3 = (2 * r + 2) + 1 by omega, pow_succ]
      push_cast
      ring
    _ ≤ (1 + ‖S‖ ^ (2 * r + 3)) + (2 * (r + (r + 2) : ℕ) + 1 : ℝ) *
        (1 + ‖S‖ ^ (2 * r + 3)) := by
      refine add_le_add (le_add_of_nonneg_left (by norm_num)) ?_
      exact mul_le_mul_of_nonneg_left (lower_pow_le_one_add hS (2 * r + 2))
        (by positivity)
    _ = _ := by push_cast; ring

/-- The remainder bound at any upper-half-plane parameter. The coefficient is explicit
and stays bounded when the imaginary part stays away from zero. -/
theorem norm_loopIntegrand_remainder_upper {N : ℕ} (β : Beta) (x : Fin N → ℝ)
    (center : ℝ) (r : ℕ) {w : ℂ} (hw : 0 < w.im) :
    ‖loopIntegrand β x center w (momentAux r w) -
        ((‖microscopicResolvent x center w‖ ^ (2 * r + 4) : ℝ) : ℂ)‖ ≤
      (1 / w.im + 1 + 2 * (r + (r + 2) : ℕ) / w.im ^ 2 : ℝ) *
        (1 + ‖microscopicResolvent x center w‖ ^ (2 * r + 3)) := by
  let S := microscopicResolvent x center w
  let P := ∏ a, microscopicResolvent x center (momentAux r w a)
  let T := ∑ a, interaction x w (momentAux r w a) *
    excludedProduct (fun b => microscopicResolvent x center (momentAux r w b)) a
  have hS : 0 ≤ ‖S‖ := norm_nonneg S
  have hcoef : ‖(2 - β.value) / β.value‖ ≤ 1 := by
    cases β <;> norm_num [Beta.value]
  have hcoef' : ‖2 / β.value‖ ≤ 2 := by
    cases β <;> norm_num [Beta.value]
  have hder : ‖resolventDerivative x w‖ ≤ ‖S‖ / w.im :=
    norm_resolventDerivative_le_norm x center hw
  have hinter (a : Fin (r + (r + 2))) :
      ‖interaction x w (momentAux r w a)‖ ≤ ‖S‖ / w.im ^ 2 := by
    simpa [S] using norm_interaction_le x center hw
      (momentAux_eq_or r w a)
  have hP : ‖P‖ = ‖S‖ ^ (2 * r + 2) :=
    norm_momentAux_product x center r w
  have hterm (a : Fin (r + (r + 2))) :
      ‖interaction x w (momentAux r w a) *
          excludedProduct
            (fun b => microscopicResolvent x center (momentAux r w b)) a‖ ≤
        ‖S‖ ^ (2 * r + 2) / w.im ^ 2 := by
    rw [norm_mul, norm_momentAux_excludedProduct]
    calc
      _ ≤ (‖S‖ / w.im ^ 2) * ‖S‖ ^ (2 * r + 1) :=
        mul_le_mul_of_nonneg_right (hinter a) (pow_nonneg hS _)
      _ = ‖S‖ ^ (2 * r + 2) / w.im ^ 2 := by
        simp only [pow_add, pow_one, pow_two]
        ring
  have hT : ‖T‖ ≤ (r + (r + 2) : ℕ) * (‖S‖ ^ (2 * r + 2) / w.im ^ 2) := by
    calc
      ‖T‖ ≤ ∑ a, ‖interaction x w (momentAux r w a) *
          excludedProduct
            (fun b => microscopicResolvent x center (momentAux r w b)) a‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _a : Fin (r + (r + 2)), ‖S‖ ^ (2 * r + 2) / w.im ^ 2 :=
        Finset.sum_le_sum (fun a _ => hterm a)
      _ = _ := by simp
  have hhead : ‖((2 - β.value) / β.value) * resolventDerivative x w + 1‖ ≤
      ‖S‖ / w.im + 1 := by
    calc
      _ ≤ ‖((2 - β.value) / β.value) * resolventDerivative x w‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
      _ = ‖(2 - β.value) / β.value‖ * ‖resolventDerivative x w‖ + 1 := by
        rw [norm_mul, norm_one]
      _ ≤ 1 * (‖S‖ / w.im) + 1 :=
        add_le_add_right (mul_le_mul hcoef hder (norm_nonneg _) (by norm_num)) _
      _ = _ := by ring
  have heq : loopIntegrand β x center w (momentAux r w) -
      ((‖S‖ ^ (2 * r + 4) : ℝ) : ℂ) =
        (((2 - β.value) / β.value) * resolventDerivative x w + 1) * P +
          (2 / β.value) * T := by
    have hlead := momentAux_leading x center r w
    change S ^ 2 * P = ((‖S‖ ^ (2 * r + 4) : ℝ) : ℂ) at hlead
    rw [← hlead]
    unfold loopIntegrand P T S
    ring
  rw [heq]
  calc
    _ ≤ ‖(((2 - β.value) / β.value) * resolventDerivative x w + 1) * P‖ +
        ‖(2 / β.value) * T‖ := norm_add_le _ _
    _ = ‖((2 - β.value) / β.value) * resolventDerivative x w + 1‖ *
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
    _ ≤ (1 / w.im) * (1 + ‖S‖ ^ (2 * r + 3)) +
        (1 + 2 * (r + (r + 2) : ℕ) / w.im ^ 2 : ℝ) *
          (1 + ‖S‖ ^ (2 * r + 3)) := by
      refine add_le_add ?_ ?_
      · exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (by norm_num)) (by positivity)
      · exact mul_le_mul_of_nonneg_left (lower_pow_le_one_add hS (2 * r + 2))
          (by positivity)
    _ = _ := by push_cast; ring

end BourgadeHuang
