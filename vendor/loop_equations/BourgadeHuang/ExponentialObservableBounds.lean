import BourgadeHuang.ExponentialMomentControl
import BourgadeHuang.HierarchyCharacterization

/-!
# Exponential bounds for characteristic-polynomial observables

The centering exponential cancels the linear deterministic part of the finite
product. Consequently the observable is controlled by the centered resolvent,
with a constant independent of the number of particles.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace BourgadeHuang

/-- A complex factor has a quadratic exponential upper bound. -/
theorem norm_one_add_le_exp_re_add_norm_sq (z : ℂ) :
    ‖1 + z‖ ≤ Real.exp (z.re + ‖z‖ ^ 2 / 2) := by
  have hsq : ‖1 + z‖ ^ 2 = 1 + 2 * z.re + ‖z‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im]
    ring
  have he := Real.add_one_le_exp (2 * z.re + ‖z‖ ^ 2)
  have hexp : Real.exp (z.re + ‖z‖ ^ 2 / 2) ^ 2 = Real.exp (2 * z.re + ‖z‖ ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  nlinarith [norm_nonneg (1 + z), Real.exp_pos (z.re + ‖z‖ ^ 2 / 2)]

/-- All linear exponential moments follow from one exponential-square moment. -/
theorem integrable_exp_mul_abs_of_exp_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) {t : ℝ} (ht : 0 < t)
    (hint : Integrable (fun ω => Real.exp (t * X ω ^ 2)) μ) (a : ℝ) :
    Integrable (fun ω => Real.exp (a * |X ω|)) μ := by
  apply (hint.const_mul (Real.exp (a ^ 2 / (4 * t)))).mono'
    (Real.continuous_exp.comp_aestronglyMeasurable ((continuous_abs.comp_aestronglyMeasurable hX).const_mul a))
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := sq_nonneg (2 * t * |X ω| - a)
  apply (mul_le_mul_right (by positivity : 0 < 4 * t)).mp
  field_simp
  rw [← sq_abs (X ω)]
  nlinarith only [hs]

/-- The ratio bound is independent of particle number and retains the exact
cancellation of the centering term. No numerator half-plane condition is needed. -/
theorem norm_finiteCharacteristicRatio_le_exp_resolvent {N : ℕ}
    (x : Fin N → ℝ) (center : ℝ) (u : ℂ) {v : ℂ} (hv : 0 < v.im) :
    ‖finiteCharacteristicRatio x center u v‖ ≤
      Real.exp ((‖u - v‖ + ‖u - v‖ ^ 2 / (2 * v.im)) *
        ‖microscopicResolvent x center v‖) := by
  have hvne (i : Fin N) : (x i : ℂ) - v ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    exact (ne_of_gt hv) hh
  have hfac (i : Fin N) : ((x i : ℂ) - u) / ((x i : ℂ) - v) =
      1 + (v - u) * ((x i : ℂ) - v)⁻¹ := by
    field_simp [hvne i]
  let S := microscopicResolvent x center v
  have hsq : (∑ i, ‖((x i : ℂ) - v)⁻¹‖ ^ 2) = S.im / v.im := by
    simp only [Complex.sq_norm, Complex.normSq_inv]
    rw [show S.im = v.im * ∑ i, (Complex.normSq ((x i : ℂ) - v))⁻¹ from
      microscopicResolvent_im_eq x center v]
    field_simp [ne_of_gt hv]
  have hsum : ((center : ℂ) * (u - v)).re +
      ∑ i, (((v - u) * ((x i : ℂ) - v)⁻¹).re +
        ‖(v - u) * ((x i : ℂ) - v)⁻¹‖ ^ 2 / 2) =
      ((v - u) * S).re + ‖u - v‖ ^ 2 / 2 * (S.im / v.im) := by
    simp only [norm_mul, mul_pow, Finset.sum_add_distrib]
    have hn : ‖v - u‖ = ‖u - v‖ := norm_sub_rev _ _
    rw [hn]
    rw [show (∑ i, ‖u - v‖ ^ 2 * ‖((x i : ℂ) - v)⁻¹‖ ^ 2 / 2) =
      ‖u - v‖ ^ 2 / 2 * ∑ i, ‖((x i : ℂ) - v)⁻¹‖ ^ 2 by rw [Finset.mul_sum]; congr 1; funext i; ring]
    rw [hsq]
    rw [← Complex.re_sum, ← Finset.mul_sum]
    dsimp [S, microscopicResolvent]
    ring
  calc
    ‖finiteCharacteristicRatio x center u v‖ =
        Real.exp (((center : ℂ) * (u - v)).re) *
          ∏ i, ‖1 + (v - u) * ((x i : ℂ) - v)⁻¹‖ := by
      simp only [finiteCharacteristicRatio, norm_mul, Complex.norm_exp, norm_prod, hfac]
    _ ≤ Real.exp (((center : ℂ) * (u - v)).re) *
        ∏ i, Real.exp (((v - u) * ((x i : ℂ) - v)⁻¹).re +
          ‖(v - u) * ((x i : ℂ) - v)⁻¹‖ ^ 2 / 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun _ _ => norm_one_add_le_exp_re_add_norm_sq _)
    _ = Real.exp (((v - u) * S).re + ‖u - v‖ ^ 2 / 2 * (S.im / v.im)) := by
      rw [← Real.exp_sum, ← Real.exp_add, hsum]
    _ ≤ Real.exp ((‖u - v‖ + ‖u - v‖ ^ 2 / (2 * v.im)) * ‖S‖) := by
      apply Real.exp_le_exp.mpr
      have hre : ((v - u) * S).re ≤ ‖u - v‖ * ‖S‖ := by
        simpa only [norm_mul, norm_sub_rev] using Complex.re_le_norm ((v - u) * S)
      have him := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (Complex.im_le_norm S) hv.le)
        (show 0 ≤ ‖u - v‖ ^ 2 / 2 by positivity)
      calc
        _ ≤ ‖u - v‖ * ‖S‖ + ‖u - v‖ ^ 2 / 2 * (‖S‖ / v.im) := add_le_add hre him
        _ = _ := by ring

/-- Reflection preserves the centered ratio. -/
theorem finiteCharacteristicRatio_reflection {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) (u v : ℂ) :
    finiteCharacteristicRatio x center (star u) (star v) =
      star (finiteCharacteristicRatio x center u v) := by
  have he : Complex.exp ((center : ℂ) * (star u - star v)) =
      star (Complex.exp ((center : ℂ) * (u - v))) := by
    simpa only [map_mul, map_sub, Complex.conj_ofReal, Complex.star_def] using
      (Complex.exp_conj (x := (center : ℂ) * (u - v)))
  simp only [finiteCharacteristicRatio, he]
  simp [map_prod]

/-- The exponential resolvent bound holds in both half-planes. -/
theorem norm_finiteCharacteristicRatio_le_exp_resolvent_offReal {N : ℕ}
    (x : Fin N → ℝ) (center : ℝ) (u : ℂ) {v : ℂ} (hv : v.im ≠ 0) :
    ‖finiteCharacteristicRatio x center u v‖ ≤
      Real.exp ((‖u - v‖ + ‖u - v‖ ^ 2 / (2 * |v.im|)) *
        ‖microscopicResolvent x center v‖) := by
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · have hv' : 0 < (star v).im := by simpa using neg_pos.mpr hneg
    have hh := norm_finiteCharacteristicRatio_le_exp_resolvent x center (star u) hv'
    rw [finiteCharacteristicRatio_reflection, norm_star, microscopicResolvent_reflection,
      norm_star, ← star_sub, norm_star] at hh
    simpa only [Complex.star_def, Complex.conj_im, abs_of_neg hneg] using hh
  · simpa only [abs_of_pos hpos] using
      norm_finiteCharacteristicRatio_le_exp_resolvent x center u hpos

/-- A product of ratios is controlled by a sum of resolvent norms with constants
that do not depend on the particle number. -/
theorem norm_finiteExponentialObservable_le_exp_resolvents {N q : ℕ}
    (x : Fin N → ℝ) (center : ℝ) (t s : Fin q → ℂ)
    (hs : ∀ j, (s j).im ≠ 0) :
    ‖finiteExponentialObservable x center t s‖ ≤
      Real.exp (∑ j, (‖t j - s j‖ + ‖t j - s j‖ ^ 2 / (2 * |(s j).im|)) *
        ‖microscopicResolvent x center (s j)‖) := by
  rw [Real.exp_sum]
  simp only [finiteExponentialObservable, norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    (fun j _ => norm_finiteCharacteristicRatio_le_exp_resolvent_offReal x center (t j) (hs j))


end BourgadeHuang
