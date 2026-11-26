import GeneralizedBulk.Gaussian.ExtendedWhitening

/-! Exact scalar/transverse eigenvalues of the actual star whitening Gram
operator, in the scalar-adapted basis used by the empirical signal. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Gaussian
open GeneralizedBulk.Entropy.Channel

theorem simplex_bilinear_parseval (d : ℕ) (hd : 2 ≤ d) (x y : Transverse d) :
    (∑ i : Fin d, @inner ℝ (Transverse d) _ (simplex d hd i) x *
      @inner ℝ (Transverse d) _ (simplex d hd i) y) =
      ((d : ℝ) / ((d : ℝ) - 1)) * @inner ℝ (Transverse d) _ x y := by
  have hh := congrArg (fun z : Transverse d => @inner ℝ (Transverse d) _ z y) (simplex_frame d hd x)
  simpa only [sum_inner, real_inner_smul_left] using hh

theorem starRow_bilinear (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) (x y : WhiteStar d) :
    (∑ j : Fin (d + 1), @inner ℝ (WhiteStar d) _ (starRow d hd E j) x *
      @inner ℝ (WhiteStar d) _ (starRow d hd E j) y) =
      (((d : ℝ) + E ^ 2) / d) * x.fst * y.fst +
        (((d : ℝ) ^ 2 - E ^ 2) / ((d : ℝ) * ((d : ℝ) - 1))) *
          @inner ℝ (Transverse d) _ x.snd y.snd := by
  have hsx : (∑ i : Fin d, @inner ℝ (Transverse d) _ (simplex d hd i) x.snd) = 0 := by
    rw [← sum_inner, simplex_sum, inner_zero_left]
  have hsy : (∑ i : Fin d, @inner ℝ (Transverse d) _ (simplex d hd i) y.snd) = 0 := by
    rw [← sum_inner, simplex_sum, inner_zero_left]
  let c : ℝ := E / d
  let rho : ℝ := starRho d E
  have hterm (i : Fin d) :
      (c * x.fst + rho * @inner ℝ (Transverse d) _ (simplex d hd i) x.snd) *
        (c * y.fst + rho * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd) =
      c ^ 2 * x.fst * y.fst + (c * rho * x.fst) * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd +
        (c * rho * y.fst) * @inner ℝ (Transverse d) _ (simplex d hd i) x.snd +
        rho ^ 2 * (@inner ℝ (Transverse d) _ (simplex d hd i) x.snd * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd) := by ring
  rw [Fin.sum_univ_succ]
  simp only [starRow_inner_root, starRow_inner_leaf]
  change x.fst * y.fst + (∑ i : Fin d,
    (c * x.fst + rho * @inner ℝ (Transverse d) _ (simplex d hd i) x.snd) *
    (c * y.fst + rho * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd)) = _
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, hsx, hsy, mul_zero, add_zero, simplex_bilinear_parseval]
  dsimp [c, rho]
  rw [starRho_sq d hd E hE]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : (d : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  <;> ring

end GeneralizedBulk.Gaussian
