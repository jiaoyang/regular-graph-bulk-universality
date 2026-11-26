import GeneralizedBulk.Graph.FinitePolynomial
import GeneralizedBulk.Graph.SpectralCompression

/-! Uniform quadratic growth of the genuine finite switching polynomial. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Graph
open External.RegularSpectralData

/-- An elementary quantitative reverse-triangle estimate for a quadratic.
The threshold depends only on explicit bounds on its three coefficients. -/
theorem quadratic_norm_lower_of_large (A B C h : ℂ) (a b c : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : a ≤ ‖A‖) (hB : ‖B‖ ≤ b) (hC : ‖C‖ ≤ c)
    (hlarge : 1 + 2 * (b + c) / a ≤ ‖h‖) :
    (a / 2) * ‖h‖ ^ 2 ≤ ‖A * h ^ 2 + B * h + C‖ := by
  have hnorm : ‖A‖ * ‖h‖ ^ 2 ≤ ‖A * h ^ 2 + B * h + C‖ + b * ‖h‖ + c := by
    calc
      _ = ‖A * h ^ 2‖ := by rw [norm_mul, norm_pow]
      _ = ‖(A * h ^ 2 + B * h + C) - B * h - C‖ := by congr 1; ring
      _ ≤ ‖(A * h ^ 2 + B * h + C) - B * h‖ + ‖C‖ := norm_sub_le _ _
      _ ≤ ‖A * h ^ 2 + B * h + C‖ + ‖B * h‖ + ‖C‖ :=
        add_le_add_right (norm_sub_le _ _) _
      _ ≤ _ := by rw [norm_mul]; nlinarith [norm_nonneg h]
  have hbase : 1 ≤ ‖h‖ := by
    have hnonneg : 0 ≤ 2 * (b + c) / a := by positivity
    linarith
  have hlinear : 2 * (b + c) ≤ a * ‖h‖ := by
    have hdiv : 2 * (b + c) / a ≤ ‖h‖ := by linarith
    simpa only [mul_comm] using (div_le_iff₀ ha).mp hdiv
  have hquad := mul_le_mul_of_nonneg_left hA (sq_nonneg ‖h‖)
  have hprod := mul_le_mul_of_nonneg_right hlinear (norm_nonneg h)
  nlinarith

theorem inverse_natCast_norm_le_one (N : ℕ) (hN : 0 < N) : ‖(N : ℂ)⁻¹‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_natCast]
  exact (inv_le_one₀ (by exact_mod_cast hN)).mpr (by exact_mod_cast hN)

theorem finite_ratio_norm_le (N d : ℕ) (hN : 0 < N) (hd : 0 < d) :
    ‖(1 - (N : ℂ)⁻¹) / (d : ℂ)‖ ≤ 2 := by
  have hdinv := inverse_natCast_norm_le_one d hd
  have hNinv := inverse_natCast_norm_le_one N hN
  rw [div_eq_mul_inv, norm_mul]
  have hnum : ‖1 - (N : ℂ)⁻¹‖ ≤ 2 := by
    have hn := norm_sub_le (1 : ℂ) (N : ℂ)⁻¹
    rw [norm_one] at hn
    linarith
  nlinarith [norm_nonneg ((d : ℂ)⁻¹), norm_nonneg (1 - (N : ℂ)⁻¹)]

theorem spectral_ratio_norm_le (d : ℕ) (hd : 0 < d) (E eta : ℝ) (heta : |eta| ≤ 1) :
    ‖spectralParameter E eta / (d : ℂ)‖ ≤ |E| + 1 := by
  have hz : ‖spectralParameter E eta‖ ≤ |E| + 1 := by
    calc
      _ ≤ ‖(E : ℂ)‖ + ‖(eta : ℂ) * Complex.I‖ := norm_add_le _ _
      _ ≤ _ := by simpa only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
        Complex.norm_I, mul_one] using add_le_add_left heta |E|
  rw [div_eq_mul_inv, norm_mul]
  exact (mul_le_mul_of_nonneg_left (inverse_natCast_norm_le_one d hd) (norm_nonneg _)).trans
    (by simpa only [mul_one] using hz)

private theorem leading_real_part (d : ℕ) (hd : 0 < d) (E eta : ℝ) :
    (1 - (spectralParameter E eta / (d : ℂ)) ^ 2).re =
      1 - (E / (d : ℝ)) ^ 2 + (eta / (d : ℝ)) ^ 2 := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  simp only [spectralParameter, div_eq_mul_inv, pow_two, Complex.sub_re,
    Complex.one_re, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.inv_re, Complex.inv_im, Complex.natCast_re, Complex.natCast_im,
    Complex.normSq_natCast]
  field_simp
  ring

/-- The strip-uniform leading coefficient has a strictly positive real part
at every real bulk energy, independently of the spectral height. -/
theorem finitePolynomial_leading_norm_lower (d : ℕ) (hd : 0 < d) (E : ℝ)
    (hE : |E| < d) (eta : ℝ) :
    0 < 1 - (E / (d : ℝ)) ^ 2 ∧
      1 - (E / (d : ℝ)) ^ 2 ≤ ‖1 - (spectralParameter E eta / (d : ℂ)) ^ 2‖ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp : |E / (d : ℝ)| < 1 := by rw [abs_div, abs_of_pos hdR, div_lt_one hdR]; exact hE
  constructor
  · exact sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr hp)
  · have hr : 1 - (E / (d : ℝ)) ^ 2 ≤ (1 - (spectralParameter E eta / (d : ℂ)) ^ 2).re := by
      rw [leading_real_part d hd E eta]
      linarith [sq_nonneg (eta / (d : ℝ))]
    exact hr.trans (Complex.re_le_norm _)

/-- Uniform growth in a shifted scalar variable, before comparing it with
`m`. Every finite-size coefficient and its correction is retained. -/
theorem finitePolynomial_norm_lower_of_large_h (N d : ℕ) (hN : 0 < N) (hd : 0 < d)
    (E : ℝ) (hE : |E| < d) (eta : ℝ) (heta : |eta| ≤ 1) (h : ℂ)
    (hlarge : 1 + 2 * (5 * (|E| + 1) + 6) / (1 - (E / (d : ℝ)) ^ 2) ≤ ‖h‖) :
    ((1 - (E / (d : ℝ)) ^ 2) / 2) * ‖h‖ ^ 2 ≤
      ‖finiteSwitchingPolynomial N d (spectralParameter E eta) h‖ := by
  rw [finiteSwitchingPolynomial_expand]
  apply quadratic_norm_lower_of_large _ _ _ _ _ _ _
    (finitePolynomial_leading_norm_lower d hd E hE eta).1 (by positivity) (by norm_num)
    (finitePolynomial_leading_norm_lower d hd E hE eta).2 _ _ hlarge
  · rw [norm_mul]
    have hz := spectral_ratio_norm_le d hd E eta heta
    have hr := finite_ratio_norm_le N d hN hd
    have hb : ‖1 - 2 * ((1 - (N : ℂ)⁻¹) / (d : ℂ))‖ ≤ 5 := by
      calc
        _ ≤ 1 + ‖(2 : ℂ)‖ * ‖((1 - (N : ℂ)⁻¹) / (d : ℂ))‖ := by
          simpa only [norm_one, norm_mul] using norm_sub_le (1 : ℂ)
            (2 * ((1 - (N : ℂ)⁻¹) / (d : ℂ)))
        _ ≤ 5 := by have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
                    rw [htwo]; linarith
    exact (mul_le_mul hz hb (norm_nonneg _) (by positivity)).trans (by ring_nf; rfl)
  · rw [norm_mul]
    have hr := finite_ratio_norm_le N d hN hd
    have hc : ‖1 - ((1 - (N : ℂ)⁻¹) / (d : ℂ))‖ ≤ 3 :=
      (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    exact (mul_le_mul hr hc (norm_nonneg _) (by norm_num)).trans (by norm_num)

/-- The constant-mode shift is uniformly bounded in a fixed vertical line
strictly below the distinguished eigenvalue `d`. -/
theorem constantMode_norm_le (N d : ℕ) (hN : 0 < N)
    (E eta : ℝ) (hE : E < d) :
    ‖constantMode N d (spectralParameter E eta)‖ ≤ ((d : ℝ) - E)⁻¹ := by
  have hgap : 0 < (d : ℝ) - E := sub_pos.mpr hE
  have hi := inverse_spectral_coefficient_le_of_gap (d : ℝ) E eta ((d : ℝ) - E) hgap
    (le_abs_self ((d : ℝ) - E))
  simp only [Complex.ofReal_natCast] at hi
  rw [constantMode, mul_inv_rev, norm_mul]
  exact (mul_le_mul_of_nonneg_right hi (norm_nonneg _)).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (inverse_natCast_norm_le_one N hN) (inv_nonneg.mpr hgap.le))

/-- The actual finite scalar polynomial has uniform quadratic growth for
large `|m|`. The threshold and positive coefficient depend only on `d,E`,
not on graph size or on the height in the displayed strip. -/
theorem exists_finitePolynomial_lower_bound (d : ℕ) (hd : 0 < d) (E : ℝ) (hE : |E| < d) :
    ∃ c : ℝ, 0 < c ∧ ∃ T0 : ℝ, 0 < T0 ∧
      ∀ N : ℕ, 0 < N → ∀ eta : ℝ, |eta| ≤ 1 → ∀ m : ℂ, T0 ≤ ‖m‖ →
        c * ‖m‖ ^ 2 ≤ ‖finiteSwitchingPolynomial N d (spectralParameter E eta)
          (m - constantMode N d (spectralParameter E eta))‖ := by
  let a : ℝ := 1 - (E / (d : ℝ)) ^ 2
  let Q : ℝ := ((d : ℝ) - E)⁻¹
  let U : ℝ := 1 + 2 * (5 * (|E| + 1) + 6) / a
  have ha : 0 < a := (finitePolynomial_leading_norm_lower d hd E hE 0).1
  have hgap : 0 < (d : ℝ) - E := sub_pos.mpr ((le_abs_self E).trans_lt hE)
  have hQ : 0 < Q := inv_pos.mpr hgap
  have hU : 0 < U := by dsimp [U]; positivity
  refine ⟨a / 8, by positivity, 2 * (Q + U), by positivity, ?_⟩
  intro N hN eta heta m hm
  have hq := constantMode_norm_le N d hN E eta ((le_abs_self E).trans_lt hE)
  have hdiff := norm_sub_norm_le m (constantMode N d (spectralParameter E eta))
  have hh : U ≤ ‖m - constantMode N d (spectralParameter E eta)‖ := by
    change ‖constantMode N d (spectralParameter E eta)‖ ≤ Q at hq
    linarith
  have hhalf : ‖m‖ / 2 ≤ ‖m - constantMode N d (spectralParameter E eta)‖ := by
    change ‖constantMode N d (spectralParameter E eta)‖ ≤ Q at hq
    linarith
  have hp := finitePolynomial_norm_lower_of_large_h N d hN hd E hE eta heta
    (m - constantMode N d (spectralParameter E eta)) hh
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ ‖m‖ / 2) (norm_nonneg _)).mpr hhalf
  change a / 2 * _ ≤ _ at hp
  calc
    a / 8 * ‖m‖ ^ 2 = (a / 2) * (‖m‖ / 2) ^ 2 := by ring
    _ ≤ (a / 2) * ‖m - constantMode N d (spectralParameter E eta)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ _ := hp

end GeneralizedBulk.Graph
