import GeneralizedBulk.Entropy.ChannelGeometry

/-! Actual positive weighted frames for the correlated regular-star channels. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel

def rho (c : ℝ) : ℝ := Real.sqrt (1 - c ^ 2)
def alpha (c : ℝ) : ℝ := (Real.sqrt (1 + c) + Real.sqrt (1 - c)) / 2
def beta (c : ℝ) : ℝ := (Real.sqrt (1 + c) - Real.sqrt (1 - c)) / 2

theorem rho_pos (c : ℝ) (hc : |c| < 1) : 0 < rho c := by
  apply Real.sqrt_pos.mpr
  exact sub_pos.mpr ((sq_lt_one_iff_abs_lt_one c).mpr hc)

theorem rho_sq (c : ℝ) (hc : |c| < 1) : rho c ^ 2 = 1 - c ^ 2 :=
  Real.sq_sqrt (sub_nonneg.mpr ((sq_lt_one_iff_abs_lt_one c).mpr hc).le)

theorem alpha_sq_add_beta_sq (c : ℝ) (hc : |c| < 1) : alpha c ^ 2 + beta c ^ 2 = 1 := by
  have hp := Real.sq_sqrt (by linarith [(abs_lt.mp hc).1] : 0 ≤ 1 + c)
  have hm := Real.sq_sqrt (by linarith [(abs_lt.mp hc).2] : 0 ≤ 1 - c)
  dsimp [alpha, beta]
  nlinarith

theorem two_alpha_mul_beta (c : ℝ) (hc : |c| < 1) : 2 * alpha c * beta c = c := by
  have hp := Real.sq_sqrt (by linarith [(abs_lt.mp hc).1] : 0 ≤ 1 + c)
  have hm := Real.sq_sqrt (by linarith [(abs_lt.mp hc).2] : 0 ≤ 1 - c)
  dsimp [alpha, beta]
  nlinarith

theorem alpha_sq_sub_beta_sq (c : ℝ) (hc : |c| < 1) : alpha c ^ 2 - beta c ^ 2 = rho c := by
  have hp : 0 ≤ 1 + c := by linarith [(abs_lt.mp hc).1]
  have hmul : Real.sqrt (1 + c) * Real.sqrt (1 - c) = rho c := by
    rw [← Real.sqrt_mul hp]
    unfold rho
    congr 1
    ring
  dsimp [alpha, beta]
  nlinarith

theorem alpha_sq (c : ℝ) (hc : |c| < 1) : alpha c ^ 2 = (1 + rho c) / 2 := by
  nlinarith [alpha_sq_add_beta_sq c hc, alpha_sq_sub_beta_sq c hc]

theorem beta_sq (c : ℝ) (hc : |c| < 1) : beta c ^ 2 = (1 - rho c) / 2 := by
  nlinarith [alpha_sq_add_beta_sq c hc, alpha_sq_sub_beta_sq c hc]

def weightA (d : ℕ) (c : ℝ) : ℝ := (rho c - 1 + 2 / (d : ℝ)) / (2 * rho c)
def weightB (d : ℕ) (c : ℝ) : ℝ := (rho c + 1 - 2 / (d : ℝ)) / (2 * rho c)

theorem weight_sum (d : ℕ) (c : ℝ) (hc : |c| < 1) : weightA d c + weightB d c = 1 := by
  unfold weightA weightB
  field_simp [ne_of_gt (rho_pos c hc)]
  ring

/-- The regular-graph bulk interval is exactly the strict positivity condition
for the weighted frame. No channel-coercivity hypothesis enters this proof. -/
theorem bulk_rho_lower (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    |c| < 1 ∧ 1 - 2 / (d : ℝ) < rho c := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hdp)).2
    nlinarith [sq_nonneg ((d : ℝ) - 2)]
  have hc : |c| < 1 := (sq_lt_one_iff_abs_lt_one c).mp (hbulk.trans_le hb)
  refine ⟨hc, ?_⟩
  have ht : 0 ≤ 1 - 2 / (d : ℝ) := by
    have hh : 2 / (d : ℝ) ≤ 1 := (div_le_iff₀ hdp).2 (by linarith)
    linarith
  apply (sq_lt_sq₀ ht (rho_pos c hc).le).mp
  rw [rho_sq c hc]
  have hid : 1 - (1 - 2 / (d : ℝ)) ^ 2 = 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2 := by
    field_simp
    ring
  linarith

theorem bulk_weights_pos (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    0 < weightA d c ∧ 0 < weightB d c := by
  obtain ⟨hc, hr⟩ := bulk_rho_lower d hd c hbulk
  have hp := rho_pos c hc
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have ht : 0 < 1 - 2 / (d : ℝ) := by
    have hh : 2 / (d : ℝ) < 1 := (div_lt_iff₀ hdp).2 (by linarith)
    linarith
  constructor <;> simp only [weightA, weightB] <;> apply div_pos _ (by positivity) <;> linarith

theorem frame_scalar_weight (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) :
    weightA d c * alpha c ^ 2 + weightB d c * beta c ^ 2 = 1 / (d : ℝ) := by
  rw [alpha_sq c hc, beta_sq c hc]
  unfold weightA weightB
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  field_simp [ne_of_gt (rho_pos c hc), hd0]
  ring

theorem frame_transverse_weight (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) :
    weightA d c * beta c ^ 2 + weightB d c * alpha c ^ 2 = ((d : ℝ) - 1) / (d : ℝ) := by
  rw [alpha_sq c hc, beta_sq c hc]
  unfold weightA weightB
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  field_simp [ne_of_gt (rho_pos c hc), hd0]
  ring

/-- Orthonormal endpoint-adapted directions in the actual edge subspace. -/
def directionA (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (i : Fin d) : WhiteStar d :=
  (WithLp.equiv 2 _).symm (alpha c, -(beta c) • simplex d hd i)

def directionB (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (i : Fin d) : WhiteStar d :=
  (WithLp.equiv 2 _).symm (beta c, alpha c • simplex d hd i)

theorem directionA_inner (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (i : Fin d) (y : WhiteStar d) :
    @inner ℝ (WhiteStar d) _ (directionA d hd c i) y =
      alpha c * y.fst - beta c * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd := by
  simp only [directionA, WithLp.prod_inner_apply, WithLp.equiv_symm_fst,
    WithLp.equiv_symm_snd, inner_smul_left, starRingEnd_apply, star_trivial,
    RCLike.inner_apply, conj_trivial]
  ring

theorem directionB_inner (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (i : Fin d) (y : WhiteStar d) :
    @inner ℝ (WhiteStar d) _ (directionB d hd c i) y =
      beta c * y.fst + alpha c * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd := by
  simp only [directionB, WithLp.prod_inner_apply, WithLp.equiv_symm_fst,
    WithLp.equiv_symm_snd, inner_smul_left, starRingEnd_apply, star_trivial,
    RCLike.inner_apply, conj_trivial]
  ring

theorem directionA_norm_sq (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    ‖directionA d hd c i‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, directionA_inner]
  simp only [directionA, WithLp.equiv_symm_fst, WithLp.equiv_symm_snd,
    inner_smul_right, simplex_inner, ↓reduceIte, mul_one]
  nlinarith [alpha_sq_add_beta_sq c hc]

theorem directionB_norm_sq (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    ‖directionB d hd c i‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, directionB_inner]
  simp only [directionB, WithLp.equiv_symm_fst, WithLp.equiv_symm_snd,
    inner_smul_right, simplex_inner, ↓reduceIte, mul_one]
  nlinarith [alpha_sq_add_beta_sq c hc]

theorem directionA_inner_directionB (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (i : Fin d) :
    @inner ℝ (WhiteStar d) _ (directionA d hd c i) (directionB d hd c i) = 0 := by
  rw [directionA_inner]
  simp only [directionB, WithLp.equiv_symm_fst, WithLp.equiv_symm_snd,
    inner_smul_right, simplex_inner, ↓reduceIte, mul_one]
  ring

theorem whiteStar_norm_sq (d : ℕ) (y : WhiteStar d) : ‖y‖ ^ 2 = y.fst ^ 2 + ‖y.snd‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, WithLp.prod_inner_apply]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The exact weighted frame identity in energy form. This is the concrete
finite-dimensional ingredient in the Fisher and Hermite-chaos positivity proofs. -/
theorem weighted_frame_energy (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (y : WhiteStar d) :
    (∑ i : Fin d, (weightA d c * (@inner ℝ (WhiteStar d) _ (directionA d hd c i) y) ^ 2 +
      weightB d c * (@inner ℝ (WhiteStar d) _ (directionB d hd c i) y) ^ 2)) = ‖y‖ ^ 2 := by
  have hs : (∑ i : Fin d, @inner ℝ (Transverse d) _ (simplex d hd i) y.snd) = 0 := by
    rw [← sum_inner, simplex_sum, inner_zero_left]
  have ht (i : Fin d) :
      weightA d c * (@inner ℝ (WhiteStar d) _ (directionA d hd c i) y) ^ 2 +
          weightB d c * (@inner ℝ (WhiteStar d) _ (directionB d hd c i) y) ^ 2 =
        (weightA d c * alpha c ^ 2 + weightB d c * beta c ^ 2) * y.fst ^ 2 +
        (weightA d c * beta c ^ 2 + weightB d c * alpha c ^ 2) *
          (@inner ℝ (Transverse d) _ (simplex d hd i) y.snd) ^ 2 +
        (2 * alpha c * beta c * (weightB d c - weightA d c) * y.fst) *
          @inner ℝ (Transverse d) _ (simplex d hd i) y.snd := by
    rw [directionA_inner, directionB_inner]
    ring
  simp_rw [ht]
  rw [whiteStar_norm_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hs, mul_zero, add_zero,
    simplex_parseval, frame_scalar_weight d hd c hc, frame_transverse_weight d hd c hc]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  field_simp [hd0, hd1]
  ring

end GeneralizedBulk.Entropy.Channel
