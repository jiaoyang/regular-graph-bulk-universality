import GeneralizedBulk.Gaussian.Series
import Mathlib.Probability.Integration

/-!
# Moments of independent centered square-summable series

Finite even moments are controlled by a binomial recursion. The linear term
vanishes by centering, and the remaining single-mark terms are controlled by
the squared coefficient. This avoids assuming Gaussian hypercontractivity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace GeneralizedBulk.Gaussian
namespace Moments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def partialSum (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range n, Y i ω

theorem measurable_partialSum (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    Measurable (partialSum Y n) := by
  unfold partialSum
  exact Finset.measurable_sum _ (fun i hi => hY i)

omit [IsProbabilityMeasure μ] in
theorem memLp_partialSum (Y : ℕ → Ω → ℝ)
    (hY : ∀ i k : ℕ, MemLp (Y i) (k : ENNReal) μ) (n k : ℕ) :
    MemLp (partialSum Y n) (k : ENNReal) μ := by
  exact memLp_finset_sum _ (fun i hi => hY i k)

theorem integrable_pow (f : Ω → ℝ) (hf : Measurable f)
    (hm : ∀ k : ℕ, MemLp f (k : ENNReal) μ) (k : ℕ) :
    Integrable (fun ω => f ω ^ k) μ := by
  by_cases hk : k = 0
  · subst k
    simp
  · apply (hm k).integrable_norm_pow hk |>.mono' ((hf.pow_const k).aestronglyMeasurable)
    filter_upwards [] with ω
    simp only [norm_pow]
    exact le_rfl

/-- A lower power is controlled by one plus any higher power of the norm. -/
theorem abs_pow_le_one_add (x : ℝ) {m k : ℕ} (hmk : m ≤ k) :
    |x| ^ m ≤ 1 + |x| ^ k := by
  by_cases hx : |x| ≤ 1
  · have h := pow_le_one₀ (abs_nonneg x) hx (n := m)
    linarith [pow_nonneg (abs_nonneg x) k]
  · have h := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hx)) hmk
    linarith

/-- Independence gives the literal finite moment recursion. All integrals are
integrable before their algebraic expansion is used. -/
theorem integral_partialSum_pow_succ (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hm : ∀ i k : ℕ, MemLp (Y i) (k : ENNReal) μ)
    (hind : iIndepFun Y μ) (n r : ℕ) :
    (∫ ω, partialSum Y (n + 1) ω ^ r ∂μ) =
      ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        (∫ ω, partialSum Y n ω ^ (r - k) ∂μ) * (∫ ω, Y n ω ^ k ∂μ) := by
  have hpart : IndepFun (partialSum Y n) (Y n) μ := by
    have h := hind.indepFun_sum_range_succ hY n
    convert h using 1
    funext ω
    simp [partialSum, Finset.sum_apply]
  have hiS (k : ℕ) : Integrable (fun ω => partialSum Y n ω ^ k) μ :=
    integrable_pow _ (measurable_partialSum Y hY n) (memLp_partialSum Y hm n) k
  have hiY (k : ℕ) : Integrable (fun ω => Y n ω ^ k) μ := integrable_pow _ (hY n) (hm n) k
  have hpow (k : ℕ) : IndepFun (fun ω => Y n ω ^ k)
      (fun ω => partialSum Y n ω ^ (r - k)) μ :=
    hpart.symm.comp (measurable_id.pow_const k) (measurable_id.pow_const (r - k))
  have hprod (k : ℕ) : Integrable
      (fun ω => Y n ω ^ k * partialSum Y n ω ^ (r - k) * (r.choose k : ℝ)) μ :=
    ((hpow k).integrable_mul (hiY k) (hiS (r - k))).mul_const _
  have hrec (ω : Ω) : partialSum Y (n + 1) ω ^ r =
      ∑ k ∈ Finset.range (r + 1), Y n ω ^ k * partialSum Y n ω ^ (r - k) * (r.choose k : ℝ) := by
    rw [partialSum, Finset.sum_range_succ]
    simpa only [partialSum, add_comm] using add_pow (Y n ω) (partialSum Y n ω) r
  simp_rw [hrec]
  rw [integral_finset_sum _ (fun k hk => hprod k)]
  apply Finset.sum_congr rfl
  intro k hk
  have heq := (hpow k).integral_mul_of_integrable (hiY k) (hiS (r - k))
  change (∫ ω, Y n ω ^ k * partialSum Y n ω ^ (r - k) ∂μ) =
    (∫ ω, Y n ω ^ k ∂μ) * (∫ ω, partialSum Y n ω ^ (r - k) ∂μ) at heq
  rw [integral_mul_const, heq]
  ring

/-- Any lower signed moment is controlled by a higher absolute moment. -/
theorem abs_integral_pow_le_of_even_bound (f : Ω → ℝ) (hf : Measurable f)
    (hm : ∀ k : ℕ, MemLp f (k : ENNReal) μ) {m k : ℕ} (hmk : m ≤ k)
    (C : ℝ) (hC : (∫ ω, |f ω| ^ k ∂μ) ≤ C) :
    |∫ ω, f ω ^ m ∂μ| ≤ 1 + C := by
  have him : Integrable (fun ω => |f ω| ^ m) μ := by
    simpa only [Real.norm_eq_abs, norm_pow] using (integrable_pow f hf hm m).norm
  have hik : Integrable (fun ω => |f ω| ^ k) μ := by
    simpa only [Real.norm_eq_abs, norm_pow] using (integrable_pow f hf hm k).norm
  calc
    _ ≤ ∫ ω, |f ω| ^ m ∂μ := by
      simpa only [Real.norm_eq_abs, norm_pow] using norm_integral_le_integral_norm (fun ω => f ω ^ m)
    _ ≤ ∫ ω, 1 + |f ω| ^ k ∂μ :=
      integral_mono him ((integrable_const _).add hik) (fun ω => abs_pow_le_one_add (f ω) hmk)
    _ = 1 + ∫ ω, |f ω| ^ k ∂μ := by
      rw [integral_add (integrable_const _) hik]
      simp
    _ ≤ _ := by linarith

/-- The centered binomial step is quadratic in the coefficient variance. -/
theorem centered_even_step (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hm : ∀ i k : ℕ, MemLp (Y i) (k : ENNReal) μ)
    (hind : iIndepFun Y μ) (hcenter : ∀ i, (∫ ω, Y i ω ∂μ) = 0)
    (n r : ℕ) (hr : 2 ≤ r) (v M L : ℝ) (hv : 0 ≤ v) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hlower : ∀ m, m ≤ r - 2 → |∫ ω, partialSum Y n ω ^ m ∂μ| ≤ L)
    (hmark : ∀ k, 2 ≤ k → k ≤ r → |∫ ω, Y n ω ^ k ∂μ| ≤ v * M) :
    (∫ ω, partialSum Y (n + 1) ω ^ r ∂μ) ≤
      (∫ ω, partialSum Y n ω ^ r ∂μ) +
        (((r + 1 : ℕ) : ℝ) * (2 : ℝ) ^ r * L * M) * v := by
  let K := (2 : ℝ) ^ r * L * M
  have hK : 0 ≤ K := by dsimp [K]; positivity
  rw [integral_partialSum_pow_succ Y hY hm hind n r]
  have hterm (k : ℕ) (hk : k ∈ Finset.range (r + 1)) :
      (r.choose k : ℝ) * (∫ ω, partialSum Y n ω ^ (r - k) ∂μ) *
        (∫ ω, Y n ω ^ k ∂μ) ≤
      (if k = 0 then (∫ ω, partialSum Y n ω ^ r ∂μ) else 0) + K * v := by
    by_cases hk0 : k = 0
    · subst k
      simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, pow_zero,
        integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one,
        one_mul, ↓reduceIte]
      exact le_add_of_nonneg_right (mul_nonneg hK hv)
    · by_cases hk1 : k = 1
      · subst k
        simp only [pow_one, hcenter, mul_zero, if_false, Nat.one_ne_zero]
        simpa only [zero_add] using mul_nonneg hK hv
      · have hk2 : 2 ≤ k := by omega
        have hkr : k ≤ r := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
        have hl := hlower (r - k) (by omega)
        have hmom := hmark k hk2 hkr
        have hchoose : (r.choose k : ℝ) ≤ (2 : ℝ) ^ r := by
          exact_mod_cast (Nat.choose_le_two_pow r k (by omega)).le
        have hchoose0 : 0 ≤ (r.choose k : ℝ) := by positivity
        rw [if_neg hk0, zero_add]
        calc
          _ ≤ |(r.choose k : ℝ) * (∫ ω, partialSum Y n ω ^ (r - k) ∂μ) *
              (∫ ω, Y n ω ^ k ∂μ)| := le_abs_self _
          _ = ((r.choose k : ℝ) * |∫ ω, partialSum Y n ω ^ (r - k) ∂μ|) *
              |∫ ω, Y n ω ^ k ∂μ| := by rw [abs_mul, abs_mul, abs_of_nonneg hchoose0]
          _ ≤ ((2 : ℝ) ^ r * L) * (v * M) :=
            mul_le_mul (mul_le_mul hchoose hl (abs_nonneg _) (by positivity)) hmom
              (abs_nonneg _) (mul_nonneg (by positivity) hL)
          _ = K * v := by dsimp [K]; ring
  calc
    _ ≤ ∑ k ∈ Finset.range (r + 1),
        ((if k = 0 then (∫ ω, partialSum Y n ω ^ r ∂μ) else 0) + K * v) :=
      Finset.sum_le_sum hterm
    _ = (∫ ω, partialSum Y n ω ^ r ∂μ) + (((r + 1 : ℕ) : ℝ) * (2 : ℝ) ^ r * L * M) * v := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, ↓reduceIte,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [K]
      ring

/-- Uniform even moments of centered independent finite sums follow from
quadratically weighted single-mark moments. No infinite-series moment bound is
assumed. For normalized coefficients the variance weights are `v n = a n²`. -/
theorem uniform_even_moments (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hm : ∀ i k : ℕ, MemLp (Y i) (k : ENNReal) μ)
    (hind : iIndepFun Y μ) (hcenter : ∀ i, (∫ ω, Y i ω ∂μ) = 0)
    (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (hvariance : ∀ n, ∑ i ∈ Finset.range n, v i ≤ 1)
    (hmark : ∀ q : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ 2 * q →
      |∫ ω, Y n ω ^ k ∂μ| ≤ v n * M) :
    ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      (∫ ω, |partialSum Y n ω| ^ (2 * q) ∂μ) ≤ C := by
  intro q
  induction q with
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      intro n
      simp
  | succ q ih =>
      obtain ⟨C, hC, hprev⟩ := ih
      obtain ⟨M, hM, hmark⟩ := hmark (q + 1)
      let r : ℕ := 2 * (q + 1)
      let K : ℝ := ((r + 1 : ℕ) : ℝ) * (2 : ℝ) ^ r * (1 + C) * M
      have hK : 0 ≤ K := by dsimp [K]; positivity
      have hrawprev (n : ℕ) : (∫ ω, partialSum Y n ω ^ (2 * q) ∂μ) ≤ C := by
        simpa only [pow_mul, sq_abs] using hprev n
      have hstep (n : ℕ) : (∫ ω, partialSum Y (n + 1) ω ^ r ∂μ) ≤
          (∫ ω, partialSum Y n ω ^ r ∂μ) + K * v n := by
        apply centered_even_step Y hY hm hind hcenter n r (by dsimp [r]; omega)
          (v n) M (1 + C) (hv n) hM (by linarith)
        · intro m hmr
          apply abs_integral_pow_le_of_even_bound _ (measurable_partialSum Y hY n)
            (memLp_partialSum Y hm n) (show m ≤ 2 * q by dsimp [r] at hmr; omega) C
          exact hprev n
        · intro k hk2 hkr
          exact hmark n k hk2 hkr
      have hacc (n : ℕ) : (∫ ω, partialSum Y n ω ^ r ∂μ) ≤
          K * ∑ i ∈ Finset.range n, v i := by
        induction n with
        | zero => simp [partialSum, show r ≠ 0 by dsimp [r]; omega]
        | succ n ihn =>
          calc
            _ ≤ (∫ ω, partialSum Y n ω ^ r ∂μ) + K * v n := hstep n
            _ ≤ (K * ∑ i ∈ Finset.range n, v i) + K * v n := add_le_add_right ihn _
            _ = _ := by rw [Finset.sum_range_succ]; ring
      refine ⟨K, hK, ?_⟩
      intro n
      have h := (hacc n).trans (mul_le_mul_of_nonneg_left (hvariance n) hK)
      simpa only [r, mul_one, pow_mul, sq_abs] using h

/-- The deterministic even-moment constants depend only on the one-mark
moment bounds, not on the number of particles or their coefficients. -/
def evenMomentConstant (M : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | q + 1 => ((2 * (q + 1) + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (q + 1)) *
      (1 + evenMomentConstant M q) * M (q + 1)

theorem evenMomentConstant_nonneg (M : ℕ → ℝ) (hM : ∀ q, 0 ≤ M q) :
    ∀ q, 0 ≤ evenMomentConstant M q := by
  intro q
  induction q with
  | zero => norm_num [evenMomentConstant]
  | succ q ih =>
      have hMq := hM (q + 1)
      simp only [evenMomentConstant]
      positivity

/-- Explicit uniform finite-sum bound, with constants independent of the
coefficient sequence. This is suitable for integration over a random scalar
state after normalizing the coefficient square-sum. -/
theorem even_moment_bound (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hm : ∀ i k : ℕ, MemLp (Y i) (k : ENNReal) μ)
    (hind : iIndepFun Y μ) (hcenter : ∀ i, (∫ ω, Y i ω ∂μ) = 0)
    (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (hvariance : ∀ n, ∑ i ∈ Finset.range n, v i ≤ 1)
    (M : ℕ → ℝ) (hM : ∀ q, 0 ≤ M q)
    (hmark : ∀ q n k : ℕ, 2 ≤ k → k ≤ 2 * q →
      |∫ ω, Y n ω ^ k ∂μ| ≤ v n * M q) :
    ∀ q n : ℕ, (∫ ω, |partialSum Y n ω| ^ (2 * q) ∂μ) ≤ evenMomentConstant M q := by
  intro q
  induction q with
  | zero => intro n; simp [evenMomentConstant]
  | succ q ih =>
      let r : ℕ := 2 * (q + 1)
      let K : ℝ := evenMomentConstant M (q + 1)
      have hC := evenMomentConstant_nonneg M hM q
      have hK : 0 ≤ K := evenMomentConstant_nonneg M hM (q + 1)
      have hstep (n : ℕ) : (∫ ω, partialSum Y (n + 1) ω ^ r ∂μ) ≤
          (∫ ω, partialSum Y n ω ^ r ∂μ) + K * v n := by
        apply centered_even_step Y hY hm hind hcenter n r (by dsimp [r]; omega)
          (v n) (M (q + 1)) (1 + evenMomentConstant M q) (hv n) (hM _) (by linarith)
        · intro m hmr
          exact abs_integral_pow_le_of_even_bound _ (measurable_partialSum Y hY n)
            (memLp_partialSum Y hm n) (show m ≤ 2 * q by dsimp [r] at hmr; omega)
            (evenMomentConstant M q) (ih n)
        · intro k hk2 hkr
          exact hmark (q + 1) n k hk2 hkr
      have hacc (n : ℕ) : (∫ ω, partialSum Y n ω ^ r ∂μ) ≤
          K * ∑ i ∈ Finset.range n, v i := by
        induction n with
        | zero => simp [partialSum, show r ≠ 0 by dsimp [r]; omega]
        | succ n ihn =>
          calc
            _ ≤ (∫ ω, partialSum Y n ω ^ r ∂μ) + K * v n := hstep n
            _ ≤ (K * ∑ i ∈ Finset.range n, v i) + K * v n := add_le_add_right ihn _
            _ = _ := by rw [Finset.sum_range_succ]; ring
      intro n
      have h := (hacc n).trans (mul_le_mul_of_nonneg_left (hvariance n) hK)
      simpa only [r, K, mul_one, pow_mul, sq_abs] using h

/-- Normalized square-summable coefficients give uniform even moments from
ordinary one-mark moments. The constant is independent of the coefficients. -/
theorem normalized_weighted_even_moment_bound (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hm : ∀ i k : ℕ, MemLp (Y i) (k : ENNReal) μ)
    (hind : iIndepFun Y μ) (hcenter : ∀ i, (∫ ω, Y i ω ∂μ) = 0)
    (a : ℕ → ℝ) (ha : ∀ n, ∑ i ∈ Finset.range n, a i ^ 2 ≤ 1)
    (M : ℕ → ℝ) (hM : ∀ q, 0 ≤ M q)
    (hmark : ∀ q n k : ℕ, 2 ≤ k → k ≤ 2 * q → |∫ ω, Y n ω ^ k ∂μ| ≤ M q) :
    ∀ q n : ℕ,
      (∫ ω, |∑ i ∈ Finset.range n, a i * Y i ω| ^ (2 * q) ∂μ) ≤ evenMomentConstant M q := by
  let W : ℕ → Ω → ℝ := fun n ω => a n * Y n ω
  have hW (n : ℕ) : Measurable (W n) := (hY n).const_mul _
  have hmW (n k : ℕ) : MemLp (W n) (k : ENNReal) μ := (hm n k).const_mul _
  have hiW : iIndepFun W μ :=
    hind.comp (fun n x => a n * x) (fun n => measurable_const.mul measurable_id)
  have hcW (n : ℕ) : (∫ ω, W n ω ∂μ) = 0 := by
    dsimp [W]
    rw [integral_const_mul, hcenter, mul_zero]
  have ha2 (n : ℕ) : a n ^ 2 ≤ 1 := by
    have hsingle : a n ^ 2 ≤ ∑ i ∈ Finset.range (n + 1), a i ^ 2 :=
      Finset.single_le_sum (fun i hi => sq_nonneg _) (by simp)
    exact hsingle.trans (ha _)
  have hmk (q n k : ℕ) (hk2 : 2 ≤ k) (hkq : k ≤ 2 * q) :
      |∫ ω, W n ω ^ k ∂μ| ≤ a n ^ 2 * M q := by
    have hpow : |a n| ^ k ≤ a n ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_of_le_one (abs_nonneg (a n))
        ((sq_le_one_iff_abs_le_one (a n)).mp (ha2 n)) hk2
    have heq : (fun ω => W n ω ^ k) = (fun ω => a n ^ k * Y n ω ^ k) := by
      funext ω
      dsimp [W]
      rw [mul_pow]
    rw [heq, integral_const_mul, abs_mul, abs_pow]
    exact mul_le_mul hpow (hmark q n k hk2 hkq) (abs_nonneg _) (sq_nonneg _)
  exact even_moment_bound W hW hmW hiW hcW (fun n => a n ^ 2)
    (fun n => sq_nonneg _) ha M hM hmk

/-- Unnormalized finite sums have a polynomial moment bound in their total
coefficient variance. This is the form used for random scalar states. -/
theorem weighted_even_moment_bound (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hm : ∀ i k : ℕ, MemLp (Y i) (k : ENNReal) μ)
    (hind : iIndepFun Y μ) (hcenter : ∀ i, (∫ ω, Y i ω ∂μ) = 0)
    (a : ℕ → ℝ) (B : ℝ) (hB : 0 < B)
    (ha : ∀ n, ∑ i ∈ Finset.range n, a i ^ 2 ≤ B)
    (M : ℕ → ℝ) (hM : ∀ q, 0 ≤ M q)
    (hmark : ∀ q n k : ℕ, 2 ≤ k → k ≤ 2 * q → |∫ ω, Y n ω ^ k ∂μ| ≤ M q) :
    ∀ q n : ℕ,
      (∫ ω, |∑ i ∈ Finset.range n, a i * Y i ω| ^ (2 * q) ∂μ) ≤
        B ^ q * evenMomentConstant M q := by
  let b : ℕ → ℝ := fun i => a i / Real.sqrt B
  have hsqrt : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hB)
  have hb (n : ℕ) : ∑ i ∈ Finset.range n, b i ^ 2 ≤ 1 := by
    dsimp [b]
    simp_rw [div_pow]
    rw [← Finset.sum_div, Real.sq_sqrt hB.le]
    exact (div_le_one hB).mpr (ha n)
  have hnorm := normalized_weighted_even_moment_bound Y hY hm hind hcenter b hb M hM hmark
  intro q n
  have hsum (ω : Ω) : (∑ i ∈ Finset.range n, a i * Y i ω) =
      Real.sqrt B * (∑ i ∈ Finset.range n, b i * Y i ω) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [b]
    field_simp
  have hpow : Real.sqrt B ^ (2 * q) = B ^ q := by
    rw [pow_mul, Real.sq_sqrt hB.le]
  simp_rw [hsum, abs_mul, abs_of_nonneg (Real.sqrt_nonneg B), mul_pow]
  rw [integral_const_mul, hpow]
  exact mul_le_mul_of_nonneg_left (hnorm q n) (pow_nonneg hB.le q)

/-- A coarse elementary bound reduces all complex moments to real and
imaginary component moments. -/
theorem complex_norm_pow_le (z : ℂ) (k : ℕ) :
    ‖z‖ ^ k ≤ (2 : ℝ) ^ k * (|z.re| ^ k + |z.im| ^ k) := by
  by_cases h : |z.re| ≤ |z.im|
  · have hn : ‖z‖ ≤ 2 * |z.im| := (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
    calc
      _ ≤ (2 * |z.im|) ^ k := pow_le_pow_left₀ (norm_nonneg _) hn k
      _ = (2 : ℝ) ^ k * |z.im| ^ k := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg (abs_nonneg _) k)) (by positivity)
  · have hn : ‖z‖ ≤ 2 * |z.re| := (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
    calc
      _ ≤ (2 * |z.re|) ^ k := pow_le_pow_left₀ (norm_nonneg _) hn k
      _ = (2 : ℝ) ^ k * |z.re| ^ k := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg (abs_nonneg _) k)) (by positivity)

/-- Complex finite marked sums have all even moments, with a bound polynomial
in the coefficient square-sum and independent of the particle count. -/
theorem complex_weighted_even_moment_bound (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hm : ∀ i k : ℕ, MemLp (Y i) (k : ENNReal) μ)
    (hind : iIndepFun Y μ) (hcenter : ∀ i, (∫ ω, Y i ω ∂μ) = 0)
    (a : ℕ → ℂ) (B : ℝ) (hB : 0 < B)
    (ha : ∀ n, ∑ i ∈ Finset.range n, ‖a i‖ ^ 2 ≤ B)
    (M : ℕ → ℝ) (hM : ∀ q, 0 ≤ M q)
    (hmark : ∀ q n k : ℕ, 2 ≤ k → k ≤ 2 * q → |∫ ω, Y n ω ^ k ∂μ| ≤ M q) :
    ∀ q n : ℕ,
      (∫ ω, ‖∑ i ∈ Finset.range n, a i * (Y i ω : ℂ)‖ ^ (2 * q) ∂μ) ≤
        (2 : ℝ) ^ (2 * q + 1) * B ^ q * evenMomentConstant M q := by
  have hare (n : ℕ) : ∑ i ∈ Finset.range n, (a i).re ^ 2 ≤ B := by
    apply le_trans (Finset.sum_le_sum (fun i hi => ?_)) (ha n)
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_nonneg (a i).im]
  have haim (n : ℕ) : ∑ i ∈ Finset.range n, (a i).im ^ 2 ≤ B := by
    apply le_trans (Finset.sum_le_sum (fun i hi => ?_)) (ha n)
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_nonneg (a i).re]
  have hre := weighted_even_moment_bound Y hY hm hind hcenter (fun i => (a i).re) B hB hare M hM hmark
  have him := weighted_even_moment_bound Y hY hm hind hcenter (fun i => (a i).im) B hB haim M hM hmark
  intro q n
  let f : Ω → ℂ := fun ω => ∑ i ∈ Finset.range n, a i * (Y i ω : ℂ)
  have hfr (ω : Ω) : (f ω).re = ∑ i ∈ Finset.range n, (a i).re * Y i ω := by
    simp [f, Complex.mul_re]
  have hfi (ω : Ω) : (f ω).im = ∑ i ∈ Finset.range n, (a i).im * Y i ω := by
    simp [f, Complex.mul_im]
  have hmem (k : ℕ) : MemLp f (k : ENNReal) μ :=
    memLp_finset_sum _ (fun i hi => ((hm i k).ofReal (K := ℂ)).const_mul (a i))
  have hi : Integrable (fun ω => ‖f ω‖ ^ (2 * q)) μ := (hmem _).integrable_norm_pow'
  have hir : Integrable (fun ω => |(f ω).re| ^ (2 * q)) μ := by
    simpa only [Real.norm_eq_abs] using (hmem _).re.integrable_norm_pow'
  have hii : Integrable (fun ω => |(f ω).im| ^ (2 * q)) μ := by
    simpa only [Real.norm_eq_abs] using (hmem _).im.integrable_norm_pow'
  calc
    _ ≤ ∫ ω, (2 : ℝ) ^ (2 * q) * (|(f ω).re| ^ (2 * q) + |(f ω).im| ^ (2 * q)) ∂μ :=
      integral_mono hi ((hir.add hii).const_mul _) (fun ω => complex_norm_pow_le (f ω) (2 * q))
    _ = (2 : ℝ) ^ (2 * q) * ((∫ ω, |(f ω).re| ^ (2 * q) ∂μ) +
        (∫ ω, |(f ω).im| ^ (2 * q) ∂μ)) := by
      rw [integral_const_mul, integral_add hir hii]
    _ ≤ (2 : ℝ) ^ (2 * q) * (B ^ q * evenMomentConstant M q + B ^ q * evenMomentConstant M q) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · simpa only [hfr] using hre q n
      · simpa only [hfi] using him q n
    _ = _ := by rw [pow_succ]; ring

omit [IsProbabilityMeasure μ] in
/-- Fatou transfers a uniform ordinary moment bound through convergence in
measure. In particular an L² limit inherits all previously bounded moments. -/
theorem moment_bound_of_tendstoInMeasure {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → Ω → E) (f : Ω → E)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hf : AEStronglyMeasurable f μ)
    (hlim : TendstoInMeasure μ F atTop f) (k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hFi : ∀ n, Integrable (fun ω => ‖F n ω‖ ^ k) μ)
    (hbound : ∀ n, (∫ ω, ‖F n ω‖ ^ k ∂μ) ≤ C) :
    Integrable (fun ω => ‖f ω‖ ^ k) μ ∧ (∫ ω, ‖f ω‖ ^ k ∂μ) ≤ C := by
  obtain ⟨ns, hns, hsub⟩ := hlim.exists_seq_tendsto_ae
  have hpow : ∀ᵐ ω ∂μ, Tendsto (fun n => ‖F (ns n) ω‖ ^ k) atTop (𝓝 (‖f ω‖ ^ k)) := by
    filter_upwards [hsub] with ω hω
    exact hω.norm.pow k
  have hFp (n : ℕ) : AEStronglyMeasurable (fun ω => ‖F (ns n) ω‖ ^ k) μ :=
    ((hF (ns n)).norm.aemeasurable.pow_const k).aestronglyMeasurable
  have hfp : AEStronglyMeasurable (fun ω => ‖f ω‖ ^ k) μ :=
    (hf.norm.aemeasurable.pow_const k).aestronglyMeasurable
  have hb (n : ℕ) : eLpNorm (fun ω => ‖F (ns n) ω‖ ^ k) 1 μ ≤ ENNReal.ofReal C := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hFi (ns n))]
    simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using ENNReal.ofReal_le_ofReal (hbound (ns n))
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 1) hFp (fun ω => ‖f ω‖ ^ k) hpow
  have hnorm : eLpNorm (fun ω => ‖f ω‖ ^ k) 1 μ ≤ ENNReal.ofReal C :=
    hfatou.trans (liminf_le_of_frequently_le' (Filter.Eventually.of_forall hb).frequently)
  have hmem : MemLp (fun ω => ‖f ω‖ ^ k) 1 μ :=
    ⟨hfp, hnorm.trans_lt ENNReal.ofReal_lt_top⟩
  have hi : Integrable (fun ω => ‖f ω‖ ^ k) μ := memLp_one_iff_integrable.mp hmem
  refine ⟨hi, ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hi] at hreal
  simpa only [Real.norm_eq_abs, abs_pow, abs_norm,
    ENNReal.toReal_ofReal (integral_nonneg (fun ω => pow_nonneg (norm_nonneg _) k)),
    ENNReal.toReal_ofReal hC] using hreal

omit [IsProbabilityMeasure μ] in
/-- Moment transfer for the actual L² random-variable limit used in the marked
series construction. The conclusion includes genuine integrability. -/
theorem moment_bound_of_L2_tendsto {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → Lp E 2 μ) (f : Lp E 2 μ) (hlim : Tendsto F atTop (𝓝 f))
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hFi : ∀ n, Integrable (fun ω => ‖F n ω‖ ^ k) μ)
    (hbound : ∀ n, (∫ ω, ‖F n ω‖ ^ k ∂μ) ≤ C) :
    Integrable (fun ω => ‖f ω‖ ^ k) μ ∧ (∫ ω, ‖f ω‖ ^ k ∂μ) ≤ C :=
  moment_bound_of_tendstoInMeasure _ _ (fun n => Lp.aestronglyMeasurable (F n))
    (Lp.aestronglyMeasurable f) (tendstoInMeasure_of_tendsto_Lp hlim) k C hC hFi hbound

end Moments
end GeneralizedBulk.Gaussian
