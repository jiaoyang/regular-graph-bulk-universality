import BourgadeHuang.UniformResolventMoments
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Factorial moment growth from the balanced loop equations

The adjacent even-moment recurrence retains more information than the earlier
uniform-moment proof. Its constants grow linearly in the moment order. This
permits factorial moment bounds for limiting resolvent laws and exponential
integrability. The eventual size threshold is allowed to depend on the order;
no uniform-in-order estimate for every finite N is asserted.
-/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter

namespace BourgadeHuang

theorem norm_loopIntegrand_remainder_adjacent {N : ℕ} (β : Beta) (x : Fin N → ℝ)
    (center : ℝ) (r : ℕ) {w : ℂ} (hw : 0 < w.im) :
    ‖loopIntegrand β x center w (momentAux r w) -
        ((‖microscopicResolvent x center w‖ ^ (2 * r + 4) : ℝ) : ℂ)‖ ≤
      (1 / w.im) * ‖microscopicResolvent x center w‖ ^ (2 * r + 3) +
        (1 + 2 * (r + (r + 2) : ℕ) / w.im ^ 2 : ℝ) *
          ‖microscopicResolvent x center w‖ ^ (2 * r + 2) := by
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

/-- Young's inequality preserves the neighboring even moment. -/
theorem norm_loopIntegrand_remainder_half_leading {N : ℕ} (β : Beta)
    (x : Fin N → ℝ) (center : ℝ) (r : ℕ) {w : ℂ} (hw : 0 < w.im) :
    ‖loopIntegrand β x center w (momentAux r w) -
        ((‖microscopicResolvent x center w‖ ^ (2 * r + 4) : ℝ) : ℂ)‖ ≤
      (1 / 2 : ℝ) * ‖microscopicResolvent x center w‖ ^ (2 * r + 4) +
        (1 + (2 * (r + (r + 2) : ℕ) + 1 / 2) / w.im ^ 2 : ℝ) *
          ‖microscopicResolvent x center w‖ ^ (2 * r + 2) := by
  apply (norm_loopIntegrand_remainder_adjacent β x center r hw).trans
  let t := ‖microscopicResolvent x center w‖
  have hy : (1 / w.im) * t ≤ (1 / 2 : ℝ) * t ^ 2 + (1 / 2) / w.im ^ 2 := by
    calc
      _ ≤ (1 / 2 : ℝ) * t ^ 2 + (1 / 2) * (w.im⁻¹) ^ 2 := by
        rw [one_div]
        nlinarith [sq_nonneg (t - w.im⁻¹)]
      _ = _ := by simp only [inv_pow, div_eq_mul_inv]
  have hp := mul_le_mul_of_nonneg_right hy
    (pow_nonneg (norm_nonneg (microscopicResolvent x center w)) (2 * r + 2))
  dsimp only [t] at hp
  have he3 : 2 * r + 3 = (2 * r + 2) + 1 := by omega
  have he4 : 2 * r + 4 = (2 * r + 2) + 2 := by omega
  simp only [he3, he4, pow_add, pow_one] at hp ⊢
  simp only [div_eq_mul_inv] at hp ⊢
  nlinarith [hp]

/-- Integration of the half-leading remainder gives a two-step moment recurrence. -/
theorem integral_even_moment_recurrence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (F : Ω → ℂ)
    (hX : ∀ ω, 0 ≤ X ω) (n : ℕ) {C A : ℝ}
    (hn : Integrable (fun ω => X ω ^ n) μ)
    (hn2 : Integrable (fun ω => X ω ^ (n + 2)) μ)
    (hF : Integrable F μ) (hsmall : ‖∫ ω, F ω ∂μ‖ ≤ A)
    (hrem : ∀ ω, ‖F ω - ((X ω ^ (n + 2) : ℝ) : ℂ)‖ ≤
      (1 / 2 : ℝ) * X ω ^ (n + 2) + C * X ω ^ n) :
    (∫ ω, X ω ^ (n + 2) ∂μ) ≤ 2 * A + 2 * C * ∫ ω, X ω ^ n ∂μ := by
  let R : Ω → ℂ := fun ω => F ω - (X ω ^ (n + 2) : ℝ)
  have hR : Integrable R μ := hF.sub hn2.ofReal
  have hid : (∫ ω, F ω ∂μ) - (∫ ω, R ω ∂μ) =
      ((∫ ω, X ω ^ (n + 2) ∂μ : ℝ) : ℂ) := by
    have hh : (∫ ω, R ω ∂μ) = (∫ ω, F ω ∂μ) -
        ((∫ ω, X ω ^ (n + 2) ∂μ : ℝ) : ℂ) := by
      change (∫ ω, F ω - ((X ω ^ (n + 2) : ℝ) : ℂ) ∂μ) = _
      calc
        _ = (∫ ω, F ω ∂μ) - ∫ ω, ((X ω ^ (n + 2) : ℝ) : ℂ) ∂μ :=
          integral_sub hF hn2.ofReal
        _ = _ := by rw [integral_complex_ofReal]
    rw [hh]
    ring
  have hm : (∫ ω, X ω ^ (n + 2) ∂μ) ≤
      A + (1 / 2 : ℝ) * ∫ ω, X ω ^ (n + 2) ∂μ + C * ∫ ω, X ω ^ n ∂μ := by
    calc
      (∫ ω, X ω ^ (n + 2) ∂μ) = ‖(∫ ω, F ω ∂μ) - (∫ ω, R ω ∂μ)‖ := by
        rw [hid, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        exact integral_nonneg fun ω => pow_nonneg (hX ω) _
      _ ≤ ‖∫ ω, F ω ∂μ‖ + ‖∫ ω, R ω ∂μ‖ := norm_sub_le _ _
      _ ≤ A + ∫ ω, ‖R ω‖ ∂μ := add_le_add hsmall (norm_integral_le_integral_norm _)
      _ ≤ A + ∫ ω, (1 / 2 : ℝ) * X ω ^ (n + 2) + C * X ω ^ n ∂μ := by
        apply add_le_add_left
        exact integral_mono hR.norm ((hn2.const_mul _).add (hn.const_mul _)) hrem
      _ = _ := by
        rw [integral_add (hn2.const_mul _) (hn.const_mul _)]
        simp only [integral_const_mul]
        ring
  linarith

/-- The adjacent moment inequality obtained from the actual mixed hierarchy. -/
theorem eventually_adjacent_even_moment_bound_of_hierarchy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (β : Beta) (x : (N : ℕ) → Ω → Fin N → ℝ) (center : ℝ)
    (hx : ∀ N i, Measurable (fun ω => x N ω i))
    (h : ApproximateHierarchy μ β x center) {w : ℂ} (hw : 0 < w.im) (r : ℕ) :
    ∀ᶠ N in atTop,
      (∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ (2 * r + 4) ∂μ) ≤
      2 + (2 + (8 * r + 9 : ℝ) / w.im ^ 2) *
        (∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ (2 * r + 2) ∂μ) := by
  let K : Set ℂ := {w, star w}
  have hK : IsCompact K := Set.Finite.isCompact (Set.toFinite _)
  have hKoff : ∀ z ∈ K, z.im ≠ 0 := by
    intro z hz
    rcases hz with rfl | hz
    · exact ne_of_gt hw
    · have hz' : z = star w := Set.mem_singleton_iff.mp hz
      rw [hz']
      simpa using ne_of_gt hw
  have haux : ∀ a, momentAux r w a ∈ K := by
    intro a
    rcases momentAux_eq_or r w a with ha | ha <;> simp [ha, K]
  have hh := hierarchy_vanishing μ β x center h (r + (r + 2)) K hK hKoff 1
    (by norm_num)
  filter_upwards [hh] with N hN
  have hm (j : ℕ) := integrable_microscopicResolvent_norm_pow
    (μ := μ) (hx N) center (ne_of_gt hw) j
  have hloop := integrable_loopIntegrand (μ := μ) (hx N) β center (ne_of_gt hw)
    (momentAux r w) (fun a => hKoff _ (haux a))
  have hsmall := (hN w (by simp [K]) (momentAux r w) haux).le
  have habs := integral_even_moment_recurrence μ
    (fun ω => ‖microscopicResolvent (x N ω) center w‖)
    (fun ω => loopIntegrand β (x N ω) center w (momentAux r w))
    (fun _ => norm_nonneg _) (2 * r + 2) (hm _) (hm _) hloop hsmall
    (fun ω => by
      convert norm_loopIntegrand_remainder_half_leading β (x N ω) center r hw using 1)
  convert habs using 1
  push_cast
  ring

/-- The same exponential scale controls every even moment, with an order-dependent
size threshold. In particular these bounds can pass to a limiting law order by order. -/
theorem eventually_factorial_resolvent_moments_of_hierarchy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (β : Beta) (x : (N : ℕ) → Ω → Fin N → ℝ) (center : ℝ)
    (hx : ∀ N i, Measurable (fun ω => x N ω i))
    (h : ApproximateHierarchy μ β x center) {w : ℂ} (hw : 0 < w.im) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q : ℕ, ∀ᶠ N in atTop,
      (∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ (2 * q) ∂μ) ≤
        C ^ q * (q.factorial : ℝ) := by
  obtain ⟨B, hB⟩ := uniform_resolvent_moments_of_hierarchy μ β x center hx h
    {w} isCompact_singleton (by intro z hz; simpa only [Set.mem_singleton_iff.mp hz] using ne_of_gt hw) 2
  let D : ℝ := 4 + 9 / w.im ^ 2
  let C : ℝ := max 1 (max B D)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  have hBC : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hDC : D ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hsucc : ∀ r : ℕ, ∀ᶠ N in atTop,
      (∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ (2 * r + 2) ∂μ) ≤
        C ^ (r + 1) * ((r + 1).factorial : ℝ) := by
    intro r
    induction r with
    | zero =>
      exact Filter.Eventually.of_forall fun N => by
        simpa using (hB N w (Set.mem_singleton w)).trans hBC
    | succ r ih =>
      filter_upwards [ih,
        eventually_adjacent_even_moment_bound_of_hierarchy μ β x center hx h hw r] with N hprev hnext
      let A : ℝ := C ^ (r + 1) * ((r + 1).factorial : ℝ)
      have hA1 : 1 ≤ A := by
        exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1)
          (by exact_mod_cast Nat.factorial_pos (r + 1))
      have hcoef : 0 ≤ 2 + (8 * r + 9 : ℝ) / w.im ^ 2 := by positivity
      have hpoly : 4 + (8 * r + 9 : ℝ) / w.im ^ 2 ≤ C * (r + 2) := by
        have hrat : 0 ≤ 1 / w.im ^ 2 := by positivity
        have hDD : 4 + (8 * r + 9 : ℝ) / w.im ^ 2 ≤ D * (r + 2) := by
          dsimp [D]
          simp only [div_eq_mul_inv] at hrat ⊢
          nlinarith [(show (0 : ℝ) ≤ r by positivity)]
        exact hDD.trans (mul_le_mul_of_nonneg_right hDC (by positivity))
      calc
        (∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ (2 * (r + 1) + 2) ∂μ) ≤
            2 + (2 + (8 * r + 9 : ℝ) / w.im ^ 2) * A := by
          convert hnext.trans (add_le_add_left
            (mul_le_mul_of_nonneg_left hprev hcoef) 2) using 1
        _ ≤ (4 + (8 * r + 9 : ℝ) / w.im ^ 2) * A := by nlinarith
        _ ≤ (C * (r + 2)) * A := mul_le_mul_of_nonneg_right hpoly (by linarith)
        _ = C ^ (r + 1 + 1) * (((r + 1 + 1).factorial : ℕ) : ℝ) := by
          simp only [A, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
          ring
  refine ⟨C, hC1, ?_⟩
  intro q
  cases q with
  | zero => exact Filter.Eventually.of_forall fun N => by simp
  | succ r => simpa [Nat.mul_add] using hsucc r


/-- Factorial even-moment growth gives a genuine exponential-square moment. -/
theorem integrable_exp_sq_of_factorial_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : AEStronglyMeasurable X μ) {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t)
    (htC : t * C < 1)
    (hm : ∀ q : ℕ, Integrable (fun ω => X ω ^ (2 * q)) μ)
    (hbound : ∀ q : ℕ, (∫ ω, X ω ^ (2 * q) ∂μ) ≤ C ^ q * (q.factorial : ℝ)) :
    Integrable (fun ω => Real.exp (t * X ω ^ 2)) μ := by
  let f : ℕ → Ω → ℝ := fun q ω => (t * X ω ^ 2) ^ q / (q.factorial : ℝ)
  have hf0 (q : ℕ) (ω : Ω) : 0 ≤ f q ω := by
    dsimp [f]
    positivity
  have hfeq (q : ℕ) : f q = fun ω => (t ^ q / (q.factorial : ℝ)) * X ω ^ (2 * q) := by
    funext ω
    simp only [f, mul_pow, pow_mul]
    ring
  have hfi (q : ℕ) : Integrable (f q) μ := by
    rw [hfeq]
    exact (hm q).const_mul _
  have hmean (q : ℕ) : (∫ ω, f q ω ∂μ) ≤ (t * C) ^ q := by
    rw [hfeq, integral_const_mul]
    calc
      _ ≤ (t ^ q / (q.factorial : ℝ)) * (C ^ q * (q.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hbound q) (by positivity)
      _ = _ := by
        have hfac : (q.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
        field_simp
        ring
  have hsum : Summable (fun q => ∫ ω, f q ω ∂μ) :=
    (summable_geometric_of_lt_one (mul_nonneg ht hC) htC).of_nonneg_of_le
      (fun q => integral_nonneg (hf0 q)) hmean
  have hseries (ω : Ω) : HasSum (fun q => f q ω) (Real.exp (t * X ω ^ 2)) := by
    simpa only [f, Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp ℝ (t * X ω ^ 2)
  refine ⟨Real.continuous_exp.comp_aestronglyMeasurable ((hX.pow 2).const_mul t), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))]
  have hexp : (fun ω => ENNReal.ofReal (Real.exp (t * X ω ^ 2))) =
      fun ω => ∑' q, ENNReal.ofReal (f q ω) := by
    funext ω
    rw [← (hseries ω).tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg (fun q => hf0 q ω) (hseries ω).summable
  rw [hexp, lintegral_tsum (fun q => (hfi q).aemeasurable.ennreal_ofReal)]
  simp_rw [← ofReal_integral_eq_lintegral_ofReal (hfi _) (Filter.Eventually.of_forall (hf0 _))]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => integral_nonneg (hf0 q)) hsum]
  exact ENNReal.ofReal_lt_top

/-- Moment convergence transfers the factorial constants without making the
finite-size threshold independent of the moment order. -/
theorem factorial_moments_of_tendsto_moments
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ω')
    (β : Beta) (x : (N : ℕ) → Ω → Fin N → ℝ) (center : ℝ)
    (hx : ∀ N i, Measurable (fun ω => x N ω i))
    (h : ApproximateHierarchy μ β x center) {w : ℂ} (hw : 0 < w.im)
    (X : Ω' → ℝ)
    (hlim : ∀ q : ℕ, Tendsto
      (fun N => ∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ (2 * q) ∂μ)
      atTop (𝓝 (∫ ω, X ω ^ (2 * q) ∂ν))) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q : ℕ,
      (∫ ω, X ω ^ (2 * q) ∂ν) ≤ C ^ q * (q.factorial : ℝ) := by
  obtain ⟨C, hC, hb⟩ := eventually_factorial_resolvent_moments_of_hierarchy
    μ β x center hx h hw
  exact ⟨C, hC, fun q => le_of_tendsto (hlim q) (hb q)⟩

/-- Any limiting law with convergent even moments has a nonzero exponential-square
radius, deduced from the loop hierarchy rather than assumed. -/
theorem exists_integrable_exp_sq_of_hierarchy_moment_limit
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ω')
    (β : Beta) (x : (N : ℕ) → Ω → Fin N → ℝ) (center : ℝ)
    (hx : ∀ N i, Measurable (fun ω => x N ω i))
    (h : ApproximateHierarchy μ β x center) {w : ℂ} (hw : 0 < w.im)
    (X : Ω' → ℝ) (hX : AEStronglyMeasurable X ν)
    (hm : ∀ q : ℕ, Integrable (fun ω => X ω ^ (2 * q)) ν)
    (hlim : ∀ q : ℕ, Tendsto
      (fun N => ∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ (2 * q) ∂μ)
      atTop (𝓝 (∫ ω, X ω ^ (2 * q) ∂ν))) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun ω => Real.exp (t * X ω ^ 2)) ν := by
  obtain ⟨C, hC, hb⟩ := factorial_moments_of_tendsto_moments μ ν β x center hx h hw X hlim
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨(2 * C)⁻¹, by positivity, ?_⟩
  apply integrable_exp_sq_of_factorial_moments ν X hX hCpos.le (by positivity) _ hm hb
  have he : (2 * C)⁻¹ * C = (1 / 2 : ℝ) := by field_simp; ring
  rw [he]
  norm_num


end BourgadeHuang
