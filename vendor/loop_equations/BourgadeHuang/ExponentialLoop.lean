import BourgadeHuang.ExactAnchoredHierarchy
import BourgadeHuang.ExponentialObservableBounds

/-!
# Exponentially tilted loop identities

The entire exponential series can be integrated against a reconstructed law:
an exponential-square anchor moment supplies a common integrable bound. Exact
polynomial loop equations therefore imply genuine analytic generating identities.
-/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- The degree-`N-1` exponential Taylor polynomial. -/
def exponentialPartial (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, z ^ n / (n.factorial : ℂ)

theorem tendsto_exponentialPartial (z : ℂ) :
    Tendsto (fun N => exponentialPartial N z) atTop (𝓝 (Complex.exp z)) := by
  simpa only [exponentialPartial, Complex.exp_eq_exp_ℂ] using
    (NormedSpace.expSeries_div_hasSum_exp ℂ z).tendsto_sum_nat

theorem norm_exponentialPartial_le (N : ℕ) (z : ℂ) :
    ‖exponentialPartial N z‖ ≤ Real.exp ‖z‖ := by
  have hs : HasSum (fun n : ℕ => ‖z‖ ^ n / (n.factorial : ℝ)) (Real.exp ‖z‖) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp ℝ ‖z‖
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖z ^ n / (n.factorial : ℂ)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.range N, ‖z‖ ^ n / (n.factorial : ℝ) := by
      simp only [norm_div, norm_pow, Complex.norm_natCast]
    _ ≤ Real.exp ‖z‖ := by
      rw [← hs.tsum_eq]
      exact hs.summable.sum_le_tsum _ (fun n _ => by positivity)

private theorem exponentialPartial_derivative_sum (N : ℕ) (t X : ℂ) :
    (∑ n ∈ Finset.range (N + 1), (t ^ n / (n.factorial : ℂ)) * n * X ^ (n - 1)) =
      t * exponentialPartial N (t * X) := by
  induction N with
  | zero => simp [exponentialPartial]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [exponentialPartial, Finset.sum_range_succ, mul_add]
    congr 1
    have hfac : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
    have hn : (N + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel, pow_succ, mul_pow]
    field_simp
    <;> ring

private theorem exponentialPartial_loop_sum (N : ℕ) (H X J t : ℂ) :
    (∑ n ∈ Finset.range (N + 1), (t ^ n / (n.factorial : ℂ)) *
      (H * X ^ n + n * J * X ^ (n - 1))) =
      H * exponentialPartial (N + 1) (t * X) + t * J * exponentialPartial N (t * X) := by
  simp only [mul_add, Finset.sum_add_distrib]
  have hhead : (∑ n ∈ Finset.range (N + 1), (t ^ n / (n.factorial : ℂ)) * (H * X ^ n)) =
      H * exponentialPartial (N + 1) (t * X) := by
    rw [exponentialPartial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [mul_pow]
    ring
  have hder : (∑ n ∈ Finset.range (N + 1), (t ^ n / (n.factorial : ℂ)) * (n * J * X ^ (n - 1))) =
      J * (∑ n ∈ Finset.range (N + 1), (t ^ n / (n.factorial : ℂ)) * n * X ^ (n - 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hhead, hder, exponentialPartial_derivative_sum]
  ring

/-- A justified passage from all polynomial integration-by-parts identities to
an exponential identity. The domination is explicit and integrable. -/
theorem integral_exponential_identity_of_monomials
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (H X J : Ω → ℂ) (t : ℂ)
    (hH : AEStronglyMeasurable H μ) (hX : AEStronglyMeasurable X μ)
    (hJ : AEStronglyMeasurable J μ)
    (hpoly : ∀ n : ℕ, Integrable (fun ω => H ω * X ω ^ n + n * J ω * X ω ^ (n - 1)) μ ∧
      (∫ ω, H ω * X ω ^ n + n * J ω * X ω ^ (n - 1) ∂μ) = 0)
    (hdom : Integrable (fun ω => (‖H ω‖ + ‖t‖ * ‖J ω‖) * Real.exp ‖t * X ω‖) μ) :
    Integrable (fun ω => (H ω + t * J ω) * Complex.exp (t * X ω)) μ ∧
      (∫ ω, (H ω + t * J ω) * Complex.exp (t * X ω) ∂μ) = 0 := by
  let F (N : ℕ) (ω : Ω) := H ω * exponentialPartial (N + 1) (t * X ω) +
    t * J ω * exponentialPartial N (t * X ω)
  let B (ω : Ω) := (‖H ω‖ + ‖t‖ * ‖J ω‖) * Real.exp ‖t * X ω‖
  have hFi (N : ℕ) : Integrable (F N) μ := by
    have hh := integrable_finset_sum (Finset.range (N + 1)) (fun n _ =>
      ((hpoly n).1.const_mul (t ^ n / (n.factorial : ℂ))))
    simpa only [exponentialPartial_loop_sum] using hh
  have hzero (N : ℕ) : (∫ ω, F N ω ∂μ) = 0 := by
    simp only [F, ← exponentialPartial_loop_sum]
    rw [integral_finset_sum _ (fun n _ => (hpoly n).1.const_mul _)]
    simp only [integral_const_mul, (hpoly _).2, mul_zero, Finset.sum_const_zero]
  have hb (N : ℕ) (ω : Ω) : ‖F N ω‖ ≤ B ω := by
    calc
      _ ≤ ‖H ω‖ * ‖exponentialPartial (N + 1) (t * X ω)‖ +
          ‖t‖ * ‖J ω‖ * ‖exponentialPartial N (t * X ω)‖ := by
        simpa only [F, norm_mul] using norm_add_le
          (H ω * exponentialPartial (N + 1) (t * X ω))
          (t * J ω * exponentialPartial N (t * X ω))
      _ ≤ ‖H ω‖ * Real.exp ‖t * X ω‖ + ‖t‖ * ‖J ω‖ * Real.exp ‖t * X ω‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (norm_exponentialPartial_le _ _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (norm_exponentialPartial_le _ _) (by positivity))
      _ = B ω := by dsimp [B]; ring
  have hlim (ω : Ω) : Tendsto (fun N => F N ω) atTop
      (𝓝 ((H ω + t * J ω) * Complex.exp (t * X ω))) := by
    have h0 := tendsto_exponentialPartial (t * X ω)
    have hh := ((h0.comp (tendsto_add_atTop_nat 1)).const_mul (H ω)).add (h0.const_mul (t * J ω))
    simpa only [F, Function.comp_apply, add_mul] using hh
  have htarget : Integrable (fun ω => (H ω + t * J ω) * Complex.exp (t * X ω)) μ := by
    apply hdom.mono' ((hH.add (hJ.const_mul t)).mul
      (Complex.continuous_exp.comp_aestronglyMeasurable (hX.const_mul t)))
    exact Filter.Eventually.of_forall fun ω => le_of_tendsto (hlim ω).norm
      (Filter.Eventually.of_forall (fun N => hb N ω))
  have hi := tendsto_integral_of_dominated_convergence B (fun N => (hFi N).aestronglyMeasurable)
    hdom (fun N => Filter.Eventually.of_forall (hb N)) (Filter.Eventually.of_forall hlim)
  refine ⟨htarget, ?_⟩
  simp only [hzero] at hi
  exact tendsto_nhds_unique hi (tendsto_const_nhds (x := (0 : ℂ)))


/-- An exponential-square anchor moment dominates every fixed polynomial times
every linear exponential. -/
theorem integrable_anchor_polynomial_exp
    (ν : Measure AnchoredCountingState) {t : ℝ} (ht : 0 < t)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (t * ‖s.val.2‖ ^ 2)) ν)
    {C : ℝ} (hC : 0 ≤ C) (d : ℕ) (L : ℝ) :
    Integrable (fun s : AnchoredCountingState => C * (1 + ‖s.val.2‖) ^ d * Real.exp (L * ‖s.val.2‖)) ν := by
  have hm : Continuous (fun s : AnchoredCountingState => ‖s.val.2‖) :=
    (continuous_snd.comp continuous_subtype_val).norm
  have hh := integrable_exp_mul_abs_of_exp_sq hm.aestronglyMeasurable ht he ((d : ℝ) + L)
  simp only [abs_norm] at hh
  apply (hh.const_mul C).mono' (show Continuous
    (fun s : AnchoredCountingState => C * (1 + ‖s.val.2‖) ^ d * Real.exp (L * ‖s.val.2‖)) from
      (continuous_const.mul ((continuous_const.add hm).pow d)).mul
        (Real.continuous_exp.comp (continuous_const.mul hm))).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro s
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp : (1 + ‖s.val.2‖) ^ d ≤ Real.exp ((d : ℝ) * ‖s.val.2‖) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by positivity)
    simpa only [add_comm] using Real.add_one_le_exp ‖s.val.2‖
  calc
    _ ≤ C * Real.exp ((d : ℝ) * ‖s.val.2‖) * Real.exp (L * ‖s.val.2‖) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) (Real.exp_nonneg _)
    _ = C * Real.exp (((d : ℝ) + L) * ‖s.val.2‖) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The quadratic head of the loop equation. -/
def anchoredLoopHead (β : Beta) (s : AnchoredCountingState) (w : ℂ) : ℂ :=
  ((2 - β.value) / β.value) * anchoredDerivative s w + anchoredNevanlinna s w ^ 2 + 1

theorem continuous_anchoredLoopHead (β : Beta) {w : ℂ} (hw : w.im ≠ 0) :
    Continuous (fun s : AnchoredCountingState => anchoredLoopHead β s w) :=
  ((continuous_const.mul (continuous_anchoredDerivative hw)).add
    ((continuous_anchoredNevanlinna hw).pow 2)).add continuous_const

theorem anchoredGrowth_loopHead (β : Beta) {w : ℂ} (hw : w.im ≠ 0) :
    AnchoredGrowth (fun s => anchoredLoopHead β s w) 2 := by
  have hs := (anchoredGrowth_nevanlinna hw).mul (anchoredGrowth_nevanlinna hw)
  simp only [← pow_two] at hs
  exact (((AnchoredGrowth.const_mul _ (anchoredGrowth_derivative hw)).mono (by omega)).add hs).add
    ((AnchoredGrowth.const 1).mono (by omega))

/-- Repeated parameters yield the usual one-variable polynomial derivative term. -/
theorem anchoredLoopIntegrand_repeat (β : Beta) (s : AnchoredCountingState) (w v : ℂ) (n : ℕ) :
    anchoredLoopIntegrand β s w (fun _ : Fin n => v) =
      anchoredLoopHead β s w * anchoredNevanlinna s v ^ n +
        (n : ℂ) * ((2 / β.value) * anchoredInteraction s w v) * anchoredNevanlinna s v ^ (n - 1) := by
  simp only [anchoredLoopIntegrand, anchoredLoopHead, excludedProduct, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.sum_const, nsmul_eq_mul]
  ring

/-- The exact hierarchy implies an honest exponential generating identity, with
all integrability justified by the derived exponential-square anchor moment. -/
theorem exponential_tilted_loop_identity
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) (t : ℂ) :
    Integrable (fun s => (anchoredLoopHead β s w +
      t * ((2 / β.value) * anchoredInteraction s w v)) * Complex.exp (t * anchoredNevanlinna s v)) ν ∧
    (∫ s, (anchoredLoopHead β s w + t * ((2 / β.value) * anchoredInteraction s w v)) *
      Complex.exp (t * anchoredNevanlinna s v) ∂ν) = 0 := by
  let H := fun s : AnchoredCountingState => anchoredLoopHead β s w
  let X := fun s : AnchoredCountingState => anchoredNevanlinna s v
  let J := fun s : AnchoredCountingState => (2 / β.value) * anchoredInteraction s w v
  have hH := continuous_anchoredLoopHead β hw
  have hX := continuous_anchoredNevanlinna hv
  have hJ : Continuous J := continuous_const.mul (continuous_anchoredInteraction hw hv)
  apply integral_exponential_identity_of_monomials ν H X J t hH.aestronglyMeasurable
    hX.aestronglyMeasurable hJ.aestronglyMeasurable
  · intro n
    simpa only [anchoredLoopIntegrand_repeat] using hh n w hw (fun _ => v) (fun _ => hv)
  · obtain ⟨C, hC, hb⟩ := anchoredGrowth_loopHead β hw
    obtain ⟨D, hD, hd⟩ := (AnchoredGrowth.const_mul (2 / β.value)
      (anchoredGrowth_interaction hw hv)).mono (show 1 ≤ 2 by omega)
    let L := 1 + ‖v‖ + ‖1 + v ^ 2‖ / |v.im|
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hlin (s : AnchoredCountingState) : ‖t * X s‖ ≤ (‖t‖ * L) * ‖s.val.2‖ := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (norm_anchoredNevanlinna_le_anchor s hv)
        (norm_nonneg t)).trans_eq (by ring)
    have hbound := integrable_anchor_polynomial_exp ν ha he
      (add_nonneg hC (mul_nonneg (norm_nonneg t) hD)) 2 (‖t‖ * L)
    apply hbound.mono' (((hH.norm.add (continuous_const.mul hJ.norm)).mul
      (Real.continuous_exp.comp (continuous_const.mul hX).norm)).aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro s
    change ‖(‖H s‖ + ‖t‖ * ‖J s‖) * Real.exp ‖t * X s‖‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (Real.exp_nonneg _))]
    have hcoef : ‖H s‖ + ‖t‖ * ‖J s‖ ≤ (C + ‖t‖ * D) * (1 + ‖s.val.2‖) ^ 2 := by
      exact (add_le_add (hb s) (mul_le_mul_of_nonneg_left (hd s) (norm_nonneg t))).trans_eq (by ring)
    exact mul_le_mul hcoef (Real.exp_le_exp.mpr (hlin s)) (Real.exp_nonneg _) (by positivity)

end BourgadeHuang
