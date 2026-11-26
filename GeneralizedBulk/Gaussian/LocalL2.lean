import GeneralizedBulk.Gaussian.SeriesPresentedBounds

/-! Uniform Hilbert convergence of the Gaussian series away from the real axis. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped BigOperators Topology

namespace GeneralizedBulk.Gaussian

theorem uniform_weighted_orthogonal_sum
    {I W E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (f : I → E) (a : W → I → ℂ) (weight : I → ℝ) (B : ℝ)
    (horth : Pairwise fun i j => @inner ℂ E _ (f i) (f j) = 0)
    (hB : 0 ≤ B) (hf : ∀ i, ‖f i‖ ^ 2 ≤ B)
    (hw : Summable weight) (ha : ∀ w i, ‖a w i‖ ^ 2 ≤ weight i) :
    TendstoUniformly (fun s : Finset I => fun w => ∑ i ∈ s, a w i • f i)
      (fun w => ∑' i, a w i • f i) atTop := by
  classical
  have hsq (w : W) : Summable (fun i => ‖a w i‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) (ha w) hw
  have hs (w : W) : Summable (fun i => a w i • f i) :=
    summable_weighted_orthogonal f (a w) B horth hB hf (hsq w)
  have hb (s : Finset I) (w : W) :
      dist (∑' i, a w i • f i) (∑ i ∈ s, a w i • f i) ^ 2 ≤
        B * ((∑' i, weight i) - ∑ i ∈ s, weight i) := by
    let J := {i : I // i ∉ s}
    have ho : Pairwise fun i j : J => @inner ℂ E _ (f i) (f j) = 0 := by
      intro i j hij
      exact horth (fun h => hij (Subtype.ext h))
    have ht := norm_weighted_tsum_sq_le (fun i : J => f i) (fun i : J => a w i) B
      ho hB (fun i => hf i) ((hsq w).subtype {i | i ∉ s})
    have hc : (∑' i : J, ‖a w i‖ ^ 2) ≤ ∑' i : J, weight i :=
      ((hsq w).subtype {i | i ∉ s}).tsum_le_tsum (fun i => ha w i)
        (hw.subtype {i | i ∉ s})
    have htail : (∑' i : J, weight i) = (∑' i, weight i) - ∑ i ∈ s, weight i := by
      have hh := hw.sum_add_tsum_subtype_compl s
      change (∑ i ∈ s, weight i) + (∑' i : J, weight i) = ∑' i, weight i at hh
      linarith
    have heq : dist (∑' i, a w i • f i) (∑ i ∈ s, a w i • f i) =
        ‖∑' i : J, a w i • f i‖ := by
      rw [dist_eq_norm, ← (hs w).sum_add_tsum_subtype_compl s]
      simp only [add_sub_cancel_left]
      rfl
    rw [heq]
    exact ht.trans ((mul_le_mul_of_nonneg_left hc hB).trans_eq (by rw [htail]))
  have ht : Tendsto (fun s : Finset I => B * ((∑' i, weight i) - ∑ i ∈ s, weight i))
      atTop (𝓝 0) := by
    have hbase : Tendsto (fun s : Finset I => (∑' i, weight i) - ∑ i ∈ s, weight i)
        atTop (𝓝 0) := by
      convert tendsto_const_nhds.sub hw.hasSum using 1
      simp
    simpa only [mul_zero] using tendsto_const_nhds.mul hbase (a := B)
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  filter_upwards [ht.eventually (gt_mem_nhds (sq_pos_of_pos hepsilon))] with s hs
  intro w
  have h := hb s w
  have hd := dist_nonneg (x := ∑' i, a w i • f i) (y := ∑ i ∈ s, a w i • f i)
  nlinarith

def stripEnvelope (delta M : ℝ) : ℝ :=
  1 + (2 * M) * (1 / delta) + (1 + M ^ 2) * (1 / delta) ^ 2

theorem particleCoefficient_sq_bound_strip (delta M : ℝ) (hd : 0 < delta) (hM : 0 ≤ M)
    (x : ℝ) (w : ℂ) (hw : delta ≤ |w.im|) (hwM : ‖w‖ ≤ M) (tag : Bool) :
    ‖particleCoefficient x (w, tag)‖ ^ 2 ≤
      (stripEnvelope delta M + stripEnvelope delta M ^ 2) * nevanlinnaWeight x := by
  have hw0 : w.im ≠ 0 := abs_pos.mp (lt_of_lt_of_le hd hw)
  have hC : 0 ≤ stripEnvelope delta M := by unfold stripEnvelope; positivity
  have hb := norm_reciprocal_sq_le_weight_uniform x hd hw hwM
  change ‖(((x : ℂ) - w)⁻¹) ^ 2‖ ≤ stripEnvelope delta M * nevanlinnaWeight x at hb
  have hn : 0 ≤ nevanlinnaWeight x := nevanlinnaWeight_nonneg x
  have hle : nevanlinnaWeight x ≤ 1 := by
    unfold nevanlinnaWeight
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
  cases tag
  · simp only [particleCoefficient, hw0, ↓reduceIte, Bool.false_eq_true, norm_pow] at hb ⊢
    nlinarith [mul_nonneg (sq_nonneg (stripEnvelope delta M)) hn]
  · simp only [particleCoefficient, hw0, ↓reduceIte] at ⊢
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hw2 : nevanlinnaWeight x ^ 2 ≤ nevanlinnaWeight x := by nlinarith
    rw [mul_pow] at hsq
    have h := mul_le_mul_of_nonneg_left hw2 (sq_nonneg (stripEnvelope delta M))
    nlinarith [mul_nonneg hC hn]

/-- The actual Gaussian matrix series and its derivative converge uniformly
in conditional L² on every bounded strip separated from the real axis. Thus
compact convergence is not merely inferred from pointwise L² convergence. -/
theorem presentedGaussianL2_uniform_on_strip
    {I : Type*} [Countable I] {s : AnchoredCountingState}
    (parameters : Parameters) (p : ParticlePresentation s I)
    (delta M : ℝ) (hd : 0 < delta) (hM : 0 ≤ M) (tag : Bool) (i j : Fin 4) :
    TendstoUniformly
      (fun a : Finset I => fun w : {w : ℂ // delta ≤ |w.im| ∧ ‖w‖ ≤ M} =>
        ∑ n ∈ a, ((parameters.scale : ℂ) * particleCoefficient (p.location n) (w.1, tag)) •
          markQuadraticLp parameters.p n i j)
      (fun w => l2Series (iidLaw (markLaw parameters.p) I)
        (fun n => markQuadraticLp parameters.p n i j)
        (fun n => (parameters.scale : ℂ) * particleCoefficient (p.location n) (w.1, tag))) atTop := by
  apply uniform_weighted_orthogonal_sum
    (weight := fun n => (‖(parameters.scale : ℂ)‖ ^ 2 *
      (stripEnvelope delta M + stripEnvelope delta M ^ 2)) * nevanlinnaWeight (p.location n))
    (B := 2)
  · intro n m hnm
    exact markQuadraticLp_inner_off parameters.p parameters.abs_p_lt_one hnm i j
  · norm_num
  · intro n
    exact markQuadraticLp_norm_sq_le_two parameters.p parameters.abs_p_lt_one n i j
  · exact p.summable_weight.mul_left _
  · intro w n
    rw [norm_mul, mul_pow]
    exact (mul_le_mul_of_nonneg_left
      (particleCoefficient_sq_bound_strip delta M hd hM (p.location n) w.1 w.2.1 w.2.2 tag)
      (sq_nonneg _)).trans_eq (by ring)

end GeneralizedBulk.Gaussian
