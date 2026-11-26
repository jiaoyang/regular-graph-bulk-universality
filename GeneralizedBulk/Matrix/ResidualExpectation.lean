import GeneralizedBulk.Matrix.LimitNormalization

/-! The expected inverse-free residual vanishes from actual fluctuation second moments. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Graph
open GeneralizedSwitching Exterior Analysis

/-- Forward and reversed fluctuations may be correlated. Their second
moments, a uniform mean second moment, and the literal switching identity
already force vanishing expected common residual. -/
theorem integral_switchingResidual_tendsto_zero_of_fluctuations
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H M Mtilde : ℕ → Ω → Mat) (h x y : ℕ → Ω → ℝ)
    (hh : ∀ n, AEStronglyMeasurable (h n) P)
    (hx : ∀ n, AEStronglyMeasurable (x n) P) (hy : ∀ n, AEStronglyMeasurable (y n) P)
    (hR : ∀ n, AEStronglyMeasurable (fun ω => ‖switchingResidual (H n ω) 0 1‖) P)
    (hH : ∀ n, ∀ᵐ ω ∂P, EntryBound (H n ω) (h n ω))
    (hX : ∀ n, ∀ᵐ ω ∂P, EntryBound (M n ω - H n ω) (x n ω))
    (hY : ∀ n, ∀ᵐ ω ∂P, EntryBound
      (endpointPermutation * (Mtilde n ω - H n ω) * endpointPermutation) (y n ω))
    (hshift : ∀ n, ∀ᵐ ω ∂P, (1 + M n ω * switchIncrement) *
      (endpointPermutation * Mtilde n ω * endpointPermutation) = M n ω)
    (hh2 : ∀ n, Integrable (fun ω => h n ω ^ 2) P)
    (hx2 : ∀ n, Integrable (fun ω => x n ω ^ 2) P)
    (hy2 : ∀ n, Integrable (fun ω => y n ω ^ 2) P)
    (hxzero : Tendsto (fun n => ∫ ω, x n ω ^ 2 ∂P) atTop (𝓝 0))
    (hyzero : Tendsto (fun n => ∫ ω, y n ω ^ 2 ∂P) atTop (𝓝 0))
    (C : ℝ) (hC : 0 ≤ C) (hmean : ∀ n, (∫ ω, h n ω ^ 2 ∂P) ≤ C) :
    Tendsto (fun n => ∫ ω, ‖switchingResidual (H n ω) 0 1‖ ∂P) atTop (𝓝 0) := by
  have hhnonneg (n) : ∀ᵐ ω ∂P, 0 ≤ h n ω := (hH n).mono (fun ω hω => hω.nonneg)
  have hxnonneg (n) : ∀ᵐ ω ∂P, 0 ≤ x n ω := (hX n).mono (fun ω hω => hω.nonneg)
  have hynonneg (n) : ∀ᵐ ω ∂P, 0 ≤ y n ω := (hY n).mono (fun ω hω => hω.nonneg)
  have hfirstX := integral_tendsto_zero_of_square_tendsto P x hx hxnonneg hx2 hxzero
  have hfirstY := integral_tendsto_zero_of_square_tendsto P y hy hynonneg hy2 hyzero
  have hprodXH := integral_product_tendsto_zero_of_square_tendsto P x h hx hh
    hxnonneg hhnonneg hx2 hh2 hxzero C hC hmean
  have hprodYH := integral_product_tendsto_zero_of_square_tendsto P y h hy hh
    hynonneg hhnonneg hy2 hh2 hyzero C hC hmean
  have hybounded : ∃ D : ℝ, 0 ≤ D ∧ ∀ n, (∫ ω, y n ω ^ 2 ∂P) ≤ D := by
    obtain ⟨D,hD⟩ := hyzero.bddAbove_range
    refine ⟨max D 0, le_max_right _ _, ?_⟩
    intro n
    exact (hD (Set.mem_range_self n)).trans (le_max_left _ _)
  obtain ⟨D,hD,hDbound⟩ := hybounded
  have hprodXY := integral_product_tendsto_zero_of_square_tendsto P x y hx hy
    hxnonneg hynonneg hx2 hy2 hxzero D hD hDbound
  let Q := fun n ω => x n ω + y n ω + 16 * (y n ω * h n ω) +
    16 * (x n ω * h n ω) + 16 * (x n ω * y n ω)
  have hiX (n) : Integrable (x n) P :=
    ((memLp_two_iff_integrable_sq (hx n)).mpr (hx2 n)).integrable (by norm_num)
  have hiY (n) : Integrable (y n) P :=
    ((memLp_two_iff_integrable_sq (hy n)).mpr (hy2 n)).integrable (by norm_num)
  have hiYH (n) := integrable_real_product_of_squares P (y n) (h n) (hy n) (hh n) (hy2 n) (hh2 n)
  have hiXH (n) := integrable_real_product_of_squares P (x n) (h n) (hx n) (hh n) (hx2 n) (hh2 n)
  have hiXY (n) := integrable_real_product_of_squares P (x n) (y n) (hx n) (hy n) (hx2 n) (hy2 n)
  have hiQ (n) : Integrable (Q n) P :=
    ((((hiX n).add (hiY n)).add ((hiYH n).const_mul 16)).add
      ((hiXH n).const_mul 16)).add ((hiXY n).const_mul 16)
  have hpoint (n) : ∀ᵐ ω ∂P, ‖switchingResidual (H n ω) 0 1‖ ≤ Q n ω := by
    filter_upwards [hH n,hX n,hY n,hshift n] with ω hHω hXω hYω hshiftω
    have hbound := switchingResidual_entry_le_errors (H n ω) (M n ω) (Mtilde n ω)
      (h n ω) (x n ω) (y n ω) hHω hXω hYω hshiftω
    convert hbound using 1 <;> dsimp [Q] <;> ring
  have hiR (n) : Integrable (fun ω => ‖switchingResidual (H n ω) 0 1‖) P := by
    apply (hiQ n).mono' (hR n)
    filter_upwards [hpoint n] with ω hω
    simpa only [norm_norm] using hω
  have heq (n) : (∫ ω, Q n ω ∂P) = (∫ ω, x n ω ∂P) + (∫ ω, y n ω ∂P) +
      16 * (∫ ω, y n ω * h n ω ∂P) + 16 * (∫ ω, x n ω * h n ω ∂P) +
      16 * (∫ ω, x n ω * y n ω ∂P) := by
    dsimp [Q]
    have h1 := integral_add (hiX n) (hiY n)
    have h2 := integral_add ((hiX n).add (hiY n)) ((hiYH n).const_mul 16)
    have h3 := integral_add (((hiX n).add (hiY n)).add ((hiYH n).const_mul 16))
      ((hiXH n).const_mul 16)
    have h4 := integral_add ((((hiX n).add (hiY n)).add ((hiYH n).const_mul 16)).add
      ((hiXH n).const_mul 16)) ((hiXY n).const_mul 16)
    simp only [Pi.add_apply] at h1 h2 h3 h4
    rw [h4,h3,h2,h1,integral_const_mul,integral_const_mul,integral_const_mul]
  have hQzero : Tendsto (fun n => ∫ ω, Q n ω ∂P) atTop (𝓝 0) := by
    simp_rw [heq]
    simpa only [mul_zero,add_zero] using
      (((hfirstX.add hfirstY).add (hprodYH.const_mul 16)).add (hprodXH.const_mul 16)).add
        (hprodXY.const_mul 16)
  exact squeeze_zero (fun n => integral_nonneg (fun ω => norm_nonneg _))
    (fun n => integral_mono_ae (hiR n) (hiQ n) (hpoint n)) hQzero

/-- The scalar normalization follows from the inverse-free switched coupling
and second moments. No expected polynomial identity is an input. -/
theorem normalization_of_inverse_free_switching_and_second_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (parameters : Parameters) (s : ℕ → Ω → ℂ)
    (hs : ∀ n, AEStronglyMeasurable (s n) P)
    (hsupper : ∀ n, ∀ᵐ ω ∂P, 0 ≤ (s n ω).im)
    (hs2 : ∀ n, Integrable (fun ω => ‖s n ω‖ ^ 2) P)
    (M Mtilde : ℕ → Ω → Mat) (h x y : ℕ → Ω → ℝ)
    (hh : ∀ n, AEStronglyMeasurable (h n) P)
    (hx : ∀ n, AEStronglyMeasurable (x n) P) (hy : ∀ n, AEStronglyMeasurable (y n) P)
    (hH : ∀ n, ∀ᵐ ω ∂P, EntryBound (calibratedMean parameters (s n ω)) (h n ω))
    (hX : ∀ n, ∀ᵐ ω ∂P, EntryBound (M n ω - calibratedMean parameters (s n ω)) (x n ω))
    (hY : ∀ n, ∀ᵐ ω ∂P, EntryBound
      (endpointPermutation * (Mtilde n ω - calibratedMean parameters (s n ω)) * endpointPermutation) (y n ω))
    (hshift : ∀ n, ∀ᵐ ω ∂P, (1 + M n ω * switchIncrement) *
      (endpointPermutation * Mtilde n ω * endpointPermutation) = M n ω)
    (hh2 : ∀ n, Integrable (fun ω => h n ω ^ 2) P)
    (hx2 : ∀ n, Integrable (fun ω => x n ω ^ 2) P)
    (hy2 : ∀ n, Integrable (fun ω => y n ω ^ 2) P)
    (hxzero : Tendsto (fun n => ∫ ω, x n ω ^ 2 ∂P) atTop (𝓝 0))
    (hyzero : Tendsto (fun n => ∫ ω, y n ω ^ 2 ∂P) atTop (𝓝 0))
    (C : ℝ) (hC : 0 ≤ C) (hmean : ∀ n, (∫ ω, h n ω ^ 2 ∂P) ≤ C) :
    Tendsto (fun n => ∫ ω, ‖s n ω - Complex.I‖ ∂P) atTop (𝓝 0) := by
  have hpoly (n) : Integrable (fun ω => s n ω ^ 2 + 1) P := by
    apply Integrable.add _ (integrable_const 1)
    exact (integrable_norm_iff ((hs n).pow 2)).mp (by simpa only [Pi.pow_apply,norm_pow] using hs2 n)
  have hR (n) : AEStronglyMeasurable (fun ω =>
      ‖switchingResidual (calibratedMean parameters (s n ω)) 0 1‖) P := by
    apply (((hpoly n).aestronglyMeasurable.norm).const_mul
      (parameters.scale ^ 2 * (1 - parameters.p ^ 2))).congr
    exact Eventually.of_forall (fun ω => (calibratedMean_residual_entry_norm parameters (s n ω)).symm)
  apply integral_normalization_of_calibrated_residual P parameters s hs hsupper hpoly
  exact integral_switchingResidual_tendsto_zero_of_fluctuations P
    (fun n ω => calibratedMean parameters (s n ω)) M Mtilde h x y hh hx hy hR
    hH hX hY hshift hh2 hx2 hy2 hxzero hyzero C hC hmean

end GeneralizedBulk.Graph
