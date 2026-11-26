import GeneralizedBulk.Gaussian.Series

/-! # Quantitative L² bounds for the constructed orthogonal marked sum -/
noncomputable section
open MeasureTheory Filter BourgadeHuang
open scoped BigOperators Topology

namespace GeneralizedBulk.Gaussian

section Hilbert
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Pythagoras for a finite collection of arbitrary orthogonal vectors. -/
theorem norm_sum_sq_of_pairwise_inner_zero (f : ι → E)
    (horth : Pairwise fun i j => @inner ℂ E _ (f i) (f j) = 0) (s : Finset ι) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  let V : ι → Submodule ℂ E := fun i => Submodule.span ℂ {f i}
  have hV : OrthogonalFamily ℂ (fun i => V i) (fun i => (V i).subtypeₗᵢ) := by
    apply OrthogonalFamily.of_pairwise
    intro i j hij
    change Submodule.span ℂ {f i} ⟂ Submodule.span ℂ {f j}
    rw [Submodule.isOrtho_span]
    intro u hu v hv
    simp only [Set.mem_singleton_iff] at hu hv
    subst u; subst v
    exact horth hij
  let v : ∀ i, V i := fun i => ⟨f i, Submodule.subset_span (by simp)⟩
  exact hV.norm_sum v s

omit [CompleteSpace E] in
/-- The norm square of the infinite orthogonal sum equals the sum of the norm
squares; the proof passes the finite Pythagorean identity through norm limits. -/
theorem norm_sq_hasSum_of_pairwise_inner_zero (f : ι → E) (hf : Summable f)
    (horth : Pairwise fun i j => @inner ℂ E _ (f i) (f j) = 0) :
    HasSum (fun i => ‖f i‖ ^ 2) (‖∑' i, f i‖ ^ 2) := by
  have hlim := hf.hasSum.norm.pow 2
  exact hlim.congr' (Filter.Eventually.of_forall (norm_sum_sq_of_pairwise_inner_zero f horth))

omit [CompleteSpace E] in
theorem norm_tsum_sq_of_pairwise_inner_zero (f : ι → E) (hf : Summable f)
    (horth : Pairwise fun i j => @inner ℂ E _ (f i) (f j) = 0) :
    ‖∑' i, f i‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 :=
  (norm_sq_hasSum_of_pairwise_inner_zero f hf horth).tsum_eq.symm

/-- Weighted orthogonal sums obey the expected square-variance bound. -/
theorem norm_weighted_tsum_sq_le (f : ι → E) (a : ι → ℂ) (B : ℝ)
    (horth : Pairwise fun i j => @inner ℂ E _ (f i) (f j) = 0)
    (hB : 0 ≤ B) (hbound : ∀ i, ‖f i‖ ^ 2 ≤ B)
    (ha : Summable fun i => ‖a i‖ ^ 2) :
    ‖∑' i, a i • f i‖ ^ 2 ≤ B * ∑' i, ‖a i‖ ^ 2 := by
  have hs := summable_weighted_orthogonal f a B horth hB hbound ha
  have horth' : Pairwise fun i j => @inner ℂ E _ (a i • f i) (a j • f j) = 0 := by
    intro i j hij
    simp [inner_smul_left, inner_smul_right, horth hij]
  rw [norm_tsum_sq_of_pairwise_inner_zero _ hs horth']
  calc
    _ ≤ ∑' i, B * ‖a i‖ ^ 2 := by
      apply Summable.tsum_le_tsum _ (norm_sq_hasSum_of_pairwise_inner_zero _ hs horth').summable (ha.mul_left B)
      intro i
      rw [norm_smul, mul_pow]
      nlinarith [hbound i, sq_nonneg ‖a i‖]
    _ = _ := tsum_mul_left

end Hilbert

section L2
variable {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- The L² norm is the actual second moment of its measurable representative. -/
theorem integral_norm_sq_L2 (f : Lp ℂ 2 μ) :
    (∫ ω, ‖f ω‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using (L2.inner_def (𝕜 := ℝ) f f).symm

/-- Cauchy--Schwarz bounds the ordinary expectation of a bilinear product by
its two L² norms. This controls the degree-two stationary observables. -/
theorem integral_norm_product_L2_le (f g : Lp ℂ 2 μ) :
    (∫ ω, ‖f ω * g ω‖ ∂μ) ≤ ‖f‖ * ‖g‖ := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hf : MemLp (fun ω => f ω) (ENNReal.ofReal (2 : ℝ)) μ := by simpa using Lp.memLp f
  have hg : MemLp (fun ω => g ω) (ENNReal.ofReal (2 : ℝ)) μ := by simpa using Lp.memLp g
  have h := integral_mul_norm_le_Lp_mul_Lq hpq hf hg
  simp only [Real.rpow_two, integral_norm_sq_L2, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg f), Real.sqrt_sq (norm_nonneg g)] at h
  simpa only [norm_mul] using h

/-- A symmetric quadratic second-moment bound, avoiding square roots in
subsequent scalar-state polynomial estimates. -/
theorem integral_norm_product_L2_le_half_sq (f g : Lp ℂ 2 μ) :
    (∫ ω, ‖f ω * g ω‖ ∂μ) ≤ (‖f‖ ^ 2 + ‖g‖ ^ 2) / 2 := by
  have h := integral_norm_product_L2_le μ f g
  nlinarith [sq_nonneg (‖f‖ - ‖g‖)]

/-- A real-valued centered quadratic mark has the same Hilbert and bilinear
cross covariance. This bridges independence to L² orthogonality. -/
theorem l2_inner_eq_bilinear_of_ae_real (f g : Lp ℂ 2 μ) (F : Ω → ℝ)
    (hf : (f : Ω → ℂ) =ᵐ[μ] (fun ω => (F ω : ℂ))) :
    @inner ℂ (Lp ℂ 2 μ) _ f g = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf] with ω hω
  simp only [RCLike.inner_apply', hω, Complex.conj_ofReal]

/-- The squared L² norm of a real mark is its ordinary second moment. -/
theorem l2_norm_sq_of_ae_real (f : Lp ℂ 2 μ) (F : Ω → ℝ)
    (hf : (f : Ω → ℂ) =ᵐ[μ] (fun ω => (F ω : ℂ))) :
    ‖f‖ ^ 2 = ∫ ω, F ω ^ 2 ∂μ := by
  rw [← integral_norm_sq_L2]
  apply integral_congr_ae
  filter_upwards [hf] with ω hω
  simp only [hω, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A polynomial second-moment bound on the first absolute moment is enough
for the common analytic version; no Gaussian moment inequality is required. -/
theorem integral_norm_L2_le_one_add_sq [IsProbabilityMeasure μ] (f : Lp ℂ 2 μ) :
    (∫ ω, ‖f ω‖ ∂μ) ≤ 1 + ‖f‖ ^ 2 := by
  have hi : Integrable (fun ω => ‖f ω‖) μ := (MemLp.integrable (by norm_num) (Lp.memLp f)).norm
  have hi2 : Integrable (fun ω => ‖f ω‖ ^ 2) μ := (Lp.memLp f).integrable_norm_pow'
  calc
    _ ≤ ∫ ω, 1 + ‖f ω‖ ^ 2 ∂μ := by
      apply integral_mono hi ((integrable_const _).add hi2)
      intro ω
      change ‖f ω‖ ≤ 1 + ‖f ω‖ ^ 2
      nlinarith [sq_nonneg (‖f ω‖ - 1)]
    _ = _ := by rw [integral_add (integrable_const _) hi2, integral_norm_sq_L2]; simp

/-- Conditional second moment bound for the constructed marked resolvent
entry. This is sufficient for the degree-two stationary loop observable. -/
theorem integral_norm_sq_l2Series_le (marks : ι → Lp ℂ 2 μ) (coeff : ι → ℂ) (B : ℝ)
    (horth : Pairwise fun i j => @inner ℂ (Lp ℂ 2 μ) _ (marks i) (marks j) = 0)
    (hB : 0 ≤ B) (hbound : ∀ i, ‖marks i‖ ^ 2 ≤ B)
    (ha : Summable fun i => ‖coeff i‖ ^ 2) :
    (∫ ω, ‖l2Series μ marks coeff ω‖ ^ 2 ∂μ) ≤ B * ∑' i, ‖coeff i‖ ^ 2 := by
  rw [integral_norm_sq_L2]
  exact norm_weighted_tsum_sq_le marks coeff B horth hB hbound ha

end L2
end GeneralizedBulk.Gaussian
