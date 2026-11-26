import Mathlib
import Mathlib.MeasureTheory.Function.Holder
import GeneralizedBulk.GaussianContractions
import GeneralizedBulk.Gaussian.ParticleKernels

/-!
# Orthogonal L² series of centered Gaussian marks

The series is constructed as an actual sum in the complete `Lp` space. Its
existence follows from pairwise orthogonality and square-summable coefficients;
no convergence or limiting covariance is assumed as a certificate.
-/

noncomputable section
open MeasureTheory Filter BourgadeHuang
open scoped BigOperators Topology ComplexConjugate

namespace GeneralizedBulk.Gaussian

section Hilbert
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Square-summable orthogonal vectors have a genuine convergent Hilbert sum. -/
theorem summable_of_pairwise_inner_zero (f : ι → E)
    (horth : Pairwise fun i j => @inner ℂ E _ (f i) (f j) = 0)
    (hsq : Summable fun i => ‖f i‖ ^ 2) : Summable f := by
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
  exact (hV.summable_iff_norm_sq_summable v).mpr hsq

/-- A uniform L² bound reduces convergence to the square-sum of coefficients. -/
theorem summable_weighted_orthogonal (f : ι → E) (a : ι → ℂ) (B : ℝ)
    (horth : Pairwise fun i j => @inner ℂ E _ (f i) (f j) = 0)
    (_hB : 0 ≤ B) (hbound : ∀ i, ‖f i‖ ^ 2 ≤ B)
    (ha : Summable fun i => ‖a i‖ ^ 2) : Summable fun i => a i • f i := by
  apply summable_of_pairwise_inner_zero
  · intro i j hij
    simp [inner_smul_left, inner_smul_right, horth hij]
  · apply Summable.of_nonneg_of_le (fun i => sq_nonneg _) _ (ha.mul_left B)
    intro i
    rw [norm_smul, mul_pow]
    nlinarith [hbound i, sq_nonneg ‖a i‖]

omit [CompleteSpace E] in
/-- A continuous bilinear covariance is the sum of the diagonal covariances
when distinct particle labels have zero cross covariance. -/
theorem bilinear_hasSum_diagonal (B : E →L[ℂ] E →L[ℂ] ℂ)
    (f g : ι → E) (hf : Summable f) (hg : Summable g)
    (hoff : ∀ i j, i ≠ j → B (f i) (g j) = 0) :
    HasSum (fun i => B (f i) (g i)) (B (∑' i, f i) (∑' i, g i)) := by
  classical
  have hfinite (s : Finset ι) :
      B (∑ i ∈ s, f i) (∑ j ∈ s, g j) = ∑ i ∈ s, B (f i) (g i) := by
    simp only [map_sum, ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_eq_single i
    · intro j hj hji
      exact hoff j i hji
    · intro hnot
      exact (hnot hi).elim
  have hlim := B.continuous₂.tendsto (∑' i, f i, ∑' i, g i)
  have hlim' := hlim.comp (hf.hasSum.prodMk_nhds hg.hasSum)
  change Tendsto (fun s : Finset ι => B (∑ i ∈ s, f i) (∑ j ∈ s, g j))
    atTop (𝓝 (B (∑' i, f i) (∑' i, g i))) at hlim'
  exact hlim'.congr' (Filter.Eventually.of_forall hfinite)

omit [CompleteSpace E] in
/-- Bilinear covariance commutes with the constructed orthogonal sum. -/
theorem bilinear_tsum_diagonal (B : E →L[ℂ] E →L[ℂ] ℂ)
    (f g : ι → E) (hf : Summable f) (hg : Summable g)
    (hoff : ∀ i j, i ≠ j → B (f i) (g j) = 0) :
    B (∑' i, f i) (∑' i, g i) = ∑' i, B (f i) (g i) :=
  (bilinear_hasSum_diagonal B f g hf hg hoff).tsum_eq.symm

end Hilbert

section L2
variable {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- The continuous bilinear (not sesquilinear) product expectation on L². -/
def l2Pairing : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2

/-- The continuous pairing is the ordinary integral of the product. -/
theorem l2Pairing_eq_integral (f g : Lp ℂ 2 μ) :
    l2Pairing μ f g = ∫ ω, f ω * g ω ∂μ := by
  exact ContinuousLinearMap.lpPairing_eq_integral _ _ _

/-- The actual infinite centered marked sum as an L² random variable. -/
def l2Series (marks : ι → Lp ℂ 2 μ) (coeff : ι → ℂ) : Lp ℂ 2 μ :=
  ∑' i, coeff i • marks i

/-- Partial marked sums converge in L² once the coefficients are square-summable. -/
theorem hasSum_l2Series (marks : ι → Lp ℂ 2 μ) (coeff : ι → ℂ) (B : ℝ)
    (horth : Pairwise fun i j => @inner ℂ (Lp ℂ 2 μ) _ (marks i) (marks j) = 0)
    (hB : 0 ≤ B) (hbound : ∀ i, ‖marks i‖ ^ 2 ≤ B)
    (ha : Summable fun i => ‖coeff i‖ ^ 2) :
    HasSum (fun i => coeff i • marks i) (l2Series μ marks coeff) :=
  (summable_weighted_orthogonal marks coeff B horth hB hbound ha).hasSum

/-- Products of the L² representatives are genuinely integrable. -/
theorem integrable_l2_product (f g : Lp ℂ 2 μ) :
    Integrable (fun ω => f ω * g ω) μ :=
  (Lp.memLp f).integrable_mul (Lp.memLp g)

/-- Covariance of two weighted particle series is obtained by passing the
finite diagonal contraction through continuous bilinear L² pairing. -/
theorem l2Series_covariance (f g : ι → Lp ℂ 2 μ) (a b : ι → ℂ)
    (hf : Summable fun i => a i • f i) (hg : Summable fun i => b i • g i)
    (hoff : ∀ i j, i ≠ j → l2Pairing μ (f i) (g j) = 0) :
    (∫ ω, l2Series μ f a ω * l2Series μ g b ω ∂μ) =
      ∑' i, (a i * b i) * (∫ ω, f i ω * g i ω ∂μ) := by
  rw [← l2Pairing_eq_integral]
  have hzero : ∀ i j, i ≠ j →
      l2Pairing μ (a i • f i) (b j • g j) = 0 := by
    intro i j hij
    simp [map_smul, ContinuousLinearMap.smul_apply, hoff i j hij]
  have hdiag := bilinear_tsum_diagonal (l2Pairing μ)
    (fun i => a i • f i) (fun i => b i • g i) hf hg hzero
  simpa only [l2Series, map_smul, ContinuousLinearMap.smul_apply,
    smul_eq_mul, mul_assoc, mul_left_comm, l2Pairing_eq_integral] using hdiag

/-- Pairing with the constant one is the expectation, on a finite mark space. -/
theorem l2Pairing_one [IsFiniteMeasure μ] (f : Lp ℂ 2 μ) :
    l2Pairing μ f (Lp.const 2 μ 1) = ∫ ω, f ω ∂μ := by
  rw [l2Pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ (1 : ℂ)] with ω hω
  simp only [hω, Function.const_apply, mul_one]

/-- Centering survives the L² limit; the infinite series has zero mean. -/
theorem l2Series_mean_zero [IsFiniteMeasure μ] (marks : ι → Lp ℂ 2 μ) (coeff : ι → ℂ)
    (hsum : Summable fun i => coeff i • marks i)
    (hmean : ∀ i, (∫ ω, marks i ω ∂μ) = 0) :
    (∫ ω, l2Series μ marks coeff ω ∂μ) = 0 := by
  rw [← l2Pairing_one]
  unfold l2Series
  change ((l2Pairing μ).flip (Lp.const 2 μ 1)) (∑' i, coeff i • marks i) = 0
  rw [ContinuousLinearMap.map_tsum _ hsum]
  simp [map_smul, l2Pairing_one, hmean]

variable {Λ : Type*}

/-- Entrywise L² construction of the centered marked resolvent. -/
def matrixL2Series (marks : Λ → Matrix (Fin 4) (Fin 4) (Lp ℂ 2 μ))
    (coeff : ι → Λ → ℂ) (w : ι) (ω : Ω) : EndpointMatrix :=
  fun i j => l2Series μ (fun n => marks n i j) (coeff w) ω

/-- The complete infinite-series Wick interface follows from centered,
orthogonal particle marks. The convergence and limiting covariance are proved
here, rather than made fields of a convergence record. -/
theorem entryWickCovariance_matrixL2Series [IsFiniteMeasure μ]
    (marks : Λ → Matrix (Fin 4) (Fin 4) (Lp ℂ 2 μ))
    (coeff : ι → Λ → ℂ) (p sigma : ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hbound : ∀ n i j, ‖marks n i j‖ ^ 2 ≤ B)
    (horth : ∀ i j, Pairwise fun n m => @inner ℂ (Lp ℂ 2 μ) _ (marks n i j) (marks m i j) = 0)
    (hcoeff : ∀ w, Summable fun n => ‖coeff w n‖ ^ 2)
    (hmean : ∀ n i j, (∫ ω, marks n i j ω ∂μ) = 0)
    (hoff : ∀ n m, n ≠ m → ∀ i j a b,
      (∫ ω, marks n i j ω * marks m a b ω ∂μ) = 0)
    (hdiag : ∀ n i j a b,
      (∫ ω, marks n i j ω * marks n a b ω ∂μ) =
        covarianceMatrix p i a * covarianceMatrix p j b +
          covarianceMatrix p i b * covarianceMatrix p j a) :
    EntryWickCovariance μ p sigma (fun w u => ∑' n, coeff w n * coeff u n)
      (matrixL2Series μ marks (fun w n => sigma * coeff w n)) := by
  have hscoeff (w : ι) : Summable fun n => ‖sigma * coeff w n‖ ^ 2 := by
    simpa only [norm_mul, mul_pow] using (hcoeff w).mul_left (‖sigma‖ ^ 2)
  have hs (w : ι) (i j : Fin 4) : Summable fun n => (sigma * coeff w n) • marks n i j :=
    summable_weighted_orthogonal _ _ B (horth i j) hB (fun n => hbound n i j) (hscoeff w)
  constructor
  · intro w i j
    exact MemLp.integrable (by norm_num) (Lp.memLp _)
  · intro w i j
    exact l2Series_mean_zero μ _ _ (hs w i j) (fun n => hmean n i j)
  · intro w u i j a b
    exact integrable_l2_product μ _ _
  · intro w u i j a b
    change (∫ ω, l2Series μ (fun n => marks n i j) (fun n => sigma * coeff w n) ω *
      l2Series μ (fun n => marks n a b) (fun n => sigma * coeff u n) ω ∂μ) = _
    rw [l2Series_covariance μ _ _ _ _ (hs w i j) (hs u a b)]
    · simp_rw [hdiag]
      calc
        _ = ∑' n, (sigma ^ 2 * (covarianceMatrix p i a * covarianceMatrix p j b +
            covarianceMatrix p i b * covarianceMatrix p j a)) * (coeff w n * coeff u n) := by
          apply tsum_congr
          intro n
          ring
        _ = _ := by rw [tsum_mul_left]
    · intro n m hnm
      rw [l2Pairing_eq_integral]
      exact hoff n m hnm i j a b

/-- Specialization of the L² construction to the literal compensated particle
resolvent coefficients. Multiplicities are preserved by `ParticleLabels`. -/
theorem entryWickCovariance_particleSeries [IsFiniteMeasure μ]
    (s : AnchoredCountingState)
    (marks : s.val.1.ParticleLabels → Matrix (Fin 4) (Fin 4) (Lp ℂ 2 μ))
    (p sigma : ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ n i j, ‖marks n i j‖ ^ 2 ≤ B)
    (horth : ∀ i j, Pairwise fun n m => @inner ℂ (Lp ℂ 2 μ) _ (marks n i j) (marks m i j) = 0)
    (hmean : ∀ n i j, (∫ ω, marks n i j ω ∂μ) = 0)
    (hoff : ∀ n m, n ≠ m → ∀ i j a b,
      (∫ ω, marks n i j ω * marks m a b ω ∂μ) = 0)
    (hdiag : ∀ n i j a b,
      (∫ ω, marks n i j ω * marks n a b ω ∂μ) =
        covarianceMatrix p i a * covarianceMatrix p j b +
          covarianceMatrix p i b * covarianceMatrix p j a) :
    EntryWickCovariance μ p sigma (particleKernel s)
      (matrixL2Series μ marks (fun v n => sigma * particleCoefficient
        (s.val.1.particleLocation n) v)) := by
  have hh := entryWickCovariance_matrixL2Series μ marks
    (fun v n => particleCoefficient (s.val.1.particleLocation n) v) p sigma B hB
    hbound horth (summable_particleCoefficient_sq s) hmean hoff hdiag
  have hk : (fun v u => ∑' n : s.val.1.ParticleLabels,
      particleCoefficient (s.val.1.particleLocation n) v *
        particleCoefficient (s.val.1.particleLocation n) u) = particleKernel s := by
    funext v u
    exact (hasSum_particleKernel s v u).tsum_eq
  rw [hk] at hh
  exact hh

/-- The actual centered resolvent entry is a differentiable L²-valued function,
with derivative given by the `true` coefficient slot. The derivative is proved
by a summable uniform envelope on a nonreal ball. -/
theorem hasDerivAt_l2ParticleSeries (s : AnchoredCountingState)
    (marks : s.val.1.ParticleLabels → Lp ℂ 2 μ) (sigma : ℂ) (B : ℝ)
    (horth : Pairwise fun i j => @inner ℂ (Lp ℂ 2 μ) _ (marks i) (marks j) = 0)
    (hB : 0 ≤ B) (hbound : ∀ i, ‖marks i‖ ^ 2 ≤ B)
    {w : ℂ} (hw : w.im ≠ 0) :
    HasDerivAt
      (fun z => l2Series μ marks (fun i => sigma * particleCoefficient
        (s.val.1.particleLocation i) (z, false)))
      (l2Series μ marks (fun i => sigma * particleCoefficient
        (s.val.1.particleLocation i) (w, true))) w := by
  have hm (i : s.val.1.ParticleLabels) : ‖marks i‖ ≤ Real.sqrt B :=
    (Real.le_sqrt (norm_nonneg _) hB).mpr (hbound i)
  let u : s.val.1.ParticleLabels → ℝ := fun i =>
    (‖sigma‖ * Real.sqrt B * derivativeEnvelope w) * nevanlinnaWeight (s.val.1.particleLocation i)
  have hu : Summable u := s.summable_particle_weight.mul_left _
  have hR : 0 < |w.im| / 2 := by positivity
  have hder (i : s.val.1.ParticleLabels) (z : ℂ)
      (hz : z ∈ Metric.ball w (|w.im| / 2)) :
      HasDerivAt (fun y => (sigma * particleCoefficient (s.val.1.particleLocation i) (y, false)) • marks i)
        ((sigma * particleCoefficient (s.val.1.particleLocation i) (z, true)) • marks i) z := by
    exact ((hasDerivAt_particleCoefficient _
      (half_imaginary_ball_bound w z hw hz).2).const_mul sigma).smul_const (marks i)
  have hnorm (i : s.val.1.ParticleLabels) (z : ℂ)
      (hz : z ∈ Metric.ball w (|w.im| / 2)) :
      ‖(sigma * particleCoefficient (s.val.1.particleLocation i) (z, true)) • marks i‖ ≤ u i := by
    rw [norm_smul, norm_mul]
    have hcoef := particleCoefficient_derivative_ball_bound (s.val.1.particleLocation i) hw hz
    calc
      _ ≤ (‖sigma‖ * (derivativeEnvelope w * nevanlinnaWeight (s.val.1.particleLocation i))) * Real.sqrt B :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcoef (norm_nonneg _)) (hm i)
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (derivativeEnvelope_nonneg _) (nevanlinnaWeight_nonneg _)))
      _ = _ := by dsimp [u]; ring
  have hscoef : Summable fun i : s.val.1.ParticleLabels =>
      ‖sigma * particleCoefficient (s.val.1.particleLocation i) (w, false)‖ ^ 2 := by
    simpa only [norm_mul, mul_pow] using (summable_particleCoefficient_sq s (w, false)).mul_left (‖sigma‖ ^ 2)
  have hsbase := summable_weighted_orthogonal marks _ B horth hB hbound hscoef
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball w _).isPreconnected
    hder hnorm (Metric.mem_ball_self hR) hsbase (Metric.mem_ball_self hR)

end L2
end GeneralizedBulk.Gaussian
