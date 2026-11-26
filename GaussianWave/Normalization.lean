import GaussianWave.GaussianLaws
import GaussianWave.Compactness

/-! Uniform fourth moments plus the qualitative BS classification identify all
subsequential laws and prove actual weak convergence. The subsequence exists by
a proved compactness theorem, not by an extra hypothesis. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GaussianWave

theorem weakLaw_of_gaussian_subsequence_characterization
    {ι : Type*} [Fintype ι] (μ : ℕ → Measure (ι → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν]
    (target : Matrix ι ι ℝ)
    (hν : ∀ t : ι → ℝ,
      (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂ν) =
        Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic target t) : ℂ))
    (hi : ∀ n, Integrable (fun x => ‖x‖ ^ 4) (μ n)) (M : ℝ)
    (hM : ∀ n, (∫ x, ‖x‖ ^ 4 ∂μ n) ≤ M)
    (hsecond : ∀ i j, Tendsto (fun n => ∫ x, x i * x j ∂μ n) atTop (𝓝 (target i j)))
    (hGaussian : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ ρ : ProbabilityMeasure (ι → ℝ),
      WeakLawConverges (fun n => μ (φ n)) (ρ : Measure (ι → ℝ)) →
        CenteredGaussianLaw (ρ : Measure (ι → ℝ))) :
    WeakLawConverges μ ν := by
  intro F
  apply tendsto_of_subseq_tendsto
  intro r hr
  obtain ⟨t, ht, hrt⟩ := strictMono_subseq_of_tendsto_atTop hr
  let laws : ℕ → ProbabilityMeasure (ι → ℝ) := fun n => ⟨μ (r (t n)), inferInstance⟩
  obtain ⟨ρ, s, hs, hconv⟩ := finite_laws_subsequence_of_uniform_norm_fourth laws
    (fun n => hi (r (t n))) M (fun n => hM (r (t n)))
  let φ := r ∘ t ∘ s
  have hφ : StrictMono φ := hrt.comp hs
  have hweak : WeakLawConverges (fun n => μ (φ n)) (ρ : Measure (ι → ℝ)) := by
    intro G
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv G
  have hcf := no_covariance_loss_of_norm_fourth (fun n => μ (φ n)) (ρ : Measure (ι → ℝ))
    hweak (hGaussian φ hφ ρ hweak) target (fun n => hi (φ n)) M (fun n => hM (φ n))
    (fun i j => (hsecond i j).comp hφ.tendsto_atTop)
  have heq : (ρ : Measure (ι → ℝ)) = ν := by
    apply measure_eq_of_linear_characteristic
    intro a
    exact (hcf a).trans (hν a).symm
  refine ⟨t ∘ s, ?_⟩
  have h := hweak F
  rw [heq] at h
  exact h


/-- An entrywise limit of actual second-moment matrices is positive
semidefinite. This is proved, rather than assumed of the target covariance. -/
theorem covariance_posSemidef_of_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ℕ → Measure (ι → ℝ)) [∀ n, IsProbabilityMeasure (μ n)]
    (h4 : ∀ n, Integrable (fun x => ‖x‖ ^ 4) (μ n))
    (C : Matrix ι ι ℝ)
    (hsecond : ∀ i j, Tendsto (fun n => ∫ x, x i * x j ∂μ n) atTop (𝓝 (C i j))) :
    C.PosSemidef := by
  constructor
  · change C.conjTranspose = C
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    apply tendsto_nhds_unique (hsecond j i)
    simpa only [mul_comm] using hsecond i j
  · intro t
    have hlim := tendsto_finset_sum Finset.univ (fun i hi =>
      tendsto_finset_sum Finset.univ (fun j hj =>
        ((hsecond i j).const_mul (t i)).mul_const (t j)))
    have hp : Tendsto (fun n => ∫ x, finiteLinearForm t x ^ 2 ∂μ n)
        atTop (𝓝 (finiteCovarianceQuadratic C t)) := by
      simpa only [integral_finiteLinearForm_sq (μ _) t
        (integrable_coord_product_of_norm_fourth (μ _) (h4 _)), finiteCovarianceQuadratic]
        using hlim
    have hn : 0 ≤ finiteCovarianceQuadratic C t :=
      ge_of_tendsto hp (Eventually.of_forall (fun n => integral_nonneg (fun x => sq_nonneg _)))
    simpa only [finiteCovarianceQuadratic, star_trivial, dotProduct,
      Matrix.mulVec, Finset.mul_sum, mul_assoc] using hn

/-- Main deterministic normalization theorem for arbitrary fixed finite
windows. Only qualitative Gaussian classification of subsequential limits is
imported; fourth control, tightness, covariance preservation, and identification
of the actual Gaussian probability law are proved inside this project. -/
theorem normalizedGaussian_weakConverges
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ℕ → Measure (ι → ℝ)) [∀ n, IsProbabilityMeasure (μ n)]
    (h4 : ∀ n i, Integrable (fun x => x i ^ 4) (μ n))
    (M : ℝ) (hM : ∀ n i, (∫ x, x i ^ 4 ∂μ n) ≤ M)
    (C : Matrix ι ι ℝ)
    (hsecond : ∀ i j, Tendsto (fun n => ∫ x, x i * x j ∂μ n) atTop (𝓝 (C i j)))
    (BS : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ ρ : ProbabilityMeasure (ι → ℝ),
      WeakLawConverges (fun n => μ (φ n)) (ρ : Measure (ι → ℝ)) →
        CenteredGaussianLaw (ρ : Measure (ι → ℝ))) :
    ∃ hC : C.PosSemidef, WeakLawConverges μ (gaussianCovarianceLaw C hC) := by
  have hi (n : ℕ) := (integral_pi_norm_fourth_le (μ n) (h4 n) M (hM n)).1
  have hb (n : ℕ) := (integral_pi_norm_fourth_le (μ n) (h4 n) M (hM n)).2
  have hC := covariance_posSemidef_of_tendsto μ hi C hsecond
  refine ⟨hC, ?_⟩
  exact weakLaw_of_gaussian_subsequence_characterization μ (gaussianCovarianceLaw C hC)
    C (gaussianCovarianceLaw_characteristic C hC) hi
    (M * (Fintype.card ι : ℝ) ^ 2) hb hsecond BS

end GaussianWave
