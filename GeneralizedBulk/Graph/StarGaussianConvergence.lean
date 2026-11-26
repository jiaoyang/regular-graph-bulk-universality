import GeneralizedBulk.Analysis.FiniteDimensionalSubsequence
import GeneralizedBulk.Gaussian.StarLaw

/-!
# Actual weak convergence of finite empirical Gaussian stars

Fourth moments yield tightness and an actual weak subsequence. Qualitative BS
Gaussianity and the exact empirical covariance then identify every subsequence
limit with the constructed Gaussian star law. No weak-limit existence or
normalized Gaussian-limit conclusion is assumed.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators

namespace GeneralizedBulk.Gaussian

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
      External.WeakLawConverges (fun n => μ (φ n)) (ρ : Measure (ι → ℝ)) →
        External.CenteredGaussianLaw (ρ : Measure (ι → ℝ))) :
    External.WeakLawConverges μ ν := by
  intro F
  apply tendsto_of_subseq_tendsto
  intro r hr
  obtain ⟨t, ht, hrt⟩ := strictMono_subseq_of_tendsto_atTop hr
  let laws : ℕ → ProbabilityMeasure (ι → ℝ) := fun n => ⟨μ (r (t n)), inferInstance⟩
  obtain ⟨ρ, s, hs, hconv⟩ := Analysis.finite_laws_subsequence_of_uniform_norm_fourth laws
    (fun n => hi (r (t n))) M (fun n => hM (r (t n)))
  let φ := r ∘ t ∘ s
  have hφ : StrictMono φ := hrt.comp hs
  have hweak : External.WeakLawConverges (fun n => μ (φ n)) (ρ : Measure (ι → ℝ)) := by
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

end GeneralizedBulk.Gaussian

namespace GeneralizedBulk.External.RegularSpectralData

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem BS_bulk_abs_lt_degree (P : Measure Ω) [IsProbabilityMeasure P] (K : Set ℝ)
    (BS : BSQualitativeInput D P K) (E : ℝ) (hE : E ∈ K) : |E| < d := by
  have hd : (3 : ℝ) ≤ d := by exact_mod_cast BS.degree_ge_three
  have hs : Real.sqrt ((d : ℝ) - 1) ^ 2 = (d : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hs0 := Real.sqrt_nonneg ((d : ℝ) - 1)
  have htree : 2 * Real.sqrt ((d : ℝ) - 1) ≤ d := by
    by_contra h
    have hneg : (d : ℝ) - 2 * Real.sqrt ((d : ℝ) - 1) < 0 := by linarith
    have hp := mul_neg_of_neg_of_pos hneg (by linarith : 0 < (d : ℝ) + 2 * Real.sqrt ((d : ℝ) - 1))
    nlinarith [sq_nonneg ((d : ℝ) - 2)]
  exact (BS.compact_bulk.2 E hE).trans_le htree

/-- Finite empirical stars actually converge weakly to the constructed
normalized independent-channel Gaussian star law. The fourth moment is an
explicit analytic input for the entropy argument, and BS stays qualitative. -/
theorem BS_starLaw_weakConverges {k : ℕ} (hk : 0 < k)
    (P : Measure Ω) [IsProbabilityMeasure P] (K : Set ℝ)
    (BS : BSQualitativeInput D P K) (ω : ℕ → Ω)
    (hgood : ∀ᶠ n in atTop, ω n ∈ BS.good k n)
    (a : ∀ n, Fin k → Fin (N n)) (hinj : ∀ n, Function.Injective (a n))
    (hnonconstant : ∀ n i, a n i ≠ ⟨0, D.size_pos n⟩)
    (energy : ℕ → ℝ) (hbulk : ∀ᶠ n in atTop, energy n ∈ K)
    (E : ℝ) (hE : E ∈ K) (henergy : Tendsto energy atTop (𝓝 E))
    (hEig : ∀ i, Tendsto (fun n => D.eigenvalue n (ω n) (a n i)) atTop (𝓝 E))
    (M : ℝ) (hM : ∀ n, (∫ x, ‖x‖ ^ 4 ∂D.starLaw n (ω n)
      (fun i => D.eigenvector n (ω n) (a n i))) ≤ M) :
    WeakLawConverges (fun n => D.starLaw n (ω n) (fun i => D.eigenvector n (ω n) (a n i)))
      (Gaussian.jointStarGaussianLaw d k (by have h := BS.degree_ge_three; omega) E) := by
  have hdegree : 2 ≤ d := by have h := BS.degree_ge_three; omega
  let μ := fun n => D.starLaw n (ω n) (fun i => D.eigenvector n (ω n) (a n i))
  letI : ∀ n, IsProbabilityMeasure (μ n) := fun n => D.starLaw_isProbability n (ω n) _
  apply Gaussian.weakLaw_of_gaussian_subsequence_characterization μ
    (Gaussian.jointStarGaussianLaw d k hdegree E) (jointStarCovariance d k E)
    (Gaussian.jointStarGaussianLaw_characteristic d k hdegree E (D.BS_bulk_abs_lt_degree P K BS E hE))
    (fun n => D.integrable_starLaw n (ω n) _ (fun x => ‖x‖ ^ 4)) M hM
  · intro aj bl
    have heq (n : ℕ) : (∫ x, x aj * x bl ∂μ n) =
        (if aj.1 = bl.1 then 1 else 0) *
          starWaveCovariance d (D.eigenvalue n (ω n) (a n aj.1)) aj.2 bl.2 :=
      D.integral_star_orthonormal_eigen_covariance n (ω n) hdegree (a n) (hinj n) aj.1 bl.1 aj.2 bl.2
    simp_rw [heq]
    exact (((continuous_starWaveCovariance d aj.2 bl.2).tendsto E).comp (hEig aj.1)).const_mul _
  · intro φ hφ ρ hweak
    have hcentered : ∀ᶠ n in atTop, ∀ i : Fin k,
        (∑ v, D.eigenvector n (ω n) (a n i) v) = 0 :=
      Eventually.of_forall (fun n i => D.eigenvector_sum_zero n (ω n) (a n i) (hnonconstant n i))
    have horth : ∀ᶠ n in atTop, ∀ i j : Fin k,
        (∑ v, D.eigenvector n (ω n) (a n i) v * D.eigenvector n (ω n) (a n j) v) =
          if i = j then 1 else 0 := by
      apply Eventually.of_forall
      intro n i j
      simpa only [(hinj n).eq_iff] using D.orthonormal n (ω n) (a n i) (a n j)
    exact BS.gaussian_limit k hk ω hgood
      (fun n i => D.eigenvector n (ω n) (a n i)) energy hbulk hcentered horth
      (D.eigen_tupleResidual_tendsto ω a energy E hEig henergy) E hE henergy φ hφ ρ hweak

end GeneralizedBulk.External.RegularSpectralData
