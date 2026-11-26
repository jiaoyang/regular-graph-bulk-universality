import GeneralizedBulk.Graph.StarCovariance
import GeneralizedBulk.Gaussian.UniformIntegrability

/-!
# Normalizing the qualitative BS Gaussian star limit

The covariance comes from the proved finite empirical identities. A uniform
fourth moment, supplied by the entropy argument, prevents covariance loss in
the weak limit. BS itself contributes only qualitative Gaussianity.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace GeneralizedBulk.External.RegularSpectralData

theorem continuous_starWaveCovariance (degree : ℕ) (j l : Fin (degree + 1)) :
    Continuous (fun energy : ℝ => starWaveCovariance degree energy j l) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · refine Fin.cases ?_ (fun l => ?_) l
    · exact continuous_const
    · exact continuous_id.div_const _
  · refine Fin.cases ?_ (fun l => ?_) l
    · exact continuous_id.div_const _
    · by_cases h : j = l
      · simp only [starWaveCovariance, Fin.cases_succ, h, ↓reduceIte]
        exact continuous_const
      · simp only [starWaveCovariance, Fin.cases_succ, h, ↓reduceIte]
        exact ((continuous_id.pow 2).sub continuous_const).div_const _

def jointStarCovariance (d k : ℕ) (energy : ℝ) :
    Matrix (Fin k × Fin (d + 1)) (Fin k × Fin (d + 1)) ℝ :=
  fun aj bl => (if aj.1 = bl.1 then 1 else 0) * starWaveCovariance d energy aj.2 bl.2

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem eigen_tupleResidual {k : ℕ} (n : ℕ) (ω : Ω) (a : Fin k → Fin (N n)) (energy : ℝ) :
    D.tupleResidual n ω (fun i => D.eigenvector n ω (a i)) energy =
      ∑ i, (D.eigenvalue n ω (a i) - energy) ^ 2 := by
  have hs (i : Fin k) : (∑ v, D.eigenvector n ω (a i) v ^ 2) = 1 := by
    simpa only [pow_two, ↓reduceIte] using D.orthonormal n ω (a i) (a i)
  simp only [tupleResidual]
  simp_rw [D.eigen_equation n ω, ← sub_mul, mul_pow, ← Finset.mul_sum, hs, mul_one]

theorem eigen_tupleResidual_tendsto {k : ℕ} (ω : ℕ → Ω)
    (a : ∀ n, Fin k → Fin (N n)) (energy : ℕ → ℝ) (E : ℝ)
    (ha : ∀ i, Tendsto (fun n => D.eigenvalue n (ω n) (a n i)) atTop (𝓝 E))
    (henergy : Tendsto energy atTop (𝓝 E)) :
    Tendsto (fun n => D.tupleResidual n (ω n) (fun i => D.eigenvector n (ω n) (a n i)) (energy n))
      atTop (𝓝 0) := by
  simp_rw [D.eigen_tupleResidual]
  have h := tendsto_finset_sum Finset.univ (fun i hi => ((ha i).sub henergy).pow 2)
  simpa only [sub_self, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] using h

/-- Actual finite-star covariance and uniform fourth moments identify the
joint Gaussian limit, including independence of distinct eigenchannels. -/
theorem starGaussian_normalized_characteristic {k : ℕ} (hd : 2 ≤ d)
    (ω : ℕ → Ω) (a : ∀ n, Fin k → Fin (N n)) (hinj : ∀ n, Function.Injective (a n))
    (E : ℝ) (hEig : ∀ i, Tendsto (fun n => D.eigenvalue n (ω n) (a n i)) atTop (𝓝 E))
    (ν : Measure ((Fin k × Fin (d + 1)) → ℝ))
    (hweak : WeakLawConverges (fun n => D.starLaw n (ω n)
      (fun i => D.eigenvector n (ω n) (a n i))) ν)
    (hGaussian : CenteredGaussianLaw ν)
    (M : ℝ) (hM : ∀ n, (∫ x, ‖x‖ ^ 4 ∂D.starLaw n (ω n)
      (fun i => D.eigenvector n (ω n) (a n i))) ≤ M) :
    ∀ t : (Fin k × Fin (d + 1)) → ℝ,
      (∫ x, Complex.exp ((↑(Gaussian.finiteLinearForm t x) : ℂ) * Complex.I) ∂ν) =
        Complex.exp (↑(-(1 / 2 : ℝ) * Gaussian.finiteCovarianceQuadratic (jointStarCovariance d k E) t) : ℂ) := by
  let μ := fun n => D.starLaw n (ω n) (fun i => D.eigenvector n (ω n) (a n i))
  letI : ∀ n, IsProbabilityMeasure (μ n) := fun n => D.starLaw_isProbability n (ω n) _
  apply Gaussian.no_covariance_loss_of_norm_fourth μ ν hweak hGaussian (jointStarCovariance d k E)
    (fun n => D.integrable_starLaw n (ω n) _ (fun x => ‖x‖ ^ 4)) M hM
  intro aj bl
  have heq (n : ℕ) : (∫ x, x aj * x bl ∂μ n) =
      (if aj.1 = bl.1 then 1 else 0) *
        starWaveCovariance d (D.eigenvalue n (ω n) (a n aj.1)) aj.2 bl.2 :=
    D.integral_star_orthonormal_eigen_covariance n (ω n) hd (a n) (hinj n) aj.1 bl.1 aj.2 bl.2
  simp_rw [heq]
  exact (((continuous_starWaveCovariance d aj.2 bl.2).tendsto E).comp (hEig aj.1)).const_mul _

/-- A source-faithful BS hypothesis becomes the normalized joint Gaussian
statement only after exact finite normalization and fourth-moment control. -/
theorem BS_normalized_star_characteristic {k : ℕ} (hk : 0 < k)
    (P : Measure Ω) [IsProbabilityMeasure P] (K : Set ℝ)
    (BS : BSQualitativeInput D P K) (ω : ℕ → Ω)
    (hgood : ∀ᶠ n in atTop, ω n ∈ BS.good k n)
    (a : ∀ n, Fin k → Fin (N n)) (hinj : ∀ n, Function.Injective (a n))
    (hnonconstant : ∀ n i, a n i ≠ ⟨0, D.size_pos n⟩)
    (energy : ℕ → ℝ) (hbulk : ∀ᶠ n in atTop, energy n ∈ K)
    (E : ℝ) (hE : E ∈ K) (henergy : Tendsto energy atTop (𝓝 E))
    (hEig : ∀ i, Tendsto (fun n => D.eigenvalue n (ω n) (a n i)) atTop (𝓝 E))
    (ν : Measure ((Fin k × Fin (d + 1)) → ℝ))
    (hweak : WeakLawConverges (fun n => D.starLaw n (ω n)
      (fun i => D.eigenvector n (ω n) (a n i))) ν)
    (M : ℝ) (hM : ∀ n, (∫ x, ‖x‖ ^ 4 ∂D.starLaw n (ω n)
      (fun i => D.eigenvector n (ω n) (a n i))) ≤ M) :
    ∀ t : (Fin k × Fin (d + 1)) → ℝ,
      (∫ x, Complex.exp ((↑(Gaussian.finiteLinearForm t x) : ℂ) * Complex.I) ∂ν) =
        Complex.exp (↑(-(1 / 2 : ℝ) * Gaussian.finiteCovarianceQuadratic (jointStarCovariance d k E) t) : ℂ) := by
  have hcentered : ∀ᶠ n in atTop, ∀ i : Fin k,
      (∑ v, D.eigenvector n (ω n) (a n i) v) = 0 :=
    Eventually.of_forall (fun n i => D.eigenvector_sum_zero n (ω n) (a n i) (hnonconstant n i))
  have horth : ∀ᶠ n in atTop, ∀ i j : Fin k,
      (∑ v, D.eigenvector n (ω n) (a n i) v * D.eigenvector n (ω n) (a n j) v) =
        if i = j then 1 else 0 := by
    apply Eventually.of_forall
    intro n i j
    simpa only [(hinj n).eq_iff] using D.orthonormal n (ω n) (a n i) (a n j)
  have hGauss := BS.gaussian_limit k hk ω hgood
    (fun n i => D.eigenvector n (ω n) (a n i)) energy hbulk hcentered horth
    (D.eigen_tupleResidual_tendsto ω a energy E hEig henergy) E hE henergy id strictMono_id ν hweak
  have hdegree := BS.degree_ge_three
  exact D.starGaussian_normalized_characteristic (by omega) ω a hinj E hEig ν hweak hGauss M hM

end GeneralizedBulk.External.RegularSpectralData
