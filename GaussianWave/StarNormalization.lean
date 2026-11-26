import GaussianWave.Covariance
import GaussianWave.Normalization

/-!
# The normalized eigenvector-star theorem

This is the deterministic sequence-of-good-graphs part of the research note.
The only Gaussianity hypothesis is the qualitative BS classification, with
unspecified covariance. The required fourth input is literally the empirical
root moment N * sum u(v)^4. There is no prescribed star covariance hypothesis.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GaussianWave

def jointStarCovariance (d k : ℕ) (E : ℝ) :
    Matrix (Fin k × Fin (d + 1)) (Fin k × Fin (d + 1)) ℝ :=
  fun aj bl => (if aj.1 = bl.1 then 1 else 0) *
    RegularEigenData.starWaveCovariance d E aj.2 bl.2

/-- The precise qualitative imported input along a sequence of good graphs:
each existing weak subsequential limit is centered Gaussian, with covariance
left existential. Neither variance one nor independence is an input. -/
def BSJointClassification {ι : Type*} [Fintype ι]
    (μ : ℕ → Measure (ι → ℝ)) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → ∀ ρ : ProbabilityMeasure (ι → ℝ),
    WeakLawConverges (fun n => μ (φ n)) (ρ : Measure (ι → ℝ)) →
      CenteredGaussianLaw (ρ : Measure (ι → ℝ))

/-- Exact finite-star covariance, scalar fourth bounds, and only the
qualitative BS input imply convergence to the normalized Gaussian star law. -/
theorem eigenvectors_normalizedStar_weakConverges
    {d k : ℕ} (hd : 2 ≤ d) (N c : ℕ → ℕ)
    (D : ∀ n, RegularEigenData d (N n) (c n))
    (a : ∀ n, Fin k → Fin (c n)) (ha : ∀ n, Function.Injective (a n))
    (E : ℝ) (hE : ∀ i, Tendsto (fun n => (D n).eigenvalue (a n i)) atTop (𝓝 E))
    (M : ℝ) (hM : ∀ n i, (N n : ℝ) *
      ∑ v, (D n).eigenvector (a n i) v ^ 4 ≤ M)
    (BS : BSJointClassification (fun n =>
      (D n).starLaw (fun i => (D n).eigenvector (a n i)))) :
    ∃ hC : (jointStarCovariance d k E).PosSemidef,
      WeakLawConverges (fun n => (D n).starLaw (fun i => (D n).eigenvector (a n i)))
        (gaussianCovarianceLaw (jointStarCovariance d k E) hC) := by
  classical
  let μ := fun n => (D n).starLaw (fun i => (D n).eigenvector (a n i))
  letI : ∀ n, IsProbabilityMeasure (μ n) := fun n => (D n).starLaw_isProbability _
  apply normalizedGaussian_weakConverges μ
    (fun n aj => (D n).integrable_starLaw _ _) M ?_ (jointStarCovariance d k E) ?_ BS
  · intro n aj
    change (∫ x, x aj ^ 4 ∂(D n).starLaw (fun i => (D n).eigenvector (a n i))) ≤ M
    rw [(D n).integral_star_coordinate_fourth]
    exact hM n aj.1
  · intro aj bl
    have heq (n : ℕ) : (∫ x, x aj * x bl ∂μ n) =
        (if aj.1 = bl.1 then 1 else 0) *
          RegularEigenData.starWaveCovariance d ((D n).eigenvalue (a n aj.1)) aj.2 bl.2 :=
      (D n).integral_star_orthonormal_eigen_covariance hd (a n) (ha n) _ _ _ _
    simp_rw [heq]
    exact (((RegularEigenData.continuous_starWaveCovariance d aj.2 bl.2).tendsto E).comp
      (hE aj.1)).const_mul _

end GaussianWave
