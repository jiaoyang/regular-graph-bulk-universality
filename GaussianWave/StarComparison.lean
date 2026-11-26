import GaussianWave.StarNormalization
import GaussianWave.GaussianProduct
import GaussianWave.GaussianContinuity
import GaussianWave.WeakTransport

/-!
# Eigenvector stars compared at their own eigenvalues

The comparison law is an actual Gaussian measure, with each channel at its
own eigenvalue. It is proved to be a product measure. The principal theorem
concludes convergence in the genuine infimum-over-couplings Wasserstein cost.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GaussianWave.RegularEigenData

variable {d N k : ℕ} (D : GaussianWave.RegularEigenData d N k)

def eigenStarLaw : Measure ((Fin k × Fin (d + 1)) → ℝ) := D.starLaw D.eigenvector

instance eigenStarLaw_isProbability : IsProbabilityMeasure D.eigenStarLaw :=
  D.starLaw_isProbability _

def eigenStarCovariance : Matrix (Fin k × Fin (d + 1)) (Fin k × Fin (d + 1)) ℝ :=
  fun aj bl => (if aj.1 = bl.1 then 1 else 0) *
    starWaveCovariance d (D.eigenvalue aj.1) aj.2 bl.2

theorem eigenStarCovariance_diagonal (i : Fin k × Fin (d + 1)) :
    D.eigenStarCovariance i i = 1 := by
  simp only [eigenStarCovariance, ↓reduceIte, one_mul]
  refine Fin.cases ?_ (fun j => ?_) i.2 <;> simp [starWaveCovariance]

theorem eigenStarCovariance_posSemidef (hd : 2 ≤ d) : D.eigenStarCovariance.PosSemidef := by
  classical
  apply GaussianWave.covariance_posSemidef_of_tendsto (fun _ => D.eigenStarLaw)
    (fun _ => D.integrable_starLaw _ _)
  intro aj bl
  have heq : (∫ x, x aj * x bl ∂D.eigenStarLaw) = D.eigenStarCovariance aj bl :=
    D.integral_star_orthonormal_eigen_covariance hd id Function.injective_id _ _ _ _
  simp_rw [heq]
  exact tendsto_const_nhds

def eigenStarGaussian (hd : 2 ≤ d) : Measure ((Fin k × Fin (d + 1)) → ℝ) :=
  GaussianWave.gaussianCovarianceLaw D.eigenStarCovariance (D.eigenStarCovariance_posSemidef hd)

instance eigenStarGaussian_isProbability (hd : 2 ≤ d) :
    IsProbabilityMeasure (D.eigenStarGaussian hd) := by
  unfold eigenStarGaussian
  infer_instance

theorem eigenStarGaussian_coordinate_fourth (hd : 2 ≤ d) (i : Fin k × Fin (d + 1)) :
    (∫ x, x i ^ 4 ∂D.eigenStarGaussian hd) = 3 := by
  rw [eigenStarGaussian, GaussianWave.gaussianCovarianceLaw_coordinate_fourth,
    D.eigenStarCovariance_diagonal]
  norm_num

theorem eigenStarGaussian_product (hd : 2 ≤ d) :
    ∃ hC : ∀ a : Fin k, (starWaveCovariance d (D.eigenvalue a)).PosSemidef,
      D.eigenStarGaussian hd = Measure.map GaussianWave.flattenChannels
        (Measure.pi (fun a => GaussianWave.gaussianCovarianceLaw
          (starWaveCovariance d (D.eigenvalue a)) (hC a))) := by
  classical
  have hC (a : Fin k) : (starWaveCovariance d (D.eigenvalue a)).PosSemidef := by
    have h := (D.eigenStarCovariance_posSemidef hd).submatrix (fun j => (a, j))
    simpa [eigenStarCovariance, Matrix.submatrix] using h
  refine ⟨hC, ?_⟩
  apply GaussianWave.gaussian_eq_flattened_product _ _ hC
  intro t
  have h := GaussianWave.gaussianCovarianceLaw_characteristic
    D.eigenStarCovariance (D.eigenStarCovariance_posSemidef hd) t
  have heq : D.eigenStarCovariance = GaussianWave.channelBlockCovariance
      (fun a => starWaveCovariance d (D.eigenvalue a)) := by
    ext aj bl
    simp only [eigenStarCovariance, GaussianWave.channelBlockCovariance]
    split_ifs <;> simp
  simpa only [eigenStarGaussian, heq] using h

end GaussianWave.RegularEigenData

namespace GaussianWave

/-- Deterministic nearby-energy eigenvector version of the main theorem.
The comparison at every N uses each eigenvector's own eigenvalue. Fourth
control is exactly the root bound; normalization and independence are outputs. -/
theorem eigenvectors_normalizedStar_wasserstein
    {d k : ℕ} (hd : 2 ≤ d) (N : ℕ → ℕ)
    (D : ∀ n, RegularEigenData d (N n) k)
    (E : ℝ) (hE : ∀ i, Tendsto (fun n => (D n).eigenvalue i) atTop (𝓝 E))
    (M : ℝ) (hM : ∀ n i, (N n : ℝ) * ∑ v, (D n).eigenvector i v ^ 4 ≤ M)
    (BS : BSJointClassification (fun n => (D n).eigenStarLaw)) :
    Tendsto (fun n => wassersteinTwo (D n).eigenStarLaw ((D n).eigenStarGaussian hd))
      atTop (𝓝 0) := by
  classical
  obtain ⟨hC, hw⟩ := eigenvectors_normalizedStar_weakConverges hd N (fun _ => k)
    D (fun _ => id) (fun _ => Function.injective_id) E hE M hM BS
  let C := jointStarCovariance d k E
  have hg : WeakLawConverges (fun n => (D n).eigenStarGaussian hd)
      (gaussianCovarianceLaw C hC) := by
    apply gaussianCovarianceLaw_weakConverges
    intro aj bl
    exact (((RegularEigenData.continuous_starWaveCovariance d aj.2 bl.2).tendsto E).comp
      (hE aj.1)).const_mul _
  have hμ (n : ℕ) := integral_squareMass_sq_le (D n).eigenStarLaw
    (fun aj => (D n).integrable_starLaw _ _) M (fun aj => by
      rw [RegularEigenData.eigenStarLaw, (D n).integral_star_coordinate_fourth]
      exact hM n aj.1)
  have hν (n : ℕ) := integral_squareMass_sq_le ((D n).eigenStarGaussian hd)
    (fun aj => gaussianCovarianceLaw_coordinate_integrable_pow _ _ aj 4) 3
    (fun aj => ((D n).eigenStarGaussian_coordinate_fourth hd aj).le)
  exact wassersteinTwo_tendsto_zero_of_common_weak_limit
    (fun n => (D n).eigenStarLaw) (fun n => (D n).eigenStarGaussian hd)
    (gaussianCovarianceLaw C hC) hw hg
    (fun n => (hμ n).1) (fun n => (hν n).1)
    (M * (Fintype.card (Fin k × Fin (d + 1)) : ℝ) ^ 2)
    (3 * (Fintype.card (Fin k × Fin (d + 1)) : ℝ) ^ 2)
    (fun n => (hμ n).2) (fun n => (hν n).2)

end GaussianWave
