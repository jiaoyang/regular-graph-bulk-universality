import GaussianWave.BS.GaussianSecondMoments
import GaussianWave.BS.InvariantEigenCovariance
import GaussianWave.BS.ProcessBallMarginals

/-! Qualitative finite Gaussianity identifies the exact common-energy wave
kernel, with the source's actual root covariance and possible variance loss. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

theorem centeredGaussianLaw_actual_secondMoments {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) (hG : CenteredGaussianLaw μ) :
    (actualSecondMomentMatrix μ).PosSemidef ∧ HasGaussianCovariance μ (actualSecondMomentMatrix μ) := by
  letI := hG.1
  obtain ⟨C,hs,hp,hCF⟩ := hG.2
  have hC : C.PosSemidef := by
    constructor
    · ext i j
      simpa only [Matrix.conjTranspose_apply,star_trivial] using hs j i
    · intro t
      simpa only [finiteCovarianceQuadratic,Matrix.mulVec,dotProduct,Pi.star_apply,
        star_trivial,Finset.mul_sum,mul_assoc] using hp t
  have hM := gaussian_hasSecondMoments μ C hC hCF
  have hEq : actualSecondMomentMatrix μ=C := by
    ext i j
    exact hM i j
  rw [hEq]
  exact ⟨hC,hCF⟩

def treeWaveWindowCovariance {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) (energy : ℝ)
    {J : Type*} (site : J → RegularTreeVertex (m+2)) : Matrix (Fin r × J) (Fin r × J) ℝ :=
  fun ai bj => treeRootCovariance μ ai.1 bj.1*sphericalCovariance (m+2) energy
    ((regularWordTree (m+2)).dist (site ai.2) (site bj.2))

theorem actualSecondMomentMatrix_treeWindow {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hμ : ChannelTreeInvariant μ) (hi : ∀ av,Integrable (fun x => x av^2) μ)
    (energy : ℝ)
    (hE : ∀ a v,∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) a v x=0)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2)) :
    actualSecondMomentMatrix (Measure.map (jointTreeWindow site) μ)=treeWaveWindowCovariance μ energy site := by
  ext ⟨a,i⟩ ⟨b,j⟩
  rw [actualSecondMomentMatrix,integral_map (measurable_jointTreeWindow _).aemeasurable
    (((continuous_apply (a,i)).mul (continuous_apply (b,j))).measurable.aestronglyMeasurable)]
  exact treeMixedMoment_eq_spherical μ hμ hi energy hE a b (site i) (site j)

theorem finite_gaussian_eigenprocess_wave_covariance {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hμ : ChannelTreeInvariant μ) (hi : ∀ av,Integrable (fun x => x av^2) μ)
    (energy : ℝ)
    (hE : ∀ a v,∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) a v x=0)
    {J : Type*} [Fintype J] [DecidableEq J] (site : J → RegularTreeVertex (m+2))
    (hG : CenteredGaussianLaw (Measure.map (jointTreeWindow site) μ)) :
    (treeWaveWindowCovariance μ energy site).PosSemidef ∧
      HasGaussianCovariance (Measure.map (jointTreeWindow site) μ) (treeWaveWindowCovariance μ energy site) := by
  have h := centeredGaussianLaw_actual_secondMoments _ hG
  rw [actualSecondMomentMatrix_treeWindow μ hμ hi energy hE site] at h
  exact h

end GaussianWave.BS
