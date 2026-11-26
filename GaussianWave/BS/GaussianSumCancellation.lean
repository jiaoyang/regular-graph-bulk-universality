import GaussianWave.BS.WhitenedGaussianSum
import GaussianWave.BS.GaussianDeconvolution
import GaussianWave.BS.ProcessBallMarginals
import GaussianWave.BS.ChannelSupportReduction
import GaussianWave.TwoEdgeGaussian

/-! Removing the actual independent Gaussian wave after classification of
the whitened sum. Covariance is the source's actual second-moment matrix;
no preservation of the original graph variance is assumed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

theorem centeredGaussian_of_independent_sum {I : Type*} [Fintype I] [DecidableEq I]
    (μ ν : Measure (I → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (squareRadius (I := I)) μ)
    (hν : Integrable (squareRadius (I := I)) ν) (hmean : ∀ i,(∫ x,x i ∂ν)=0)
    (S D : Matrix I I ℝ) (hS : S.PosSemidef) (hD : D.PosSemidef)
    (hνG : HasGaussianCovariance ν S) (hsum : HasGaussianCovariance (independentAddLaw μ ν 1) D) :
    CenteredGaussianLaw μ := by
  let C := actualSecondMomentMatrix μ
  have hC : C.PosSemidef := actualSecondMomentMatrix_posSemidef μ
    (integrable_coordinate_mul_of_squareRadius μ hμ)
  have hμM : HasSecondMoments μ C := fun _ _ => rfl
  have hsumM := independentAddLaw_secondMoments μ ν hμ hν hmean C S hμM
    (gaussian_hasSecondMoments ν S hS hνG)
  have hDM := gaussian_hasSecondMoments (independentAddLaw μ ν 1) D hD hsum
  have hDeq : D=C+S := by
    ext i j
    exact (hDM i j).symm.trans (hsumM i j)
  rw [hDeq] at hsum
  have hG := hasGaussianCovariance_of_independent_gaussian_addition μ ν C S hνG hsum
  refine ⟨inferInstance,C,?_,finiteCovarianceQuadratic_nonneg_of_posSemidef C hC,hG⟩
  intro i j
  have hh := congrArg (fun M => M j i) hC.1
  simpa only [Matrix.conjTranspose_apply,star_trivial] using hh

theorem channelProcessMap_one {r d : ℕ} (x : (Fin r × RegularTreeVertex d) → ℝ) :
    channelProcessMap (1 : Matrix (Fin r) (Fin r) ℝ) x=x := by
  funext ⟨a,v⟩
  change (1 : Matrix (Fin r) (Fin r) ℝ).mulVec (fun b => x (b,v)) a=x (a,v)
  rw [Matrix.one_mulVec]

theorem positiveRootFactor_rightInverse {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (hC : C.PosSemidef) :
    positiveRootFactor C hC*positiveRootWhitening C hC=1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (positiveRootFactor_det_ne_zero C hC))

theorem gaussianSum_recover_from_whitening {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (energy : ℝ) :
    Measure.map (channelProcessMap (positiveRootFactor (treeRootCovariance μ) (treeRootCovariance_posSemidef μ hi)))
      (whitenedGaussianSumLaw μ hi energy)=independentTreeSumLaw μ (jointGaussianTreeProcessLaw r m energy) := by
  rw [whitenedGaussianSumLaw,Measure.map_map (continuous_channelProcessMap _).measurable
    (continuous_channelProcessMap _).measurable]
  have he : channelProcessMap (d := m+2) (positiveRootFactor (treeRootCovariance μ) (treeRootCovariance_posSemidef μ hi)) ∘
      channelProcessMap (positiveRootWhitening (treeRootCovariance μ) (treeRootCovariance_posSemidef μ hi))=id := by
    funext x
    rw [Function.comp_apply,channelProcessMap_mul,positiveRootFactor_rightInverse,channelProcessMap_one]
    rfl
  rw [he,Measure.map_id]

theorem jointTreeWindow_channelProcessMap_law {r s d : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ)) (A : Matrix (Fin s) (Fin r) ℝ)
    (site : J → RegularTreeVertex d) :
    Measure.map (jointTreeWindow site) (Measure.map (channelProcessMap A) μ)=
      Measure.map (channelLift A J).mulVec (Measure.map (jointTreeWindow site) μ) := by
  rw [Measure.map_map (measurable_jointTreeWindow _) (continuous_channelProcessMap _).measurable,
    Measure.map_map (measurable_finiteMatrixAction _) (measurable_jointTreeWindow _)]
  congr 1
  funext x ⟨a,j⟩
  exact (channelLift_mulVec A (jointTreeWindow site x) a j).symm

theorem integrable_squareRadius_jointTreeWindow_for_cancellation {r d : ℕ} {J : Type*} [Fintype J]
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (site : J → RegularTreeVertex d) :
    Integrable (squareRadius (I := Fin r × J)) (Measure.map (jointTreeWindow site) μ) := by
  unfold squareRadius
  apply integrable_finset_sum
  intro aj _
  apply (integrable_map_measure ((measurable_pi_apply aj).pow_const 2).aestronglyMeasurable
    (measurable_jointTreeWindow _).aemeasurable).mpr
  exact hi (aj.1,site aj.2)

theorem jointGaussianTreeProcessLaw_window_covariance_posSemidef
    (r m : ℕ) (energy : ℝ) (he : |energy|<(m+2 : ℝ))
    {J : Type*} [Fintype J] [DecidableEq J] (site : J → RegularTreeVertex (m+2)) :
    (channelBlockCovariance (fun _ : Fin r => fun i j : J => sphericalCovariance (m+2) energy
      ((regularWordTree (m+2)).dist (site i) (site j)))).PosSemidef := by
  obtain ⟨K,hK,L,hL,hGram⟩ := gaussianTreeProcessLaw_finite_waveFactor m energy he site
  letI := hK
  apply channelBlockCovariance_posSemidef
  intro a
  rw [← hGram]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose L

theorem finiteGaussian_of_classified_whitened_sum {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (energy : ℝ) (he : |energy|<(m+2 : ℝ))
    (hclass : whitenedGaussianSumLaw μ hi energy=jointGaussianTreeProcessLaw r m energy)
    {J : Type*} [Fintype J] [DecidableEq J] (site : J → RegularTreeVertex (m+2)) :
    CenteredGaussianLaw (Measure.map (jointTreeWindow site) μ) := by
  let G := jointGaussianTreeProcessLaw r m energy
  let W := jointTreeWindow (r := r) site
  let ν := Measure.map W G
  let ρ := Measure.map W μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map (measurable_jointTreeWindow _).aemeasurable
  letI : IsProbabilityMeasure ρ := isProbabilityMeasure_map (measurable_jointTreeWindow _).aemeasurable
  let S := channelBlockCovariance (fun _ : Fin r => fun i j : J => sphericalCovariance (m+2) energy
    ((regularWordTree (m+2)).dist (site i) (site j)))
  have hS : S.PosSemidef := jointGaussianTreeProcessLaw_window_covariance_posSemidef r m energy he site
  have hν : HasGaussianCovariance ν S := jointGaussianTreeProcessLaw_finite_wave_kernel r m energy he site
  let A := positiveRootFactor (treeRootCovariance μ) (treeRootCovariance_posSemidef μ hi)
  let R := channelLift A J
  have hD : (R*S*R.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.mul_mul_conjTranspose_same R
  have hsumlaw : independentAddLaw ρ ν 1=Measure.map R.mulVec ν := by
    change independentAddLaw
      (Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun aj : Fin r × J => z (aj.1,site aj.2)) μ)
      (Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun aj : Fin r × J => z (aj.1,site aj.2)) G) 1=_
    rw [← independentTreeSumLaw_window μ G site]
    change Measure.map (jointTreeWindow site) (independentTreeSumLaw μ G)=_
    rw [← gaussianSum_recover_from_whitening μ hi energy,hclass,jointTreeWindow_channelProcessMap_law]
  have hsum : HasGaussianCovariance (independentAddLaw ρ ν 1) (R*S*R.transpose) := by
    rw [hsumlaw]
    exact hν.linearImage R
  have hmean (aj : Fin r × J) : (∫ x,x aj ∂ν)=0 := by
    dsimp only [ν]
    rw [integral_map (measurable_jointTreeWindow _).aemeasurable (measurable_pi_apply aj).aestronglyMeasurable]
    exact jointGaussianTreeProcessLaw_mean_zero r m energy he aj.1 (site aj.2)
  exact centeredGaussian_of_independent_sum ρ ν (integrable_squareRadius_jointTreeWindow_for_cancellation μ hi site)
    (integrable_squareRadius_jointTreeWindow_for_cancellation G (jointGaussianTreeProcessLaw_coordinate_integrable_square r m energy he) site)
    hmean S (R*S*R.transpose) hS hD hν hsum

end GaussianWave.BS
