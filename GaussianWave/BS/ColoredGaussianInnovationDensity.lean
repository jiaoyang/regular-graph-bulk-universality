import GaussianWave.BS.IndependentLawSplit
import GaussianWave.BS.InnovationRelativeSSA

/-! Positive density witnesses and actual layer splitting for the full
independent-channel Gaussian reference. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

def PositiveEntropyDensity.independentChannels {I : Type*} [Fintype I]
    (p : PositiveEntropyDensity (volume : Measure (I → ℝ))) (κ : Type*) [Fintype κ] :
    PositiveEntropyDensity (volume : Measure ((κ × I) → ℝ)) :=
  (p.iid κ).transport (curryBlocksEquiv κ I ℝ).symm
    (by simpa only [volume_pi] using
      (measurePreserving_curryBlocks (A := κ) (B := I) (volume : Measure ℝ)).symm)

@[simp] theorem PositiveEntropyDensity.independentChannels_law {I : Type*} [Fintype I]
    (p : PositiveEntropyDensity (volume : Measure (I → ℝ))) (κ : Type*) [Fintype κ] :
    (p.independentChannels κ).law = independentChannelLaw (fun _ : κ => p.law) := by
  rw [PositiveEntropyDensity.independentChannels, PositiveEntropyDensity.transport_law,
    PositiveEntropyDensity.iid_law]
  rfl

def jointForestGaussianPositiveDensity {A : Type*} [Fintype A] [DecidableEq A]
    (κ : Type*) [Fintype κ] (m k : ℕ) (scale : ℝ) (hs : scale ≠ 0)
    (R : Matrix A A ℝ) (hR : Function.Surjective R.mulVec) :=
  (forestGaussianPositiveDensity m k scale hs R hR).independentChannels κ

def jointNewBranchGaussianPositiveDensity (κ : Type*) [Fintype κ]
    (m k : ℕ) (scale : ℝ) (hs : scale ≠ 0) :=
  (newBranchGaussianPositiveDensity m k scale hs).independentChannels κ

@[simp] theorem jointForestGaussianPositiveDensity_law {A : Type*} [Fintype A] [DecidableEq A]
    (κ : Type*) [Fintype κ] (m k : ℕ) (scale : ℝ) (hs : scale ≠ 0)
    (R : Matrix A A ℝ) (hR : Function.Surjective R.mulVec) :
    (jointForestGaussianPositiveDensity κ m k scale hs R hR).law =
      independentChannelLaw (fun _ : κ => forestGaussianInnovationLaw m k scale R) := by
  simp only [jointForestGaussianPositiveDensity, PositiveEntropyDensity.independentChannels_law,
    forestGaussianPositiveDensity_law]

@[simp] theorem jointNewBranchGaussianPositiveDensity_law (κ : Type*) [Fintype κ]
    (m k : ℕ) (scale : ℝ) (hs : scale ≠ 0) :
    (jointNewBranchGaussianPositiveDensity κ m k scale hs).law =
      independentChannelLaw (fun _ : κ => newBranchGaussianLaw m k scale) := by
  simp only [jointNewBranchGaussianPositiveDensity, PositiveEntropyDensity.independentChannels_law,
    newBranchGaussianPositiveDensity_law]

theorem innovationReferenceFull_jointGaussian_law {κ A : Type*}
    [Fintype κ] [Fintype A] [DecidableEq A] [DecidableEq κ]
    (m k : ℕ) (scale : ℝ) (hs : scale ≠ 0)
    (R : Matrix A A ℝ) (hR : Function.Surjective R.mulVec) :
    (innovationReferenceFull (coloredForestSplit κ A m k)
      (jointForestGaussianPositiveDensity κ m k scale hs R hR)
      (jointNewBranchGaussianPositiveDensity κ m k scale hs)).law =
      independentChannelLaw (fun _ : κ => forestGaussianInnovationLaw m (k + 1) scale R) := by
  rw [innovationReferenceFull, PositiveEntropyDensity.transport_law,
    PositiveEntropyDensity.prod_law, PositiveEntropyDensity.iid_law,
    jointForestGaussianPositiveDensity_law, jointNewBranchGaussianPositiveDensity_law,
    ← independent_forestGaussianInnovationLaw_split m k scale R]
  change Measure.map (coloredForestSplitCoordinates κ A m k).symm
    (Measure.map (coloredForestSplitCoordinates κ A m k)
      (independentChannelLaw (fun _ : κ => forestGaussianInnovationLaw m (k + 1) scale R))) = _
  rw [Measure.map_map (coloredForestSplitCoordinates κ A m k).symm.measurable
      (coloredForestSplitCoordinates κ A m k).measurable]
  have h : (coloredForestSplitCoordinates κ A m k).symm ∘
      coloredForestSplitCoordinates κ A m k = id :=
    funext (coloredForestSplitCoordinates κ A m k).symm_apply_apply
  rw [h, Measure.map_id]

theorem vertexRootInnovationFactor_surjective (m : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    Function.Surjective (vertexRootInnovationFactor m energy).mulVec := by
  intro y
  obtain ⟨z, hz⟩ := vertexGaussianInnovation_surjective m 0 energy
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using he)
    (Sum.elim y (fun aj => Empty.elim aj.2))
  refine ⟨fun a => z (Sum.inl a), ?_⟩
  ext a
  rw [vertexRootInnovationFactor_mulVec]
  exact congrFun hz (Sum.inl a)

theorem physicalEdgeMatrix_surjective (m : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    Function.Surjective (physicalEdgeMatrix (energy / (m + 2))).mulVec := by
  have hc : |energy / (m + 2 : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < m + 2)]
    exact (div_lt_one (by positivity)).mpr he
  apply Matrix.mulVec_surjective_iff_isUnit.mpr
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, physicalEdgeMatrix_det _ hc]
  exact (rho_pos _ hc).ne'

end GaussianWave.BS
