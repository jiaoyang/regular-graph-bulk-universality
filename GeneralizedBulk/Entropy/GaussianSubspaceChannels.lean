import GeneralizedBulk.Entropy.GaussianOrthogonalTransport

/-! Genuine Gaussian conditional observations in arbitrary orthogonal coordinates. -/
noncomputable section
open MeasureTheory Filter
namespace GeneralizedBulk.Entropy.Hermite

variable {I : Type*} [Fintype I] [DecidableEq I]

def rotatedCoordinateSigma (O : Matrix I I ℝ) (observed : Finset I) : MeasurableSpace (I → ℝ) :=
  MeasurableSpace.comap (fun x => O.transpose.mulVec x) (coordinateSigma observed)

theorem rotatedCoordinateSigma_le (O : Matrix I I ℝ) (observed : Finset I) :
    rotatedCoordinateSigma O observed ≤ (inferInstance : MeasurableSpace (I → ℝ)) :=
  (MeasurableSpace.comap_mono (coordinateSigma_le observed)).trans
    (GeneralizedBulk.Gaussian.measurable_finiteMatrixAction O.transpose).comap_le

/-- The inverse orthogonal coordinate map is measurable between the actual
observation sigma algebras. -/
theorem measurable_matrixAction_rotatedSigma (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (observed : Finset I) :
    @Measurable (I → ℝ) (I → ℝ) (coordinateSigma observed) (rotatedCoordinateSigma O observed)
      (fun x => O.mulVec x) := by
  apply Measurable.of_comap_le
  change ((coordinateSigma observed).comap (fun x => O.transpose.mulVec x)).comap (fun x => O.mulVec x) ≤ _
  rw [MeasurableSpace.comap_comp]
  have hid : (fun x => O.transpose.mulVec x) ∘ (fun x => O.mulVec x) = id := by
    funext x
    simp only [Function.comp_apply, id_eq, Matrix.mulVec_mulVec, Matrix.mul_eq_one_comm.mpr hO,
      Matrix.one_mulVec]
  rw [hid, MeasurableSpace.comap_id]

/-- Coarse-sigma measurability is transported using an actual measure-preserving
map. The null-set comparison still uses the full Gaussian measure. -/
theorem aestronglyMeasurable_comp_subsigma
    (source target : MeasurableSpace (I → ℝ)) (T : (I → ℝ) → (I → ℝ))
    (hTm : @Measurable (I → ℝ) (I → ℝ) source target T)
    (hT : @MeasurePreserving (I → ℝ) (I → ℝ) MeasurableSpace.pi MeasurableSpace.pi T
      (standardGaussian I) (standardGaussian I))
    (f : (I → ℝ) → ℝ) (hf : AEStronglyMeasurable[target] f (standardGaussian I)) :
    AEStronglyMeasurable[source] (fun x => f (T x)) (standardGaussian I) := by
  letI : MeasurableSpace (I → ℝ) := MeasurableSpace.pi
  refine ⟨hf.mk f ∘ T, hf.stronglyMeasurable_mk.comp_measurable hTm, ?_⟩
  exact hT.quasiMeasurePreserving.ae_eq_comp hf.ae_eq_mk

theorem gaussianPullback_measurable_subsigma (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (source target : MeasurableSpace (I → ℝ))
    (hTm : @Measurable (I → ℝ) (I → ℝ) source target (fun x => O.mulVec x))
    (f : Lp ℝ 2 (standardGaussian I))
    (hf : AEStronglyMeasurable[target] (f : (I → ℝ) → ℝ) (standardGaussian I)) :
    AEStronglyMeasurable[source] (gaussianPullback O hO f : (I → ℝ) → ℝ) (standardGaussian I) :=
  (aestronglyMeasurable_comp_subsigma source target _ hTm
    (standardGaussian_matrixAction_measurePreserving O hO) _ hf).congr (gaussianPullback_ae O hO f).symm

/-- The observation operator after an orthogonal change of coordinates. -/
def subspaceConditionalL2 (O : Matrix I I ℝ) (hO : O * O.transpose = 1) (observed : Finset I) :
    Lp ℝ 2 (standardGaussian I) →L[ℝ] Lp ℝ 2 (standardGaussian I) :=
  (gaussianPullback O.transpose (by simpa using Matrix.mul_eq_one_comm.mpr hO)).toContinuousLinearMap.comp
    ((coordinateConditionalL2 observed).comp (gaussianPullback O hO).toContinuousLinearMap)

theorem subspaceConditionalL2_measurable (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (observed : Finset I) (f : Lp ℝ 2 (standardGaussian I)) :
    AEStronglyMeasurable[rotatedCoordinateSigma O observed]
      (subspaceConditionalL2 O hO observed f : (I → ℝ) → ℝ) (standardGaussian I) := by
  have hOt : O.transpose * O.transpose.transpose = 1 := by simpa using Matrix.mul_eq_one_comm.mpr hO
  have hc : AEStronglyMeasurable[coordinateSigma observed]
      (coordinateConditionalL2 observed (gaussianPullback O hO f) : (I → ℝ) → ℝ) (standardGaussian I) :=
    aestronglyMeasurable_condExpL2 (coordinateSigma_le observed) _
  exact gaussianPullback_measurable_subsigma O.transpose hOt
    (rotatedCoordinateSigma O observed) (coordinateSigma observed)
    (Measurable.of_comap_le le_rfl) _ hc

/-- The rotated operator has the defining inner-product identity of the
conditional expectation for its actual observation sigma algebra. -/
theorem subspaceConditionalL2_inner_of_measurable (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (observed : Finset I) (f g : Lp ℝ 2 (standardGaussian I))
    (hg : AEStronglyMeasurable[rotatedCoordinateSigma O observed]
      (g : (I → ℝ) → ℝ) (standardGaussian I)) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (subspaceConditionalL2 O hO observed f) g =
      @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ f g := by
  have hpg := gaussianPullback_measurable_subsigma O hO (coordinateSigma observed)
    (rotatedCoordinateSigma O observed) (measurable_matrixAction_rotatedSigma O hO observed) g hg
  calc
    _ = @inner ℝ (Lp ℝ 2 (standardGaussian I)) _
        (gaussianPullback O hO (subspaceConditionalL2 O hO observed f)) (gaussianPullback O hO g) :=
      ((gaussianPullback O hO).inner_map_map _ _).symm
    _ = @inner ℝ (Lp ℝ 2 (standardGaussian I)) _
        (coordinateConditionalL2 observed (gaussianPullback O hO f)) (gaussianPullback O hO g) := by
      rw [subspaceConditionalL2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        LinearIsometry.coe_toContinuousLinearMap, gaussianPullback_transpose_inverse]
      rfl
    _ = @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (gaussianPullback O hO f) (gaussianPullback O hO g) :=
      inner_condExpL2_eq_inner_fun (coordinateSigma_le observed) _ _ hpg
    _ = _ := (gaussianPullback O hO).inner_map_map _ _

/-- This identifies the constructed rotated channel with Mathlib's genuine
conditional expectation, rather than assuming a projection law. -/
theorem subspaceConditionalL2_eq_condExpL2 (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (observed : Finset I) (f : Lp ℝ 2 (standardGaussian I)) :
    subspaceConditionalL2 O hO observed f =
      (condExpL2 ℝ ℝ (rotatedCoordinateSigma_le O observed) f : Lp ℝ 2 (standardGaussian I)) := by
  let K := lpMeas ℝ ℝ (rotatedCoordinateSigma O observed) 2 (standardGaussian I)
  letI : Fact (rotatedCoordinateSigma O observed ≤ (inferInstance : MeasurableSpace (I → ℝ))) :=
    ⟨rotatedCoordinateSigma_le O observed⟩
  have hm : subspaceConditionalL2 O hO observed f ∈ K :=
    mem_lpMeas_iff_aestronglyMeasurable.mpr (subspaceConditionalL2_measurable O hO observed f)
  have he := K.eq_orthogonalProjection_of_mem_of_inner_eq_zero (u := f)
    (v := subspaceConditionalL2 O hO observed f) hm (fun g hg => by
    rw [inner_sub_left, subspaceConditionalL2_inner_of_measurable O hO observed f g
      (mem_lpMeas_iff_aestronglyMeasurable.mp hg), sub_self])
  exact he.symm

/-- The actual Gaussian observation in any orthogonal coordinates preserves
every full homogeneous chaos. -/
theorem subspaceConditionalL2_mem_fullChaos (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (observed : Finset I) (degree : ℕ) {f : Lp ℝ 2 (standardGaussian I)}
    (hf : f ∈ fullChaosSpace I degree) : subspaceConditionalL2 O hO observed f ∈ fullChaosSpace I degree := by
  have hOt : O.transpose * O.transpose.transpose = 1 := by simpa using Matrix.mul_eq_one_comm.mpr hO
  exact gaussianPullback_mem_fullChaos O.transpose hOt degree
    (coordinateConditionalL2_mem_fullChaos observed degree (gaussianPullback_mem_fullChaos O hO degree hf))

end GeneralizedBulk.Entropy.Hermite
