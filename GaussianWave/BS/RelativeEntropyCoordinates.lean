import GaussianWave.BS.LinearEntropy
import GaussianWave.BS.FiniteCoordinateReindex
import GaussianWave.BS.GaussianEntropyWitness

/-! Relative differential entropy is unchanged by any common invertible
linear chart, including charts with different finite coordinate index sets. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GaussianWave.BS

variable {I J : Type*} [Fintype I] [Fintype J]

def FiniteEntropyDensity.reindex {μ : Measure (I → ℝ)} (f : FiniteEntropyDensity μ)
    (e : I ≃ J) : FiniteEntropyDensity (Measure.map (coordinateReindex e) μ) := by
  let E := coordinateReindexMeasurableEquiv ℝ e
  let g := fun y => f.density (E.symm y)
  have hpres : MeasurePreserving E volume volume := coordinateReindex_volumePreserving e
  have hgi : Integrable g := (hpres.integrable_comp_emb E.measurableEmbedding).mp (by
    change Integrable (fun x => f.density (E.symm (E x))) volume
    simpa only [E.symm_apply_apply] using f.integrable)
  have hglog : Integrable (fun y => g y * Real.log (g y)) :=
    (hpres.integrable_comp_emb E.measurableEmbedding).mp (by
      change Integrable (fun x => f.density (E.symm (E x)) * Real.log (f.density (E.symm (E x)))) volume
      simpa only [E.symm_apply_apply] using f.integrable_log)
  have hmass : (∫ y,g y) = 1 := by
    have hh := hpres.integral_comp E.measurableEmbedding g
    simpa only [g,E.symm_apply_apply,f.integral_eq_one] using hh.symm
  refine ⟨g,f.measurable.comp E.symm.measurable,fun _ => f.nonneg _,hgi,hmass,hglog,?_⟩
  change Measure.map E μ = _
  rw [f.measure_eq,map_withDensity_measurableEquiv volume E _ f.measurable.ennreal_ofReal,hpres.map_eq]

theorem FiniteEntropyDensity.reindex_entropy {μ : Measure (I → ℝ)}
    (f : FiniteEntropyDensity μ) (e : I ≃ J) : (f.reindex e).entropy = f.entropy := by
  let E := coordinateReindexMeasurableEquiv ℝ e
  have hpres : MeasurePreserving E volume volume := coordinateReindex_volumePreserving e
  have h := hpres.integral_comp E.measurableEmbedding
    (fun y => f.density (E.symm y) * Real.log (f.density (E.symm y)))
  simp only [E.symm_apply_apply] at h
  exact congrArg Neg.neg h.symm

def coordinateReindexLinearEquiv (e : I ≃ J) : (I → ℝ) ≃ₗ[ℝ] (J → ℝ) where
  toEquiv := coordinateReindexEquiv ℝ e
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

def linearChartIndexEquiv (A : (I → ℝ) ≃ₗ[ℝ] (J → ℝ)) : I ≃ J :=
  Fintype.equivOfCardEq (by simpa using A.finrank_eq)

def squareChartEquiv (A : (I → ℝ) ≃ₗ[ℝ] (J → ℝ)) : (J → ℝ) ≃ₗ[ℝ] (J → ℝ) :=
  (coordinateReindexLinearEquiv (linearChartIndexEquiv A)).symm.trans A

variable [DecidableEq I] [DecidableEq J]

def squareChartMatrix (A : (I → ℝ) ≃ₗ[ℝ] (J → ℝ)) : Matrix J J ℝ :=
  LinearMap.toMatrix' (squareChartEquiv A).toLinearMap

theorem squareChartMatrix_det_ne_zero (A : (I → ℝ) ≃ₗ[ℝ] (J → ℝ)) :
    (squareChartMatrix A).det ≠ 0 := by
  rw [squareChartMatrix,LinearMap.det_toMatrix']
  exact (squareChartEquiv A).isUnit_det'.ne_zero

theorem squareChartMatrix_comp_reindex (A : (I → ℝ) ≃ₗ[ℝ] (J → ℝ)) :
    (squareChartMatrix A).mulVec ∘ coordinateReindex (linearChartIndexEquiv A) = A := by
  have h : (squareChartMatrix A).mulVec = squareChartEquiv A :=
    congrArg DFunLike.coe (Matrix.toLin'_toMatrix' (squareChartEquiv A).toLinearMap)
  rw [h]
  funext x
  exact congrArg A ((coordinateReindexLinearEquiv (linearChartIndexEquiv A)).symm_apply_apply x)

def FiniteEntropyDensity.linearEquiv {μ : Measure (I → ℝ)} [IsProbabilityMeasure μ]
    (f : FiniteEntropyDensity μ) (A : (I → ℝ) ≃ₗ[ℝ] (J → ℝ)) :
    FiniteEntropyDensity (Measure.map A μ) := by
  let e := linearChartIndexEquiv A
  letI : IsProbabilityMeasure (Measure.map (coordinateReindex e) μ) :=
    isProbabilityMeasure_map (measurable_coordinateReindex e).aemeasurable
  have hmap : Measure.map (squareChartMatrix A).mulVec (Measure.map (coordinateReindex e) μ) =
      Measure.map A μ := by
    rw [Measure.map_map (measurable_finiteMatrixAction _) (measurable_coordinateReindex e)]
    rw [squareChartMatrix_comp_reindex]
  exact ((f.reindex e).linearImage (squareChartMatrix A) (squareChartMatrix_det_ne_zero A)).cast hmap.symm

theorem FiniteEntropyDensity.linearEquiv_entropy_difference
    {μ ν : Measure (I → ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : FiniteEntropyDensity μ) (g : FiniteEntropyDensity ν)
    (A : (I → ℝ) ≃ₗ[ℝ] (J → ℝ)) :
    (f.linearEquiv A).entropy - (g.linearEquiv A).entropy = f.entropy-g.entropy := by
  let e := linearChartIndexEquiv A
  letI : IsProbabilityMeasure (Measure.map (coordinateReindex e) μ) :=
    isProbabilityMeasure_map (measurable_coordinateReindex e).aemeasurable
  letI : IsProbabilityMeasure (Measure.map (coordinateReindex e) ν) :=
    isProbabilityMeasure_map (measurable_coordinateReindex e).aemeasurable
  change ((f.reindex e).linearImage (squareChartMatrix A) (squareChartMatrix_det_ne_zero A)).entropy -
    ((g.reindex e).linearImage (squareChartMatrix A) (squareChartMatrix_det_ne_zero A)).entropy = _
  rw [FiniteEntropyDensity.linearImage_entropy_difference,f.reindex_entropy,g.reindex_entropy]

end GaussianWave.BS
