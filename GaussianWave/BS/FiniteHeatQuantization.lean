import GaussianWave.BS.FiniteCoordinateReindex

/-! Uniform finite-alphabet heat quantization limits on arbitrary finite
coordinate types, proved by actual volume-preserving reindexing. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GaussianWave.BS
open Reused.Entropy
variable {I J : Type*} [Fintype I] [Fintype J]

theorem clippedGridVector_eq_coordinatewise {m : ℕ} (a : ℝ) (K : ℕ) :
    clippedGridVector (m := m) a K =
      coordinatewiseQuantizer (codedClippedGridLabel a (K+1) (by omega)) := by
  funext x i
  rfl

def finiteHeatGridEntropy (μ : Measure (I → ℝ)) (t a : ℝ) (K : ℕ) : ℝ :=
  Finite.entropy (lawMass (heatedLaw μ t)
    (coordinatewiseQuantizer (codedClippedGridLabel a (K+1) (by omega))))

def countableHeatGridEntropy (μ : Measure (I → ℝ)) (t a : ℝ) : ℝ :=
  countableEntropy (lawMass (heatedLaw μ t) (gridLabel a))

theorem finiteHeatGridEntropy_reindex
    (μ : Measure (I → ℝ)) [SFinite μ] (e : I ≃ J) (t a : ℝ) (K : ℕ) :
    finiteHeatGridEntropy (Measure.map (coordinateReindex e) μ) t a K = finiteHeatGridEntropy μ t a K := by
  unfold finiteHeatGridEntropy
  rw [← heatedLaw_map_coordinateReindex]
  exact finite_quantizer_entropy_coordinateReindex (heatedLaw μ t) e _ (measurable_codedClippedGridLabel a (K+1) (by omega))

theorem countableHeatGridEntropy_reindex
    (μ : Measure (I → ℝ)) [SFinite μ] (e : I ≃ J) (t a : ℝ) :
    countableHeatGridEntropy (Measure.map (coordinateReindex e) μ) t a = countableHeatGridEntropy μ t a := by
  unfold countableHeatGridEntropy
  rw [← heatedLaw_map_coordinateReindex]
  exact countable_quantizer_entropy_coordinateReindex (heatedLaw μ t) e (fun x : ℝ => Int.floor (x/a)) (by fun_prop)

/-- Actual finite clipping entropy converges to the countable-grid entropy
for any finite window index, with no arbitrary enumeration as an input. -/
theorem tendsto_finiteHeatGridEntropy_cutoff
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (finiteHeatGridEntropy μ t a) atTop (𝓝 (countableHeatGridEntropy μ t a)) := by
  let e := Fintype.equivFin I
  let ν := Measure.map (coordinateReindex e) μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map (measurable_coordinateReindex e).aemeasurable
  have hν := integrable_squareRadius_coordinateReindex μ e hμ
  have h := tendsto_heat_finite_grid_entropy_cutoff ν hν ht a ha
  have hfinite (K : ℕ) :
      Finite.entropy (lawMass (heatedLaw ν t) (clippedGridVector a K)) = finiteHeatGridEntropy μ t a K := by
    rw [clippedGridVector_eq_coordinatewise]
    have hh := finiteHeatGridEntropy_reindex μ e t a K
    unfold finiteHeatGridEntropy at hh
    convert hh using 1
    unfold Finite.entropy
    congr 1
    ext b
    simp
  have hcount : countableEntropy (gridMass a (heatDensity ν t)) = countableHeatGridEntropy μ t a := by
    rw [← lawMass_heatedLaw_gridLabel ν ht a ha]
    exact countableHeatGridEntropy_reindex μ e t a
  simpa only [hfinite, hcount] using h

/-- The second limit removes the mesh normalization and gives the actual
ambient differential entropy, with an arbitrary finite coordinate type. -/
theorem tendsto_countableHeatGridEntropy_mesh
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => countableHeatGridEntropy μ t (a n) + (Fintype.card I : ℝ)*Real.log (a n)) atTop
      (𝓝 (densityEntropy volume (heatDensity μ t))) := by
  let e := Fintype.equivFin I
  let ν := Measure.map (coordinateReindex e) μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map (measurable_coordinateReindex e).aemeasurable
  have hν := integrable_squareRadius_coordinateReindex μ e hμ
  have h := tendsto_heatDensity_grid_entropy ν hν ht a ha ha0
  have hcount (n : ℕ) : countableEntropy (gridMass (a n) (heatDensity ν t)) = countableHeatGridEntropy μ t (a n) := by
    rw [← lawMass_heatedLaw_gridLabel ν ht (a n) (ha n)]
    exact countableHeatGridEntropy_reindex μ e t (a n)
  rw [heatDensity_entropy_coordinateReindex μ e t] at h
  simpa only [hcount] using h
end GaussianWave.BS
