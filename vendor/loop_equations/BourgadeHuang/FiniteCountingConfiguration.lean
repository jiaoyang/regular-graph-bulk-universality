import BourgadeHuang.PointProcessModel

/-! The canonical measurable counting configuration of a finite real spectrum. -/
noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory Filter
namespace BourgadeHuang

/-- The actual finite counting measure, retaining repeated particle locations. -/
def finiteCountingConfiguration {N : ℕ} (x : Fin N → ℝ) : LocalCountingMeasure where
  measure := ∑ i,Measure.dirac (x i)
  locallyFinite := inferInstance
  integer_compacts K hK := by
    classical
    refine ⟨(Finset.univ.filter (fun i=>x i∈K)).card,?_⟩
    rw [Measure.finset_sum_apply]
    simp only [Measure.dirac_apply' _ hK.measurableSet,Finset.card_filter]
    simp [Set.indicator_apply,Finset.sum_boole]

theorem finiteCountingConfiguration_measure {N : ℕ} (x : Fin N → ℝ) :
    (finiteCountingConfiguration x).measure=∑i,Measure.dirac (x i) := rfl

theorem continuous_finiteCountingConfiguration (N : ℕ) :
    Continuous (finiteCountingConfiguration : (Fin N → ℝ) → LocalCountingMeasure) := by
  apply continuous_iInf_rng.mpr
  intro f
  apply continuous_induced_rng.mpr
  change Continuous (fun x : Fin N → ℝ=>∫y,f y ∂(finiteCountingConfiguration x).measure)
  have hfinite (x : Fin N → ℝ) :
      (∫ y, f y ∂(finiteCountingConfiguration x).measure) = ∑ i, f (x i) := by
    rw [finiteCountingConfiguration_measure, integral_finset_sum_measure]
    · simp only [integral_dirac]
    · intro i _
      exact integrable_dirac
  simp only [hfinite]
  exact continuous_finset_sum _ (fun i _=>f.continuous.comp (continuous_apply i))

theorem measurable_finiteCountingConfiguration (N : ℕ) :
    Measurable (finiteCountingConfiguration : (Fin N → ℝ) → LocalCountingMeasure) :=
  by
    letI : BorelSpace LocalCountingMeasure := ⟨rfl⟩
    exact (continuous_finiteCountingConfiguration N).measurable

end BourgadeHuang
