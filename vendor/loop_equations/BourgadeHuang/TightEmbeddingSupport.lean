import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tight

/-!
# Tight mapped limits remain on the image

A weak limit of continuous images of a tight family gives full mass to the
image. The image itself need not be assumed measurable: its complement is
contained in complements of compact images with arbitrarily small mass.
-/
noncomputable section
open scoped Topology
open MeasureTheory Filter Set
namespace BourgadeHuang

/-- Tightness prevents mass escaping the range of a continuous map under weak
convergence. Injectivity and compactness of the ambient target are unnecessary. -/
theorem measure_compl_range_eq_zero_of_tight_map_limit
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (hf : Continuous f) (hfm : Measurable f)
    (μ : ℕ → ProbabilityMeasure X)
    (ht : IsTightMeasureSet (Set.range (fun n => (μ n : Measure X))))
    (ν : ProbabilityMeasure Y) (r : ℕ → ℕ)
    (hlim : Tendsto (fun n => (μ (r n)).map hfm.aemeasurable) atTop (𝓝 ν)) :
    (ν : Measure Y) (Set.range f)ᶜ = 0 := by
  apply le_antisymm _ bot_le
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  obtain ⟨K, hK, hmass⟩ :=
    IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht ε hε
  have hclosed : IsClosed (f '' K) := (hK.image hf).isClosed
  have hpre : f ⁻¹' (f '' K)ᶜ ⊆ Kᶜ := by
    intro x hx hxK
    exact hx ⟨x, hxK, rfl⟩
  have hm (n : ℕ) : ((μ (r n)).map hfm.aemeasurable : Measure Y) (f '' K)ᶜ ≤ ε := by
    rw [ProbabilityMeasure.map_apply' _ _ hclosed.measurableSet.compl]
    exact (measure_mono hpre).trans (hmass _ ⟨r n, rfl⟩)
  calc
    (ν : Measure Y) (Set.range f)ᶜ ≤ (ν : Measure Y) (f '' K)ᶜ :=
      measure_mono (Set.compl_subset_compl.mpr (Set.image_subset_range _ _))
    _ ≤ atTop.liminf (fun n => ((μ (r n)).map hfm.aemeasurable : Measure Y) (f '' K)ᶜ) :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hclosed.isOpen_compl
    _ ≤ ε := liminf_le_of_frequently_le (Filter.Eventually.of_forall hm).frequently

end BourgadeHuang
