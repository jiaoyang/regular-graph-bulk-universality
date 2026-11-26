import GaussianWave.Foundation

/-!
# Finite continuity partitions of compact sets

Null-boundary metric balls are constructed from the countability argument in
Portmanteau, then a finite subcover is disjointized. The resulting finite
cells have arbitrarily small diameter. Weak convergence supplies actual
convergence of every cell's mass; this is not a transport hypothesis.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace GaussianWave

section ContinuityAlgebra
variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] (ν : Measure E)

/-- A measurable set whose frontier has zero limiting mass. -/
def IsContinuityCell (s : Set E) : Prop := MeasurableSet s ∧ ν (frontier s) = 0

theorem continuityCell_empty : IsContinuityCell ν (∅ : Set E) := by
  simp [IsContinuityCell]

theorem continuityCell_union {s t : Set E}
    (hs : IsContinuityCell ν s) (ht : IsContinuityCell ν t) :
    IsContinuityCell ν (s ∪ t) := by
  refine ⟨hs.1.union ht.1, measure_mono_null ?_ (measure_union_null hs.2 ht.2)⟩
  intro x hx
  rcases frontier_union_subset s t hx with hx | hx
  · exact Or.inl hx.1
  · exact Or.inr hx.2

theorem continuityCell_diff {s t : Set E}
    (hs : IsContinuityCell ν s) (ht : IsContinuityCell ν t) :
    IsContinuityCell ν (s \ t) := by
  refine ⟨hs.1.diff ht.1, measure_mono_null ?_ (measure_union_null hs.2 ht.2)⟩
  intro x hx
  rw [diff_eq] at hx
  rcases frontier_inter_subset s tᶜ hx with hx | hx
  · exact Or.inl hx.1
  · exact Or.inr (by simpa using hx.2)

theorem continuityCell_finset_sup {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (f : ι → Set E)
    (hf : ∀ i ∈ t, IsContinuityCell ν (f i)) :
    IsContinuityCell ν (t.sup f) := by
  induction t using Finset.induction_on with
  | empty => simpa using continuityCell_empty ν
  | @insert i t hi ih =>
    rw [Finset.sup_insert]
    exact continuityCell_union ν (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem continuityCell_disjointed {ι : Type*} [Preorder ι]
    [LocallyFiniteOrderBot ι] [DecidableEq ι]
    (f : ι → Set E) (hf : ∀ i, IsContinuityCell ν (f i)) (i : ι) :
    IsContinuityCell ν (disjointed f i) := by
  rw [disjointed_apply]
  exact continuityCell_diff ν (hf i)
    (continuityCell_finset_sup ν (Finset.Iio i) f (fun j _ => hf j))

end ContinuityAlgebra

/-- A finite disjoint family of continuity cells covers any compact set.
The index type can be empty when the compact set is empty. -/
theorem exists_finite_continuity_partition
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [SFinite ν] (K : Set E) (hK : IsCompact K)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, ∃ P : Fin n → Set E,
      (∀ i, MeasurableSet (P i)) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      (K ⊆ ⋃ i, P i) ∧
      (∀ i, ν (frontier (P i)) = 0) ∧
      ∀ i, ∀ x ∈ P i, ∀ y ∈ P i, dist x y ≤ δ := by
  classical
  have hball (x : E) : ∃ r : ℝ, δ / 4 < r ∧ r < δ / 2 ∧
      ν (frontier (Metric.ball x r)) = 0 := by
    obtain ⟨r, hr, hn⟩ := exists_null_frontier_thickening ν ({x} : Set E)
      (show δ / 4 < δ / 2 by linarith)
    exact ⟨r, hr.1, hr.2, by simpa only [Metric.thickening_singleton] using hn⟩
  choose r hr using hball
  let U : E → Set E := fun x => Metric.ball x (r x)
  have hUopen (x : E) : IsOpen (U x) := Metric.isOpen_ball
  have hcover : K ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, Metric.mem_ball_self (by linarith [(hr x).1])⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUopen hcover
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  let f : Fin (Fintype.card t) → Set E := fun i => U (e.symm i).val
  have hf (i : Fin (Fintype.card t)) : IsContinuityCell ν (f i) := by
    exact ⟨(hUopen _).measurableSet, (hr _).2.2⟩
  refine ⟨Fintype.card t, disjointed f, ?_, disjoint_disjointed f, ?_, ?_, ?_⟩
  · exact fun i => (continuityCell_disjointed ν f hf i).1
  · rw [iUnion_disjointed]
    intro x hx
    rcases mem_iUnion₂.mp (ht hx) with ⟨a, ha, hxa⟩
    exact mem_iUnion.mpr ⟨e ⟨a, ha⟩, by simpa [f] using hxa⟩
  · exact fun i => (continuityCell_disjointed ν f hf i).2
  · intro i x hx y hy
    have hx' := disjointed_subset f i hx
    have hy' := disjointed_subset f i hy
    change dist x (e.symm i).val < r (e.symm i).val at hx'
    change dist y (e.symm i).val < r (e.symm i).val at hy'
    calc
      dist x y ≤ dist x (e.symm i).val + dist (e.symm i).val y := dist_triangle _ _ _
      _ ≤ δ := by rw [dist_comm (e.symm i).val y]; linarith [(hr (e.symm i).val).2.1]

/-- Portmanteau applied to the previously constructed continuity cells. -/
theorem weakLawConverges_cell_mass
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [HasOuterApproxClosed E]
    (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hweak : WeakLawConverges μ ν) (A : Set E)
    (hfrontier : ν (frontier A) = 0) :
    Tendsto (fun n => μ n A) atTop (𝓝 (ν A)) := by
  let μ' : ℕ → ProbabilityMeasure E := fun n => ⟨μ n, inferInstance⟩
  let ν' : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have hw : Tendsto μ' atTop (𝓝 ν') :=
    (weakLawConverges_iff_probability_tendsto μ' ν').mp hweak
  exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hw hfrontier

/-- In finite measures the real masses converge as well. -/
theorem weakLawConverges_cell_real_mass
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [HasOuterApproxClosed E]
    (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hweak : WeakLawConverges μ ν) (A : Set E)
    (hfrontier : ν (frontier A) = 0) :
    Tendsto (fun n => (μ n A).toReal) atTop (𝓝 ((ν A).toReal)) := by
  exact (ENNReal.tendsto_toReal (measure_ne_top ν A)).comp
    (weakLawConverges_cell_mass μ ν hweak A hfrontier)

end GaussianWave
