import BourgadeHuang.CountingAtomicity
import BourgadeHuang.CountingEvaluation

/-!
# Measurable sorted occurrences of finite counting measures

Multiplicity is retained. The sorted list is chosen pointwise, but every
coordinate is proved measurable from fixed-threshold counting evaluations;
measurability of the choice is not postulated.
-/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators Topology ENNReal Classical
namespace GeneralizedBulk.Counting

structure OrderedOccurrences (mu : Measure ℝ) where
  count : ℕ
  location : Fin count → ℝ
  monotone_location : Monotone location
  measure_eq : mu = ∑ i, Measure.dirac (location i)

def listDiracSum (l : List ℝ) : Measure ℝ := ∑ i : Fin l.length, Measure.dirac (l.get i)

theorem listDiracSum_eq_map_sum (l : List ℝ) :
    listDiracSum l = (l.map Measure.dirac).sum := by
  rw [listDiracSum,← List.sum_ofFn]
  change (List.ofFn (Measure.dirac ∘ l.get)).sum = _
  rw [← List.map_ofFn,List.ofFn_get]

/-- Every literal finite Dirac sum has a sorted occurrence list, including
all repeated entries. -/
theorem orderedOccurrences_of_finite_diracs {m : ℕ} (x : Fin m → ℝ) :
    Nonempty (OrderedOccurrences (∑ i, Measure.dirac (x i))) := by
  let l := (List.ofFn x).mergeSort (fun a b => decide (a ≤ b))
  have hsort : l.Sorted (· ≤ ·) := List.sorted_mergeSort' (· ≤ ·) (List.ofFn x)
  have hperm : l.Perm (List.ofFn x) := List.mergeSort_perm _ _
  refine ⟨⟨l.length,l.get,hsort.get_mono,?_⟩⟩
  change (∑ i, Measure.dirac (x i)) = listDiracSum l
  have heq : listDiracSum l = listDiracSum (List.ofFn x) := by
    rw [listDiracSum_eq_map_sum,listDiracSum_eq_map_sum]
    exact (hperm.map Measure.dirac).sum_eq
  rw [heq]
  rw [listDiracSum_eq_map_sum,List.map_ofFn,List.sum_ofFn]
  rfl

/-- A monotone finite array is determined by its strict cumulative counts. -/
theorem monotone_location_lt_iff_count {m : ℕ} (x : Fin m → ℝ) (hx : Monotone x)
    (k : Fin m) (t : ℝ) :
    x k < t ↔ k.val < (Finset.univ.filter (fun j => x j < t)).card := by
  constructor
  · intro hk
    have hsub : Finset.Iic k ⊆ Finset.univ.filter (fun j => x j < t) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hx (Finset.mem_Iic.mp hj)).trans_lt hk⟩
    have hh := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hh
    omega
  · intro hk
    by_contra hnot
    have hsub : Finset.univ.filter (fun j => x j < t) ⊆ Finset.Iio k := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hjk
      have hh := (le_of_not_gt hnot).trans (hx (le_of_not_gt hjk))
      exact (not_lt_of_ge hh) (Finset.mem_filter.mp hj).2
    have hh := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hh
    omega

namespace OrderedOccurrences
variable {mu : Measure ℝ} (p : OrderedOccurrences mu)

theorem mass_univ : mu Set.univ = p.count := by
  calc
    _ = (∑ i, Measure.dirac (p.location i)) Set.univ := congrArg (fun nu => nu Set.univ) p.measure_eq
    _ = _ := by rw [Measure.finset_sum_apply]; simp

theorem mass_Iio (t : ℝ) : mu (Set.Iio t) =
    ((Finset.univ.filter (fun j => p.location j < t)).card : ℝ≥0∞) := by
  calc
    _ = (∑ i, Measure.dirac (p.location i)) (Set.Iio t) := congrArg (fun nu => nu (Set.Iio t)) p.measure_eq
    _ = _ := by
      rw [Measure.finset_sum_apply]
      simp only [Measure.dirac_apply' _ measurableSet_Iio,Set.mem_Iio,Set.indicator_apply]
      change (∑ j : Fin p.count, if p.location j < t then (1 : ℝ≥0∞) else 0) = _
      exact Finset.sum_boole _ _

end OrderedOccurrences

/-- The domain of finite counting measures, equipped with the inherited
measure-valued measurable structure. -/
abbrev FiniteCountingMeasure := {mu : Measure ℝ // Nonempty (OrderedOccurrences mu)}

def chosenOccurrences (mu : FiniteCountingMeasure) : OrderedOccurrences mu.val :=
  Classical.choice mu.property

def finiteCount (mu : FiniteCountingMeasure) : ℕ := ⌊(mu.val Set.univ).toReal⌋₊
def strictCount (mu : FiniteCountingMeasure) (t : ℝ) : ℕ := ⌊(mu.val (Set.Iio t)).toReal⌋₊

theorem finiteCount_eq (mu : FiniteCountingMeasure) : finiteCount mu = (chosenOccurrences mu).count := by
  rw [finiteCount,(chosenOccurrences mu).mass_univ]
  simp

theorem strictCount_eq (mu : FiniteCountingMeasure) (t : ℝ) : strictCount mu t =
    (Finset.univ.filter (fun j => (chosenOccurrences mu).location j < t)).card := by
  rw [strictCount,(chosenOccurrences mu).mass_Iio]
  simp

def occurrence (mu : FiniteCountingMeasure) (k : ℕ) : ℝ :=
  if h : k < (chosenOccurrences mu).count then (chosenOccurrences mu).location ⟨k,h⟩ else 0

theorem occurrence_lt_iff (mu : FiniteCountingMeasure) (k : ℕ) (t : ℝ) :
    occurrence mu k < t ↔
      (k < finiteCount mu ∧ k < strictCount mu t) ∨ (finiteCount mu ≤ k ∧ 0 < t) := by
  rw [finiteCount_eq,strictCount_eq]
  by_cases hk : k < (chosenOccurrences mu).count
  · rw [occurrence,dif_pos hk]
    simp only [hk,true_and,not_le.mpr hk,false_and,or_false]
    exact monotone_location_lt_iff_count _ (chosenOccurrences mu).monotone_location ⟨k,hk⟩ t
  · rw [occurrence,dif_neg hk]
    simp only [hk,false_and,le_of_not_gt hk,true_and,false_or]

theorem measurable_finiteCount : Measurable finiteCount :=
  Nat.floor_mono.measurable.comp ((Measure.measurable_coe MeasurableSet.univ).comp measurable_subtype_coe).ennreal_toReal

theorem measurable_strictCount (t : ℝ) : Measurable (fun mu : FiniteCountingMeasure => strictCount mu t) :=
  Nat.floor_mono.measurable.comp ((Measure.measurable_coe measurableSet_Iio).comp measurable_subtype_coe).ennreal_toReal

/-- Every sorted occurrence coordinate is Borel measurable, as proved from
its integer CDF characterization. -/
theorem measurable_occurrence (k : ℕ) : Measurable (fun mu : FiniteCountingMeasure => occurrence mu k) := by
  apply measurable_of_Iio
  intro t
  have heq : (fun mu : FiniteCountingMeasure => occurrence mu k) ⁻¹' Set.Iio t =
      {mu | k < finiteCount mu ∧ k < strictCount mu t} ∪
      {mu | finiteCount mu ≤ k ∧ 0 < t} := by
    ext mu
    exact occurrence_lt_iff mu k t
  rw [heq]
  have ht : MeasurableSet {mu : FiniteCountingMeasure | (0 : ℝ) < t} := by
    by_cases h : (0 : ℝ) < t <;> simp [h]
  exact ((measurableSet_lt measurable_const measurable_finiteCount).inter
    (measurableSet_lt measurable_const (measurable_strictCount t))).union
      ((measurableSet_le measurable_finiteCount measurable_const).inter
        ht)

end GeneralizedBulk.Counting
