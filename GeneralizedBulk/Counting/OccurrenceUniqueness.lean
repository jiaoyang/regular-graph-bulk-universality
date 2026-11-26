import GeneralizedBulk.Counting.FiniteOccurrences

/-! Sorted occurrence coordinates are independent of the pointwise choice
of sorted representation. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped ENNReal
namespace GeneralizedBulk.Counting

theorem OrderedOccurrences.occurrence_eq (mu : FiniteCountingMeasure)
    (p : OrderedOccurrences mu.val) (k : Fin p.count) : occurrence mu k.val = p.location k := by
  have hc : finiteCount mu = p.count := by
    rw [finiteCount,p.mass_univ]
    simp
  apply eq_of_forall_gt_iff
  intro t
  have hs : strictCount mu t = (Finset.univ.filter (fun j => p.location j < t)).card := by
    rw [strictCount,p.mass_Iio]
    simp
  rw [occurrence_lt_iff,hc,hs]
  simp only [k.isLt,true_and,not_le.mpr k.isLt,false_and,or_false]
  exact (monotone_location_lt_iff_count p.location p.monotone_location k t).symm

theorem finiteCountingMeasure_eq_sum_occurrences (mu : FiniteCountingMeasure) :
    mu.val = ∑ k : Fin (finiteCount mu), Measure.dirac (occurrence mu k.val) := by
  let p := chosenOccurrences mu
  have hc : finiteCount mu = p.count := finiteCount_eq mu
  rw [hc]
  calc
    _ = ∑ k, Measure.dirac (p.location k) := p.measure_eq
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [p.occurrence_eq mu k]

end GeneralizedBulk.Counting
