import GeneralizedBulk.Counting.FiniteOccurrences

/-! Canonical measurable occurrence coordinates on fixed bounded unit cells. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators Topology ENNReal Classical
namespace GeneralizedBulk.Counting

def unitCell (z : ℤ) : Set ℝ := Set.Ico (z : ℝ) ((z : ℝ) + 1)

theorem measurableSet_unitCell (z : ℤ) : MeasurableSet (unitCell z) := measurableSet_Ico

/-- Restricting a finite unit-Dirac sum retains exactly the occurrences
inside the Borel subset. -/
theorem finite_diracs_restrict {m : ℕ} (x : Fin m → ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    (∑ i, Measure.dirac (x i)).restrict A =
      ∑ i : {i : Fin m // x i ∈ A}, Measure.dirac (x i.val) := by
  classical
  ext B hB
  rw [Measure.restrict_apply hB,Measure.finset_sum_apply,Measure.finset_sum_apply]
  have hs := Finset.sum_subtype (p := fun i : Fin m => x i ∈ A) (F := inferInstance)
    (Finset.univ.filter (fun i : Fin m => x i ∈ A))
    (fun i => by simp) (fun i => (Measure.dirac (x i)) B)
  rw [← hs,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hx : x i ∈ A
  · simp [Measure.dirac_apply' _ (hB.inter hA),Measure.dirac_apply' _ hB,Set.indicator_apply,hx]
  · simp [Measure.dirac_apply' _ (hB.inter hA),Set.indicator_apply,hx]

/-- A bounded Borel restriction of an actual counting measure has a genuine
finite sorted occurrence list. -/
theorem orderedOccurrences_restrict_bounded (xi : LocalCountingMeasure)
    (A K : Set ℝ) (hA : MeasurableSet A) (hK : IsCompact K) (hAK : A ⊆ K) :
    Nonempty (OrderedOccurrences (xi.measure.restrict A)) := by
  classical
  obtain ⟨m,x,_hx,hmu,_hcount⟩ := xi.exists_compact_particle_list_with_multiplicity hK
  let J := {i : Fin m // x i ∈ A}
  let e := Fintype.equivFin J
  let y : Fin (Fintype.card J) → ℝ := fun j => x (e.symm j).val
  have heq : xi.measure.restrict A = ∑ j, Measure.dirac (y j) := by
    calc
      _ = (xi.measure.restrict K).restrict A := (Measure.restrict_restrict_of_subset hAK).symm
      _ = (∑ i, Measure.dirac (x i)).restrict A := congrArg (fun mu => mu.restrict A) hmu
      _ = ∑ i : J, Measure.dirac (x i.val) := finite_diracs_restrict x A hA
      _ = _ := Fintype.sum_equiv e _ _ (fun j => by simp [y])
  rw [heq]
  exact orderedOccurrences_of_finite_diracs y

def cellCountingMeasure (xi : LocalCountingMeasure) (z : ℤ) : FiniteCountingMeasure :=
  ⟨xi.measure.restrict (unitCell z),orderedOccurrences_restrict_bounded xi (unitCell z)
    (Set.Icc (z : ℝ) ((z : ℝ) + 1)) (measurableSet_unitCell z) isCompact_Icc
    (fun x hx => ⟨hx.1,hx.2.le⟩)⟩

theorem measurable_cellCountingMeasure (z : ℤ) :
    Measurable (fun xi : LocalCountingMeasure => cellCountingMeasure xi z) := by
  apply Measurable.subtype_mk
  apply Measure.measurable_measure.mpr
  intro A hA
  change Measurable (fun xi : LocalCountingMeasure => (xi.measure.restrict (unitCell z)) A)
  simp only [Measure.restrict_apply hA]
  exact LocalCountingMeasure.measurable_mass (hA.inter (measurableSet_unitCell z))

def cellCount (xi : LocalCountingMeasure) (z : ℤ) : ℕ := finiteCount (cellCountingMeasure xi z)
def cellOccurrence (xi : LocalCountingMeasure) (z : ℤ) (k : ℕ) : ℝ := occurrence (cellCountingMeasure xi z) k

theorem measurable_cellCount (z : ℤ) : Measurable (fun xi : LocalCountingMeasure => cellCount xi z) :=
  measurable_finiteCount.comp (measurable_cellCountingMeasure z)

theorem measurable_cellOccurrence (z : ℤ) (k : ℕ) :
    Measurable (fun xi : LocalCountingMeasure => cellOccurrence xi z k) :=
  (measurable_occurrence k).comp (measurable_cellCountingMeasure z)

/-- The sorted cell list has exactly the actual unit counting mass. -/
theorem cell_mass_eq_count (xi : LocalCountingMeasure) (z : ℤ) :
    xi.measure (unitCell z) = cellCount xi z := by
  have h := (chosenOccurrences (cellCountingMeasure xi z)).mass_univ
  rw [← finiteCount_eq] at h
  simpa only [cellCountingMeasure,Measure.restrict_apply_univ] using h

/-- Every actual cell occurrence lies in its fixed cell. -/
theorem cellOccurrence_mem (xi : LocalCountingMeasure) (z : ℤ) (k : ℕ) (hk : k < cellCount xi z) :
    cellOccurrence xi z k ∈ unitCell z := by
  classical
  let p := chosenOccurrences (cellCountingMeasure xi z)
  have hkp : k < p.count := by simpa only [cellCount,finiteCount_eq] using hk
  have hloc : cellOccurrence xi z k = p.location ⟨k,hkp⟩ := by
    change (if h : k < p.count then p.location ⟨k,h⟩ else 0) = _
    rw [dif_pos hkp]
  rw [hloc]
  have heq := p.measure_eq
  have hz : (xi.measure.restrict (unitCell z)) (unitCell z)ᶜ = 0 := by
    rw [Measure.restrict_apply (measurableSet_unitCell z).compl,Set.compl_inter_self,measure_empty]
  have hm : (∑ i, Measure.dirac (p.location i)) (unitCell z)ᶜ = 0 := by
    rw [← heq]
    exact hz
  rw [Measure.finset_sum_apply] at hm
  have hsingle := Finset.single_le_sum (fun i _ => zero_le
    ((Measure.dirac (p.location i)) (unitCell z)ᶜ)) (Finset.mem_univ ⟨k,hkp⟩)
  rw [hm] at hsingle
  by_contra hnot
  rw [Measure.dirac_apply' _ (measurableSet_unitCell z).compl,
    Set.indicator_of_mem hnot] at hsingle
  exact not_le_of_gt zero_lt_one hsingle

end GeneralizedBulk.Counting
