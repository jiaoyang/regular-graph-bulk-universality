import GeneralizedBulk.Counting.CellOccurrences
import GeneralizedBulk.Counting.PrefixEnumeration
import GeneralizedBulk.Gaussian.Presentation

/-!
# Canonical measurable global occurrences

Fixed integer unit cells are enumerated by Nat. Their finite sorted lists are
concatenated using actual measurable prefix counts. Infinite total mass makes
this a genuine Nat presentation of all occurrences, including multiplicities.
-/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators Topology ENNReal Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
namespace GeneralizedBulk.Counting

def cellInteger (n : ℕ) : ℤ := Equiv.intEquivNat.symm n

theorem pairwise_disjoint_unitCell : Pairwise (fun z w : ℤ => Disjoint (unitCell z) (unitCell w)) := by
  intro z w hzw
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hzw ((Int.floor_eq_on_Ico z x hx).symm.trans (Int.floor_eq_on_Ico w x hy))

theorem indexed_unitCell_disjoint : Pairwise (fun i j : ℕ =>
    Disjoint (unitCell (cellInteger i)) (unitCell (cellInteger j))) := by
  intro i j hij
  exact pairwise_disjoint_unitCell (fun h => hij (Equiv.intEquivNat.symm.injective h))

theorem indexed_unitCell_cover : (⋃ n : ℕ, unitCell (cellInteger n)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine Set.mem_iUnion.mpr ⟨Equiv.intEquivNat ⌊x⌋,?_⟩
  simp only [cellInteger,Equiv.symm_apply_apply]
  exact ⟨Int.floor_le x,Int.lt_floor_add_one x⟩

def indexedCellCount (xi : LocalCountingMeasure) (n : ℕ) : ℕ := cellCount xi (cellInteger n)
def prefixCells (m : ℕ) : Set ℝ := ⋃ j ∈ Finset.range m, unitCell (cellInteger j)

theorem prefixCells_monotone : Monotone prefixCells := by
  intro a b hab
  exact Set.biUnion_mono (fun j hj => Finset.range_mono hab hj) (fun j hj => Set.Subset.rfl)

theorem prefixCells_cover : (⋃ m, prefixCells m) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ j, unitCell (cellInteger j) := by rw [indexed_unitCell_cover]; trivial
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨j + 1,Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨by simp,hj⟩⟩⟩

theorem prefixCells_mass (xi : LocalCountingMeasure) (m : ℕ) :
    xi.measure (prefixCells m) = (countPrefix (indexedCellCount xi) m : ℝ≥0∞) := by
  rw [prefixCells,measure_biUnion_finset
    (fun i hi j hj hij => indexed_unitCell_disjoint hij)
    (fun j hj => measurableSet_unitCell (cellInteger j))]
  simp only [cell_mass_eq_count,countPrefix,indexedCellCount,Nat.cast_sum]

theorem exists_prefix_gt_of_totalMass_top (xi : LocalCountingMeasure)
    (hxi : xi.measure Set.univ = ∞) (n : ℕ) :
    ∃ m, n < countPrefix (indexedCellCount xi) (m + 1) := by
  classical
  by_contra hnot
  have hb (m : ℕ) : countPrefix (indexedCellCount xi) m ≤ n := by
    cases m with
    | zero => simp
    | succ m => exact le_of_not_gt (not_exists.mp hnot m)
  have hm : xi.measure Set.univ = ⨆ m, xi.measure (prefixCells m) := by
    rw [← prefixCells_cover]
    exact prefixCells_monotone.measure_iUnion
  have htop : (∞ : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    rw [← hxi,hm]
    apply iSup_le
    intro m
    rw [prefixCells_mass]
    exact_mod_cast hb m
  exact (not_le_of_gt (ENNReal.natCast_lt_top n)) htop

/-- The actual finite sorted list represents each cell restriction. -/
theorem cell_measure_eq_occurrences (xi : LocalCountingMeasure) (z : ℤ) :
    xi.measure.restrict (unitCell z) =
      ∑ k : Fin (cellCount xi z), Measure.dirac (cellOccurrence xi z k.val) := by
  let p := chosenOccurrences (cellCountingMeasure xi z)
  have hc : cellCount xi z = p.count := finiteCount_eq (cellCountingMeasure xi z)
  rw [hc]
  calc
    _ = ∑ k, Measure.dirac (p.location k) := p.measure_eq
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      change p.location k = (if h : k.val < p.count then p.location ⟨k.val,h⟩ else 0)
      rw [dif_pos k.isLt]

/-- The full counting measure is the unit-Dirac sum over cell occurrences. -/
theorem measure_eq_sum_cell_occurrences (xi : LocalCountingMeasure) :
    xi.measure = Measure.sum (fun p : (m : ℕ) × Fin (indexedCellCount xi m) =>
      Measure.dirac (cellOccurrence xi (cellInteger p.1) p.2.val)) := by
  ext A hA
  have hsets : (⋃ m, A ∩ unitCell (cellInteger m)) = A := by
    rw [← Set.inter_iUnion,indexed_unitCell_cover,Set.inter_univ]
  calc
    _ = xi.measure (⋃ m, A ∩ unitCell (cellInteger m)) := congrArg xi.measure hsets.symm
    _ = ∑' m, xi.measure (A ∩ unitCell (cellInteger m)) :=
      measure_iUnion (fun i j hij => Disjoint.mono Set.inter_subset_right Set.inter_subset_right
        (indexed_unitCell_disjoint hij)) (fun m => hA.inter (measurableSet_unitCell _))
    _ = ∑' m, ∑ k : Fin (indexedCellCount xi m),
        (Measure.dirac (cellOccurrence xi (cellInteger m) k.val)) A := by
      apply tsum_congr
      intro m
      have h := congrArg (fun mu : Measure ℝ => mu A) (cell_measure_eq_occurrences xi (cellInteger m))
      dsimp only at h
      rw [Measure.restrict_apply hA,Measure.finset_sum_apply] at h
      exact h
    _ = _ := by
      rw [Measure.sum_apply _ hA,ENNReal.tsum_sigma']
      simp only [tsum_fintype]

abbrev InfiniteCountingMeasure := {xi : LocalCountingMeasure // xi.measure Set.univ = ∞}

def globalCell (xi : InfiniteCountingMeasure) (n : ℕ) : ℕ :=
  prefixCell (indexedCellCount xi.val) (exists_prefix_gt_of_totalMass_top xi.val xi.property) n

def globalRank (xi : InfiniteCountingMeasure) (n : ℕ) : ℕ :=
  n - countPrefix (indexedCellCount xi.val) (globalCell xi n)

def globalOccurrence (xi : InfiniteCountingMeasure) (n : ℕ) : ℝ :=
  cellOccurrence xi.val (cellInteger (globalCell xi n)) (globalRank xi n)

theorem measurable_globalCell (n : ℕ) : Measurable (fun xi : InfiniteCountingMeasure => globalCell xi n) :=
  measurable_prefixCell (S := InfiniteCountingMeasure) (fun xi : InfiniteCountingMeasure => indexedCellCount xi.val)
    (fun m => (measurable_cellCount (cellInteger m)).comp measurable_subtype_coe)
    (fun xi : InfiniteCountingMeasure => exists_prefix_gt_of_totalMass_top xi.val xi.property) n

theorem measurable_globalRank (n : ℕ) : Measurable (fun xi : InfiniteCountingMeasure => globalRank xi n) :=
  measurable_prefixRank (S := InfiniteCountingMeasure) (fun xi : InfiniteCountingMeasure => indexedCellCount xi.val)
    (fun m => (measurable_cellCount (cellInteger m)).comp measurable_subtype_coe)
    (fun xi : InfiniteCountingMeasure => exists_prefix_gt_of_totalMass_top xi.val xi.property) n

section
attribute [local irreducible] cellOccurrence cellCount finiteCount occurrence chosenOccurrences globalCell globalRank

/-- Each canonical global occurrence is genuinely measurable. -/
theorem measurable_globalOccurrence (n : ℕ) :
    Measurable (fun xi : InfiniteCountingMeasure => globalOccurrence xi n) := by
  unfold globalOccurrence
  have hm : Measurable (fun p : LocalCountingMeasure × (ℤ × ℕ) => cellOccurrence p.1 p.2.1 p.2.2) := by
    apply measurable_from_prod_countable
    intro p
    exact measurable_cellOccurrence p.1 p.2
  have hv : Measurable (Subtype.val : InfiniteCountingMeasure → LocalCountingMeasure) := measurable_subtype_coe
  have hc : Measurable (fun xi : InfiniteCountingMeasure => cellInteger (globalCell xi n)) :=
    (measurable_of_countable cellInteger).comp (measurable_globalCell n)
  have hr := measurable_globalRank n
  exact hm.comp (hv.prodMk (hc.prodMk hr))

end

/-- The canonical Nat list represents all particles exactly, including every
occurrence of a repeated atom. -/
theorem measure_eq_sum_global_occurrences (xi : InfiniteCountingMeasure) :
    xi.val.measure = Measure.sum (fun n => Measure.dirac (globalOccurrence xi n)) := by
  rw [measure_eq_sum_cell_occurrences]
  ext A hA
  rw [Measure.sum_apply _ hA,Measure.sum_apply _ hA]
  let e := prefixOccurrenceEquiv (indexedCellCount xi.val)
    (exists_prefix_gt_of_totalMass_top xi.val xi.property)
  exact (e.tsum_eq (fun p => (Measure.dirac (cellOccurrence xi.val (cellInteger p.1) p.2.val)) A)).symm

end GeneralizedBulk.Counting
