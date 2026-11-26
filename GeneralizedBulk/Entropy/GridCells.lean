import Mathlib

/-! The actual countable uniform-grid partition and its normalized cell laws. -/
noncomputable section
open MeasureTheory Set Function
open scoped BigOperators ENNReal
namespace GeneralizedBulk.Entropy
variable {I : Type*} [Fintype I]

def gridLabel (a : ℝ) (x : I → ℝ) : I → ℤ := fun i => Int.floor (x i / a)
def gridCell (a : ℝ) (j : I → ℤ) : Set (I → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ico (a * (j i : ℝ)) (a * ((j i : ℝ) + 1)))

theorem measurable_gridLabel (a : ℝ) : Measurable (gridLabel (I := I) a) := by
  unfold gridLabel
  fun_prop

theorem measurableSet_gridCell (a : ℝ) (j : I → ℤ) : MeasurableSet (gridCell a j) :=
  MeasurableSet.univ_pi (fun i => measurableSet_Ico)

theorem mem_gridCell_iff (a : ℝ) (ha : 0 < a) (j : I → ℤ) (x : I → ℝ) :
    x ∈ gridCell a j ↔ gridLabel a x = j := by
  simp only [gridCell, Set.mem_univ_pi, gridLabel, funext_iff]
  apply forall_congr'
  intro i
  rw [Int.floor_eq_iff]
  constructor
  · intro h
    exact ⟨(le_div_iff₀ ha).mpr (by nlinarith [h.1]), (div_lt_iff₀ ha).mpr (by nlinarith [h.2])⟩
  · intro h
    exact ⟨by nlinarith [(le_div_iff₀ ha).mp h.1], by nlinarith [(div_lt_iff₀ ha).mp h.2]⟩

theorem gridCell_eq_fiber (a : ℝ) (ha : 0 < a) (j : I → ℤ) :
    gridCell a j = gridLabel a ⁻¹' {j} := by
  ext x
  simp only [mem_gridCell_iff a ha, Set.mem_preimage, Set.mem_singleton_iff]

theorem pairwiseDisjoint_gridCell (a : ℝ) (ha : 0 < a) : Pairwise (Disjoint on (gridCell (I := I) a)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact hij ((mem_gridCell_iff a ha i x).mp hi |>.symm.trans ((mem_gridCell_iff a ha j x).mp hj))

theorem iUnion_gridCell (a : ℝ) (ha : 0 < a) : (⋃ j : I → ℤ, gridCell a j) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨gridLabel a x, (mem_gridCell_iff a ha _ _).mpr rfl⟩

theorem volume_gridCell (a : ℝ) (j : I → ℤ) :
    volume (gridCell a j) = ENNReal.ofReal a ^ Fintype.card I := by
  rw [gridCell, Real.volume_pi_Ico]
  have he (i : I) : a * ((j i : ℝ) + 1) - a * (j i : ℝ) = a := by ring
  simp_rw [he]
  simp only [Finset.prod_const, Finset.card_univ]

def gridCellLaw (a : ℝ) (j : I → ℤ) : Measure (I → ℝ) :=
  (ENNReal.ofReal a ^ Fintype.card I)⁻¹ • volume.restrict (gridCell a j)

theorem gridCellLaw_probability (a : ℝ) (ha : 0 < a) (j : I → ℤ) : IsProbabilityMeasure (gridCellLaw a j) := by
  constructor
  rw [gridCellLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter, smul_eq_mul, volume_gridCell]
  exact ENNReal.inv_mul_cancel (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr ha)))
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

theorem hasSum_gridCell_integral (a : ℝ) (ha : 0 < a) (f : (I → ℝ) → ℝ) (hf : Integrable f) :
    HasSum (fun j : I → ℤ => ∫ x in gridCell a j, f x) (∫ x, f x) := by
  have h := hasSum_integral_iUnion (fun j : I → ℤ => measurableSet_gridCell a j)
    (pairwiseDisjoint_gridCell a ha) (hf.integrableOn (s := ⋃ j : I → ℤ, gridCell a j))
  simpa only [iUnion_gridCell a ha, Measure.restrict_univ] using h

end GeneralizedBulk.Entropy
