import GeneralizedBulk.Entropy.GridEntropyPair

/-! The grid-cell pair region is dominated by bounded translations of Lebesgue measure. -/
noncomputable section
open MeasureTheory Set Function
open scoped BigOperators ENNReal
namespace GeneralizedBulk.Entropy
variable {I : Type*} [Fintype I]

def sameGridPair (a : ℝ) : Set ((I → ℝ) × (I → ℝ)) :=
  {z | gridLabel a z.1 = gridLabel a z.2}

def gridShiftBox (a : ℝ) : Set (I → ℝ) := Set.Icc (fun _ => -a) (fun _ => a)

theorem measurableSet_sameGridPair (a : ℝ) : MeasurableSet (sameGridPair (I := I) a) :=
  measurableSet_eq_fun ((measurable_gridLabel a).comp measurable_fst) ((measurable_gridLabel a).comp measurable_snd)

theorem sameGridPair_eq_iUnion (a : ℝ) (ha : 0 < a) :
    sameGridPair (I := I) a = ⋃ j : I → ℤ, (gridCell a j) ×ˢ (gridCell a j) := by
  ext z
  constructor
  · intro hz
    exact Set.mem_iUnion.mpr ⟨gridLabel a z.1,
      (mem_gridCell_iff a ha _ _).mpr rfl, (mem_gridCell_iff a ha _ _).mpr hz.symm⟩
  · intro hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    exact ((mem_gridCell_iff a ha j z.1).mp hj.1).trans ((mem_gridCell_iff a ha j z.2).mp hj.2).symm

theorem pairwiseDisjoint_gridCell_prod (a : ℝ) (ha : 0 < a) :
    Pairwise (Disjoint on (fun j : I → ℤ => gridCell a j ×ˢ gridCell a j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  exact Set.disjoint_left.mp (pairwiseDisjoint_gridCell a ha hij) hi.1 hj.1

theorem lintegral_sameGridPair_eq_tsum (a : ℝ) (ha : 0 < a)
    (Φ : ((I → ℝ) × (I → ℝ)) → ℝ≥0∞) :
    (∫⁻ z in sameGridPair a, Φ z ∂(volume.prod volume)) =
      ∑' j : I → ℤ, ∫⁻ z in gridCell a j ×ˢ gridCell a j, Φ z ∂(volume.prod volume) := by
  rw [sameGridPair_eq_iUnion a ha]
  exact lintegral_iUnion (fun j => (measurableSet_gridCell a j).prod (measurableSet_gridCell a j))
    (pairwiseDisjoint_gridCell_prod a ha) Φ

theorem lintegral_sameGridPair_le_translations (a : ℝ) (ha : 0 < a)
    (Φ : ((I → ℝ) × (I → ℝ)) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ z in sameGridPair a, Φ z ∂(volume.prod volume)) ≤
      ∫⁻ h in gridShiftBox a, ∫⁻ x, Φ (x, x + h) := by
  let Ψ := (sameGridPair a).indicator Φ
  have hΨ : Measurable Ψ := hΦ.indicator (measurableSet_sameGridPair a)
  let T : ((I → ℝ) × (I → ℝ)) → ((I → ℝ) × (I → ℝ)) := fun z => (z.1, z.1 + z.2)
  have hT : Measurable T := by fun_prop
  let B : Set ((I → ℝ) × (I → ℝ)) := Prod.snd ⁻¹' gridShiftBox a
  have hB : MeasurableSet B := measurableSet_Icc.preimage measurable_snd
  let upper : ((I → ℝ) × (I → ℝ)) → ℝ≥0∞ := B.indicator (fun z => Φ (T z))
  have hu : Measurable upper := (hΦ.comp hT).indicator hB
  have hbound (z : (I → ℝ) × (I → ℝ)) : Ψ (T z) ≤ upper z := by
    by_cases hz : T z ∈ sameGridPair a
    · have hb : z ∈ B := by
        change (fun _ => -a) ≤ z.2 ∧ z.2 ≤ (fun _ => a)
        have hh (i : I) : |z.2 i| ≤ a := by
          have h := grid_same_cell_difference a ha z.1 (z.1 + z.2) hz i
          simpa only [Pi.add_apply, add_sub_cancel_left] using h
        exact ⟨fun i => (abs_le.mp (hh i)).1, fun i => (abs_le.mp (hh i)).2⟩
      simp only [Ψ, upper, Set.indicator_of_mem hz, Set.indicator_of_mem hb]
      exact le_rfl
    · simp only [Ψ, Set.indicator_of_not_mem hz]
      exact zero_le _
  calc
    _ = ∫⁻ z, Ψ z ∂(volume.prod volume) := (lintegral_indicator (measurableSet_sameGridPair a) Φ).symm
    _ = ∫⁻ z, Ψ (T z) ∂(volume.prod volume) :=
      ((measurePreserving_prod_add (volume : Measure (I → ℝ)) volume).lintegral_comp hΨ).symm
    _ ≤ ∫⁻ z, upper z ∂(volume.prod volume) := lintegral_mono hbound
    _ = ∫⁻ h in gridShiftBox a, ∫⁻ x, Φ (x, x + h) := by
      rw [lintegral_prod_symm' upper hu]
      rw [← lintegral_indicator (show MeasurableSet (gridShiftBox (I := I) a) from measurableSet_Icc)]
      apply lintegral_congr
      intro h
      change (∫⁻ x, upper (x,h)) = (gridShiftBox a).indicator (fun h => ∫⁻ x, Φ (x, x + h)) h
      by_cases hh : h ∈ gridShiftBox a
      · rw [Set.indicator_of_mem hh]
        apply lintegral_congr
        intro x
        exact Set.indicator_of_mem (show (x,h) ∈ B from hh) _
      · rw [Set.indicator_of_not_mem hh]
        have he (x : I → ℝ) : upper (x,h) = 0 :=
          Set.indicator_of_not_mem (show (x,h) ∉ B from hh) _
        simp_rw [he]
        simp

end GeneralizedBulk.Entropy
