import GeneralizedBulk.Counting.FiniteOccurrences

/-! Equal finite unit-Dirac measures have label bijections preserving every
particle location, including multiplicities. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace GeneralizedBulk.Counting

theorem finite_dirac_presentations_equiv {I J : Type*} [Fintype I] [Fintype J]
    (x : I → ℝ) (y : J → ℝ)
    (heq : (∑ i, Measure.dirac (x i)) = ∑ j, Measure.dirac (y j)) :
    ∃ e : I ≃ J, ∀ i, y (e i) = x i := by
  classical
  have hcard (t : ℝ) : Fintype.card {i : I // x i = t} = Fintype.card {j : J // y j = t} := by
    have h := congrArg (fun μ : Measure ℝ => μ {t}) heq
    dsimp only at h
    rw [Measure.finset_sum_apply,Measure.finset_sum_apply] at h
    simp only [Measure.dirac_apply' _ (measurableSet_singleton t),Set.indicator_apply,
      Set.mem_singleton_iff,Pi.one_apply] at h
    have hx : (∑ i : I, if x i = t then (1 : ℝ≥0∞) else 0) =
        (Fintype.card {i : I // x i = t} : ℝ≥0∞) := by
      rw [Fintype.card_subtype]
      exact Finset.sum_boole _ _
    have hy : (∑ j : J, if y j = t then (1 : ℝ≥0∞) else 0) =
        (Fintype.card {j : J // y j = t} : ℝ≥0∞) := by
      rw [Fintype.card_subtype]
      exact Finset.sum_boole _ _
    rw [hx,hy] at h
    exact_mod_cast h
  let ef (t : ℝ) : {i : I // x i = t} ≃ {j : J // y j = t} := Fintype.equivOfCardEq (hcard t)
  let e : I ≃ J := (Equiv.sigmaFiberEquiv x).symm.trans
    ((Equiv.sigmaCongrRight ef).trans (Equiv.sigmaFiberEquiv y))
  refine ⟨e,?_⟩
  intro i
  change y (ef (x i) ⟨i,rfl⟩).val = x i
  exact (ef (x i) ⟨i,rfl⟩).property

end GeneralizedBulk.Counting
