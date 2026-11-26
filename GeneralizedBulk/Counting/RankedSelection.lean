import GeneralizedBulk.Counting.OccurrenceUniqueness
import GeneralizedBulk.Counting.CellOccurrences
import Mathlib.Data.Finset.Sort

/-! Literal measurable finite indices for sorted window occurrences. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators ENNReal
namespace GeneralizedBulk.Counting

def maskFinset {N : ℕ} (mask : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun i => mask i = true)

def rankedIndex {N : ℕ} (hN : 0 < N) (mask : Fin N → Bool) (k : ℕ) : Fin N :=
  if hk : k < (maskFinset mask).card then
    (maskFinset mask).orderEmbOfFin rfl (Fin.rev ⟨k,hk⟩) else ⟨0,hN⟩

theorem rankedIndex_mem {N : ℕ} (hN : 0 < N) (mask : Fin N → Bool) (k : ℕ)
    (hk : k < (maskFinset mask).card) : mask (rankedIndex hN mask k) = true := by
  rw [rankedIndex,dif_pos hk]
  exact (Finset.mem_filter.mp ((maskFinset mask).orderEmbOfFin_mem rfl _)).2

theorem rankedIndex_injective {N m : ℕ} (hN : 0 < N) (mask : Fin N → Bool)
    (hm : m ≤ (maskFinset mask).card) :
    Function.Injective (fun k : Fin m => rankedIndex hN mask k.val) := by
  intro k l hkl
  simp only [rankedIndex,dif_pos (k.isLt.trans_le hm),dif_pos (l.isLt.trans_le hm)] at hkl
  have h := Fin.rev_injective ((maskFinset mask).orderEmbOfFin rfl |>.injective hkl)
  exact Fin.ext (congrArg (fun i : Fin (maskFinset mask).card => i.val) h)

theorem measurable_mask (S : Type*) [MeasurableSpace S] {N : ℕ} (p : S → Fin N → Prop)
    [∀ s i, Decidable (p s i)] (hp : ∀ i, MeasurableSet {s | p s i}) :
    Measurable (fun s i => decide (p s i)) := by
  apply measurable_pi_lambda
  intro i
  have heq : (fun s => decide (p s i)) = fun s => if p s i then true else false := by
    funext s
    by_cases h : p s i <;> simp [h]
  rw [heq]
  exact Measurable.ite (hp i) measurable_const measurable_const

theorem measurable_rankedIndex {S : Type*} [MeasurableSpace S] {N : ℕ}
    (hN : 0 < N) (mask : S → Fin N → Bool) (hmask : Measurable mask) (k : ℕ) :
    Measurable (fun s => rankedIndex hN (mask s) k) :=
  (measurable_of_finite (fun m : Fin N → Bool => rankedIndex hN m k)).comp hmask

/-- Sorting the retained indices in reverse order sorts an antitone spectral
list increasingly, while every repeated eigenvalue keeps its own index. -/
def rankedOrderedOccurrences {N : ℕ} (x : Fin N → ℝ) (hx : Antitone x)
    (A : Set ℝ) (hA : MeasurableSet A) (mask : Fin N → Bool)
    (hmask : ∀ i, mask i = true ↔ x i ∈ A) :
    OrderedOccurrences ((∑ i, Measure.dirac (x i)).restrict A) where
  count := (maskFinset mask).card
  location := fun k => x ((maskFinset mask).orderEmbOfFin rfl k.rev)
  monotone_location := by
    intro k l hkl
    exact hx ((maskFinset mask).orderEmbOfFin rfl |>.monotone (Fin.rev_le_rev.mpr hkl))
  measure_eq := by
    classical
    let s := maskFinset mask
    have hrestrict : (∑ i, Measure.dirac (x i)).restrict A = ∑ i ∈ s, Measure.dirac (x i) := by
      ext B hB
      rw [Measure.restrict_apply hB,Measure.finset_sum_apply,Measure.finset_sum_apply]
      simp only [Finset.sum_filter,s,maskFinset]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hm : mask i = true
      · simp [Measure.dirac_apply' _ (hB.inter hA),Measure.dirac_apply' _ hB,
          Set.indicator_apply,hm,(hmask i).mp hm]
      · have hn : x i ∉ A := by simpa only [← hmask i] using hm
        simp [Measure.dirac_apply' _ (hB.inter hA),Set.indicator_apply,hm,hn]
    rw [hrestrict,← Finset.sum_coe_sort]
    let e : Fin s.card ≃ s := Fin.revPerm.trans (s.orderIsoOfFin rfl).toEquiv
    exact (Fintype.sum_equiv e (fun k => Measure.dirac (x (s.orderEmbOfFin rfl k.rev)))
      (fun i : s => Measure.dirac (x i.val)) (fun k => rfl)).symm

end GeneralizedBulk.Counting
