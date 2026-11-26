import GeneralizedBulk.Counting.RankedSelection
import GeneralizedBulk.Counting.WindowOccurrences
import BourgadeHuang.FiniteCountingConfiguration

/-! Sorted actual finite indices coincide with the canonical window coordinates. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped ENNReal
namespace GeneralizedBulk.Counting

def windowMask {N : ℕ} (x : Fin N → ℝ) (a b : ℝ) : Fin N → Bool :=
  fun i => decide (x i ∈ Set.Icc a b)

def rankedWindowIndex {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (a b : ℝ) (k : ℕ) : Fin N :=
  rankedIndex hN (windowMask x a b) k

theorem measurable_rankedWindowIndex {S : Type*} [MeasurableSpace S] {N : ℕ}
    (hN : 0 < N) (x : S → Fin N → ℝ) (hx : ∀ i, Measurable (fun s => x s i))
    (a b : ℝ) (k : ℕ) : Measurable (fun s => rankedWindowIndex hN (x s) a b k) := by
  apply measurable_rankedIndex hN _ _ k
  exact measurable_mask S (fun s i => x s i ∈ Set.Icc a b)
    (fun i => measurableSet_Icc.preimage (hx i))

def orderedWindowOccurrences {N : ℕ} (x : Fin N → ℝ) (hx : Antitone x) (a b : ℝ) :
    OrderedOccurrences (windowCountingMeasure (finiteCountingConfiguration x) a b).val := by
  let q := rankedOrderedOccurrences x hx (Set.Icc a b) measurableSet_Icc (windowMask x a b)
    (fun i => by simp [windowMask])
  refine ⟨q.count,q.location,q.monotone_location,?_⟩
  change (finiteCountingConfiguration x).measure.restrict (Set.Icc a b) = _
  rw [finiteCountingConfiguration_measure]
  exact q.measure_eq

theorem window_count_eq_mask_card {N : ℕ} (x : Fin N → ℝ) (hx : Antitone x) (a b : ℝ) :
    intervalCount (finiteCountingConfiguration x) a b = (maskFinset (windowMask x a b)).card := by
  have h := (orderedWindowOccurrences x hx a b).mass_univ
  change (finiteCountingConfiguration x).measure.restrict (Set.Icc a b) Set.univ =
    ((maskFinset (windowMask x a b)).card : ℝ≥0∞) at h
  rw [Measure.restrict_apply_univ,interval_mass_eq_count] at h
  exact_mod_cast h

theorem rankedWindowIndex_matches_occurrence {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℝ) (hx : Antitone x) (a b : ℝ) (k : ℕ)
    (hk : k < intervalCount (finiteCountingConfiguration x) a b) :
    x (rankedWindowIndex hN x a b k) = windowOccurrence (finiteCountingConfiguration x) a b k := by
  have hkc : k < (maskFinset (windowMask x a b)).card := by
    rw [← window_count_eq_mask_card x hx a b]
    exact hk
  have he := (orderedWindowOccurrences x hx a b).occurrence_eq
    (windowCountingMeasure (finiteCountingConfiguration x) a b) ⟨k,hkc⟩
  rw [rankedWindowIndex,rankedIndex,dif_pos hkc]
  exact he.symm

theorem rankedWindowIndex_injective {N m : ℕ} (hN : 0 < N)
    (x : Fin N → ℝ) (hx : Antitone x) (a b : ℝ)
    (hm : m ≤ intervalCount (finiteCountingConfiguration x) a b) :
    Function.Injective (fun k : Fin m => rankedWindowIndex hN x a b k.val) := by
  apply rankedIndex_injective
  rwa [← window_count_eq_mask_card x hx a b]

theorem rankedWindowIndex_mem {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℝ) (hx : Antitone x) (a b : ℝ) (k : ℕ)
    (hk : k < intervalCount (finiteCountingConfiguration x) a b) :
    x (rankedWindowIndex hN x a b k) ∈ Set.Icc a b := by
  have h := rankedIndex_mem hN (windowMask x a b) k
    (by rwa [← window_count_eq_mask_card x hx a b])
  simpa only [windowMask,decide_eq_true_eq] using h

theorem sum_rankedWindowIndex {N : ℕ} {V : Type*} [AddCommMonoid V]
    (hN : 0 < N) (x : Fin N → ℝ) (hx : Antitone x) (a b : ℝ) (f : Fin N → V) :
    (∑ k : Fin (intervalCount (finiteCountingConfiguration x) a b),
      f (rankedWindowIndex hN x a b k.val)) =
      ∑ i ∈ maskFinset (windowMask x a b), f i := by
  classical
  rw [window_count_eq_mask_card x hx a b]
  let S := maskFinset (windowMask x a b)
  let e : Fin S.card ≃ S := Fin.revPerm.trans (S.orderIsoOfFin rfl).toEquiv
  calc
    _ = ∑ k : Fin S.card, f (S.orderEmbOfFin rfl k.rev) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [rankedWindowIndex,rankedIndex,k.isLt,dif_pos]
      rfl
    _ = ∑ i : S, f i.val := Fintype.sum_equiv e _ _ (fun k => rfl)
    _ = _ := Finset.sum_coe_sort _ _

end GeneralizedBulk.Counting
