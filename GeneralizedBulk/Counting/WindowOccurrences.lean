import GeneralizedBulk.Counting.WindowContinuity
import GeneralizedBulk.Counting.CellOccurrences

/-! Measurable sorted window occurrences and their actual vague continuity. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped ENNReal Topology BigOperators
namespace GeneralizedBulk.Counting

def windowCountingMeasure (xi : LocalCountingMeasure) (a b : ℝ) : FiniteCountingMeasure :=
  ⟨xi.measure.restrict (Set.Icc a b),orderedOccurrences_restrict_bounded xi _ _ measurableSet_Icc
    isCompact_Icc Set.Subset.rfl⟩

def windowOccurrence (xi : LocalCountingMeasure) (a b : ℝ) (k : ℕ) : ℝ :=
  occurrence (windowCountingMeasure xi a b) k

theorem measurable_windowCountingMeasure (a b : ℝ) :
    Measurable (fun xi : LocalCountingMeasure => windowCountingMeasure xi a b) :=
  (LocalCountingMeasure.measurable_restrict_compact isCompact_Icc).subtype_mk

theorem measurable_windowOccurrence (a b : ℝ) (k : ℕ) :
    Measurable (fun xi : LocalCountingMeasure => windowOccurrence xi a b k) :=
  (measurable_occurrence k).comp (measurable_windowCountingMeasure a b)

theorem finiteCount_window (xi : LocalCountingMeasure) (a b : ℝ) :
    finiteCount (windowCountingMeasure xi a b) = intervalCount xi a b := by
  simp only [finiteCount,windowCountingMeasure,Measure.restrict_apply_univ,intervalCount]

theorem occurrence_eq_zero_of_count_le (mu : FiniteCountingMeasure) (k : ℕ)
    (hk : finiteCount mu ≤ k) : occurrence mu k = 0 := by
  unfold occurrence
  rw [dif_neg (by simpa only [← finiteCount_eq] using not_lt_of_ge hk)]

theorem occurrence_mem_of_lt_count (mu : FiniteCountingMeasure) (k : ℕ)
    (hk : k < finiteCount mu) (A : Set ℝ) (hA : MeasurableSet A) (hmu : mu.val Aᶜ = 0) :
    occurrence mu k ∈ A := by
  classical
  let p := chosenOccurrences mu
  have hkp : k < p.count := by simpa only [finiteCount_eq] using hk
  have heq : occurrence mu k = p.location ⟨k,hkp⟩ := by
    change (if h : k < p.count then p.location ⟨k,h⟩ else 0) = _
    rw [dif_pos hkp]
  rw [heq]
  have hz : (∑ i, Measure.dirac (p.location i)) Aᶜ = 0 := by rw [← p.measure_eq]; exact hmu
  rw [Measure.finset_sum_apply] at hz
  have hs := Finset.single_le_sum (fun i _ => zero_le ((Measure.dirac (p.location i)) Aᶜ))
    (Finset.mem_univ ⟨k,hkp⟩)
  rw [hz] at hs
  by_contra h
  rw [Measure.dirac_apply' _ hA.compl,Set.indicator_of_mem h] at hs
  exact not_le_of_gt zero_lt_one hs

theorem windowOccurrence_mem (xi : LocalCountingMeasure) (a b : ℝ) (k : ℕ)
    (hk : k < intervalCount xi a b) : windowOccurrence xi a b k ∈ Set.Icc a b := by
  apply occurrence_mem_of_lt_count _ k (by simpa only [finiteCount_window] using hk) _ measurableSet_Icc
  rw [windowCountingMeasure,Measure.restrict_apply measurableSet_Icc.compl,
    Set.compl_inter_self,measure_empty]

theorem windowOccurrence_ne_of_singleton_zero (xi : LocalCountingMeasure) (a b : ℝ) (k : ℕ)
    (hk : k < intervalCount xi a b) (t : ℝ) (ht : xi.measure {t} = 0) :
    windowOccurrence xi a b k ≠ t := by
  have hmu : (windowCountingMeasure xi a b).val ({t}ᶜ)ᶜ = 0 := by
    simp only [compl_compl,windowCountingMeasure,Measure.restrict_apply (measurableSet_singleton t)]
    exact measure_mono_null Set.inter_subset_left ht
  exact occurrence_mem_of_lt_count _ k (by simpa only [finiteCount_window] using hk)
    {t}ᶜ (measurableSet_singleton t).compl hmu

theorem window_strictCount_eq_intervalCount (xi : LocalCountingMeasure) (a b t : ℝ)
    (htb : t ≤ b) (ht : xi.measure {t} = 0) :
    strictCount (windowCountingMeasure xi a b) t = intervalCount xi a t := by
  unfold strictCount intervalCount
  congr 1
  apply congrArg ENNReal.toReal
  rw [windowCountingMeasure,Measure.restrict_apply measurableSet_Iio]
  have heq : Set.Iio t ∩ Set.Icc a b = Set.Ico a t := by
    ext x
    constructor
    · intro hx; exact ⟨hx.2.1,hx.1⟩
    · intro hx; exact ⟨hx.2,⟨hx.1,hx.2.le.trans htb⟩⟩
  rw [heq]
  exact measure_congr (Ico_ae_eq_Icc' ht)

theorem eventually_window_strictCount_eq (xi : LocalCountingMeasure) (a b t : ℝ)
    (ha : xi.measure {a} = 0) (ht : xi.measure {t} = 0) (htb : t ≤ b) :
    ∀ᶠ eta in 𝓝 xi, strictCount (windowCountingMeasure eta a b) t =
      strictCount (windowCountingMeasure xi a b) t := by
  have hsingle : ∀ᶠ eta in 𝓝 xi, eta.measure {t} = 0 := by
    have h := eventually_intervalCount_eq xi t t ht ht
    filter_upwards [h] with eta heta
    have hm := interval_mass_eq_count eta t t
    have hz : intervalCount xi t t = 0 := by simp only [intervalCount,Set.Icc_self,ht,ENNReal.toReal_zero,Nat.floor_zero]
    simpa only [Set.Icc_self,heta,hz,Nat.cast_zero] using hm
  filter_upwards [eventually_intervalCount_eq xi a t ha ht,hsingle] with eta hc he
  rw [window_strictCount_eq_intervalCount eta a b t htb he,
    window_strictCount_eq_intervalCount xi a b t htb ht,hc]

theorem exists_nonatom_between (xi : LocalCountingMeasure) (a b : ℝ) (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, xi.measure {t} = 0 := by
  classical
  have hc : Set.Countable {t : ℝ | xi.measure {t} ≠ 0} := by
    simpa only [pos_iff_ne_zero] using
      (Measure.countable_meas_pos_of_disjoint_iUnion (μ := xi.measure)
        (fun t : ℝ => measurableSet_singleton t) (fun a b hab => Set.disjoint_singleton.mpr hab))
  have heq := measure_diff_null (s := Set.Ioo a b) (hc.measure_zero volume)
  have hp : 0 < volume (Set.Ioo a b \ {t | xi.measure {t} ≠ 0}) := by
    rw [heq,Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  obtain ⟨t,ht⟩ := nonempty_of_measure_ne_zero hp.ne'
  exact ⟨t,ht.1,not_not.mp ht.2⟩

theorem continuousAt_windowOccurrence (xi : LocalCountingMeasure) (a b : ℝ) (k : ℕ)
    (ha : xi.measure {a} = 0) (hb : xi.measure {b} = 0) :
    ContinuousAt (fun eta : LocalCountingMeasure => windowOccurrence eta a b k) xi := by
  classical
  have hcount := eventually_intervalCount_eq xi a b ha hb
  by_cases hk : k < intervalCount xi a b
  · let x := windowOccurrence xi a b k
    have hx := windowOccurrence_mem xi a b k hk
    have hxa : a < x := lt_of_le_of_ne hx.1
      (windowOccurrence_ne_of_singleton_zero xi a b k hk a ha).symm
    have hxb : x < b := lt_of_le_of_ne hx.2
      (windowOccurrence_ne_of_singleton_zero xi a b k hk b hb)
    apply Metric.tendsto_nhds.mpr
    intro epsilon hepsilon
    obtain ⟨l,hl,hl0⟩ := exists_nonatom_between xi (max a (x - epsilon)) x
      (max_lt hxa (by linarith))
    obtain ⟨u,hu,hu0⟩ := exists_nonatom_between xi x (min b (x + epsilon))
      (lt_min hxb (by linarith))
    have hcu : k < strictCount (windowCountingMeasure xi a b) u := by
      rcases (occurrence_lt_iff (windowCountingMeasure xi a b) k u).mp hu.1 with h | h
      · exact h.2
      · exact False.elim (not_le_of_gt (by simpa only [finiteCount_window] using hk) h.1)
    have hcl : ¬k < strictCount (windowCountingMeasure xi a b) l := by
      intro h
      have hh := (occurrence_lt_iff (windowCountingMeasure xi a b) k l).mpr
        (Or.inl ⟨by simpa only [finiteCount_window] using hk,h⟩)
      exact not_lt_of_ge hl.2.le hh
    filter_upwards [hcount,eventually_window_strictCount_eq xi a b l ha hl0
      (hl.2.le.trans hxb.le),eventually_window_strictCount_eq xi a b u ha hu0
        (hu.2.trans_le (min_le_left _ _)).le] with eta hc hcl' hcu'
    have hket : k < finiteCount (windowCountingMeasure eta a b) := by rw [finiteCount_window,hc]; exact hk
    have hupper : windowOccurrence eta a b k < u :=
      (occurrence_lt_iff _ k u).mpr (Or.inl ⟨hket,by rw [hcu']; exact hcu⟩)
    have hlower : l ≤ windowOccurrence eta a b k := by
      apply le_of_not_gt
      intro hh
      rcases (occurrence_lt_iff _ k l).mp hh with h | h
      · rw [hcl'] at h
        exact hcl h.2
      · exact not_le_of_gt hket h.1
    rw [Real.dist_eq]
    change |windowOccurrence eta a b k - x| < epsilon
    apply abs_lt.mpr
    constructor
    · linarith [hl.1,le_max_right a (x - epsilon)]
    · linarith [hu.2,min_le_right b (x + epsilon)]
  · have hz : windowOccurrence xi a b k = 0 := occurrence_eq_zero_of_count_le _ k
      (by simpa only [finiteCount_window] using le_of_not_gt hk)
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [hcount] with eta hc
    change windowOccurrence eta a b k = windowOccurrence xi a b k
    rw [hz]
    exact occurrence_eq_zero_of_count_le _ k (by rw [finiteCount_window,hc]; exact le_of_not_gt hk)

end GeneralizedBulk.Counting
