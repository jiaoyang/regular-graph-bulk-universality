import GeneralizedBulk.Counting.MeanIntensity
import GeneralizedBulk.Counting.FiniteOccurrences
import Mathlib.Topology.UrysohnsLemma

/-!
Actual vague continuity of bounded-window counting at atom-free endpoints.
Integer counts give a stronger conclusion: they are locally constant there.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped ENNReal Topology CompactlySupported
namespace GeneralizedBulk.Counting

def intervalCount (xi : LocalCountingMeasure) (a b : ℝ) : ℕ :=
  ⌊(xi.measure (Set.Icc a b)).toReal⌋₊

theorem interval_mass_eq_count (xi : LocalCountingMeasure) (a b : ℝ) :
    xi.measure (Set.Icc a b) = intervalCount xi a b := by
  obtain ⟨m,hm⟩ := xi.integer_compacts (Set.Icc a b) isCompact_Icc
  simp only [intervalCount,hm,ENNReal.toReal_natCast,Nat.floor_natCast]

theorem measurable_intervalCount (a b : ℝ) :
    Measurable (fun xi : LocalCountingMeasure => intervalCount xi a b) :=
  Nat.floor_mono.measurable.comp (LocalCountingMeasure.measurable_compact_count isCompact_Icc)

/-- A compact continuous test supported inside the window captures exactly
the given configuration's window count when its endpoints are not atoms. -/
theorem exists_window_count_test (xi : LocalCountingMeasure) (a b : ℝ)
    (ha : xi.measure {a} = 0) (hb : xi.measure {b} = 0) :
    ∃ f : ℝ →C_c ℝ, (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x ∉ Set.Icc a b, f x = 0) ∧
      (∫ x, f x ∂xi.measure) = (xi.measure (Set.Icc a b)).toReal := by
  classical
  let A := xi.atoms ∩ Set.Icc a b
  have hA : IsCompact A := (xi.finite_atoms_inter_compact isCompact_Icc).isCompact
  have hAU : A ⊆ Set.Ioo a b := by
    intro x hx
    have hxa : x ≠ a := by
      intro h
      exact hx.1 (h ▸ ha)
    have hxb : x ≠ b := by
      intro h
      exact hx.1 (h ▸ hb)
    exact ⟨lt_of_le_of_ne hx.2.1 hxa.symm,lt_of_le_of_ne hx.2.2 hxb⟩
  obtain ⟨f,hfone,hfzero,hfs,hfrange⟩ := exists_continuous_one_zero_of_isCompact hA
    isOpen_Ioo.isClosed_compl (Set.disjoint_compl_right_iff_subset.mpr hAU)
  refine ⟨⟨f,hfs⟩,hfrange,?_,?_⟩
  · intro x hx
    exact hfzero (fun h => hx ⟨h.1.le,h.2.le⟩)
  · have hzero (x : ℝ) (hx : x ∉ Set.Icc a b) : f x = 0 :=
      hfzero (fun h => hx ⟨h.1.le,h.2.le⟩)
    have hatoms : ∀ᵐ x ∂xi.measure, x ∈ xi.atoms := ae_iff.mpr xi.measure_compl_atoms
    have heq : f =ᵐ[xi.measure.restrict (Set.Icc a b)] (fun _ => (1 : ℝ)) := by
      filter_upwards [ae_restrict_of_ae hatoms,ae_restrict_mem measurableSet_Icc] with x hx hK
      exact hfone ⟨hx,hK⟩
    change (∫ x, f x ∂xi.measure) = _
    calc
      _ = ∫ x in Set.Icc a b, f x ∂xi.measure :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
      _ = ∫ _x in Set.Icc a b, (1 : ℝ) ∂xi.measure := integral_congr_ae heq
      _ = _ := by simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]

/-- In the actual vague topology, the count on a closed bounded interval is
locally constant at every configuration with atom-free endpoints. -/
theorem eventually_intervalCount_eq (xi : LocalCountingMeasure) (a b : ℝ)
    (ha : xi.measure {a} = 0) (hb : xi.measure {b} = 0) :
    ∀ᶠ eta in 𝓝 xi, intervalCount eta a b = intervalCount xi a b := by
  let m := intervalCount xi a b
  obtain ⟨f,hfrange,hfzero,hInt⟩ := exists_window_count_test xi a b ha hb
  have hmass := interval_mass_eq_count xi a b
  have hIntm : (∫ x, f x ∂xi.measure) = (m : ℝ) := by
    rw [hInt,hmass,ENNReal.toReal_natCast]
  have hup : ∀ᶠ eta in 𝓝 xi, eta.measure (Set.Icc a b) < ((m + 1 : ℕ) : ℝ≥0∞) :=
    LocalCountingMeasure.upperSemicontinuous_compact_mass isCompact_Icc xi _
      (by change xi.measure (Set.Icc a b) < _; rw [hmass]; exact_mod_cast Nat.lt_succ_self m)
  have hlow : ∀ᶠ eta in 𝓝 xi, (m : ℝ) - 1 / 2 < ∫ x, f x ∂eta.measure :=
    ((continuous_linearStatistic f).tendsto xi).eventually
      (Ioi_mem_nhds (by rw [hIntm]; linarith))
  filter_upwards [hup,hlow] with eta hu hl
  have hmasseta := interval_mass_eq_count eta a b
  have hkUpper : intervalCount eta a b ≤ m := by
    rw [hmasseta] at hu
    have hh : intervalCount eta a b < m + 1 := by exact_mod_cast hu
    omega
  have hle := integral_le_measure (μ := eta.measure) (s := Set.Icc a b)
    (fun x hx => (hfrange x).2) (fun x hx => le_of_eq (hfzero x hx))
  rw [hmasseta,← ENNReal.ofReal_natCast] at hle
  have hreal : (∫ x, f x ∂eta.measure) ≤ (intervalCount eta a b : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).mp hle
  have hkLower : m ≤ intervalCount eta a b := by
    by_cases h : m ≤ intervalCount eta a b
    · exact h
    · have hn : intervalCount eta a b + 1 ≤ m := Nat.succ_le_iff.mpr (lt_of_not_ge h)
      have hnr : (intervalCount eta a b : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hn
      linarith
  exact le_antisymm hkUpper hkLower

theorem continuousAt_intervalCount (xi : LocalCountingMeasure) (a b : ℝ)
    (ha : xi.measure {a} = 0) (hb : xi.measure {b} = 0) :
    ContinuousAt (fun eta : LocalCountingMeasure => intervalCount eta a b) xi :=
  continuousAt_const.congr_of_eventuallyEq (eventually_intervalCount_eq xi a b ha hb)

end GeneralizedBulk.Counting
