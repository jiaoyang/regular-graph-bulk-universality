import GeneralizedBulk.Analysis.ConditionalSubtype
import GeneralizedBulk.Analysis.SigmaMeasurable

/-!
# Countable mixtures of actual conditioned stratum laws

Zero-mass strata are omitted. The weighted mixture recovers the exact
original law and can attach a different independent mark space to each stratum.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace GeneralizedBulk.Analysis
variable {E I : Type*} [MeasurableSpace E] [MeasurableSpace I]
variable [Countable I] [MeasurableSingletonClass I]

def stratumSet (c : E → I) (i : I) : Set E := {x | c x = i}
def ActiveStratum (ν : Measure E) (c : E → I) := {i : I // ν (stratumSet c i) ≠ 0}

def stratumProbability (ν : Measure E) [IsProbabilityMeasure ν]
    (c : E → I) (hc : Measurable c) (i : ActiveStratum ν c) : ProbabilityMeasure (stratumSet c i.val) :=
  conditionalSubtypeLaw ν (stratumSet c i.val) (hc (measurableSet_singleton i.val)) i.property

theorem stratum_cover (c : E → I) : (⋃ i, stratumSet c i) = Set.univ := by ext x; simp [stratumSet]

theorem stratum_disjoint (c : E → I) : Pairwise (fun i j => Disjoint (stratumSet c i) (stratumSet c j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hij (hx.symm.trans hy)

/-- Literal restrictions to positive-mass fibers sum to the full measure. -/
theorem measure_eq_sum_active_stratum_restrict (ν : Measure E) (c : E → I) (hc : Measurable c) :
    ν = Measure.sum (fun i : ActiveStratum ν c => ν.restrict (stratumSet c i.val)) := by
  ext A hA
  have hsets : (⋃ i, A ∩ stratumSet c i) = A := by rw [← Set.inter_iUnion,stratum_cover,Set.inter_univ]
  have hfull : ν A = ∑' i : I, ν (A ∩ stratumSet c i) := by
    calc
      _ = ν (⋃ i, A ∩ stratumSet c i) := congrArg ν hsets.symm
      _ = _ := measure_iUnion (fun i j hij => Disjoint.mono Set.inter_subset_right Set.inter_subset_right
      (stratum_disjoint c hij)) (fun i => hA.inter (hc (measurableSet_singleton i)))
  have hsupport : Function.support (fun i : I => ν (A ∩ stratumSet c i)) ⊆
      {i : I | ν (stratumSet c i) ≠ 0} := by
    intro i hi hz
    exact hi (measure_mono_null Set.inter_subset_right hz)
  rw [Measure.sum_apply _ hA]
  simp only [Measure.restrict_apply hA]
  exact hfull.trans (tsum_subtype_eq_of_support_subset hsupport).symm

theorem active_stratum_mass_sum (ν : Measure E) [IsProbabilityMeasure ν]
    (c : E → I) (hc : Measurable c) :
    (∑' i : ActiveStratum ν c, ν (stratumSet c i.val)) = 1 := by
  have h := congrArg (fun mu : Measure E => mu Set.univ)
    (measure_eq_sum_active_stratum_restrict ν c hc)
  dsimp only at h
  rw [Measure.sum_apply _ MeasurableSet.univ] at h
  simpa only [measure_univ,Measure.restrict_apply_univ] using h.symm

/-- Marks may have a different type and law on every positive-mass stratum. -/
abbrev StratumSample (ν : Measure E) (c : E → I) (T : ActiveStratum ν c → Type*) :=
  (i : ActiveStratum ν c) × ((stratumSet c i.val) × T i)

def stratumMarkedLaw (ν : Measure E) [IsProbabilityMeasure ν]
    (c : E → I) (hc : Measurable c) (T : ActiveStratum ν c → Type*)
    [∀ i, MeasurableSpace (T i)] (Q : ∀ i, Measure (T i)) : Measure (StratumSample ν c T) :=
  Measure.sum (fun i : ActiveStratum ν c => ν (stratumSet c i.val) •
    Measure.map (Sigma.mk i) ((stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i)))

instance stratumMarkedLaw_isProbability (ν : Measure E) [IsProbabilityMeasure ν]
    (c : E → I) (hc : Measurable c) (T : ActiveStratum ν c → Type*)
    [∀ i, MeasurableSpace (T i)] (Q : ∀ i, Measure (T i)) [∀ i, IsProbabilityMeasure (Q i)] :
    IsProbabilityMeasure (stratumMarkedLaw ν c hc T Q) := by
  constructor
  rw [stratumMarkedLaw,Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply,Measure.map_apply (measurable_sigma_mk _) MeasurableSet.univ,
    Set.preimage_univ,measure_univ,smul_eq_mul,mul_one]
  exact active_stratum_mass_sum ν c hc

def stratumSampleValue (ν : Measure E) (c : E → I) (T : ActiveStratum ν c → Type*)
    (z : StratumSample ν c T) : E := z.2.1.val

theorem measurable_stratumSampleValue (ν : Measure E) (c : E → I)
    (T : ActiveStratum ν c → Type*) [∀ i, MeasurableSpace (T i)] :
    Measurable (stratumSampleValue ν c T) := by
  apply measurable_sigma_of_sections
  intro i
  exact measurable_subtype_coe.comp measurable_fst

/-- The mixed marked law has exactly the prescribed scalar-state marginal.
No independence of states across different strata is needed or asserted. -/
theorem stratumMarkedLaw_value_marginal (ν : Measure E) [IsProbabilityMeasure ν]
    (c : E → I) (hc : Measurable c) (T : ActiveStratum ν c → Type*)
    [∀ i, MeasurableSpace (T i)] (Q : ∀ i, Measure (T i)) [∀ i, IsProbabilityMeasure (Q i)] :
    Measure.map (stratumSampleValue ν c T) (stratumMarkedLaw ν c hc T Q) = ν := by
  rw [stratumMarkedLaw,Measure.map_sum (measurable_stratumSampleValue ν c T).aemeasurable]
  have heq (i : ActiveStratum ν c) : Measure.map (stratumSampleValue ν c T)
      (ν (stratumSet c i.val) • Measure.map (Sigma.mk i)
        ((stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i))) =
      ν.restrict (stratumSet c i.val) := by
    rw [Measure.map_smul,Measure.map_map (measurable_stratumSampleValue ν c T) (measurable_sigma_mk i)]
    change ν (stratumSet c i.val) • Measure.map
      ((Subtype.val : stratumSet c i.val → E) ∘ Prod.fst)
      ((stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i)) = _
    rw [← Measure.map_map measurable_subtype_coe measurable_fst,Measure.map_fst_prod,
      measure_univ,one_smul]
    exact mass_smul_map_conditionalSubtypeLaw ν (stratumSet c i.val)
      (hc (measurableSet_singleton i.val)) i.property
  simp_rw [heq]
  exact (measure_eq_sum_active_stratum_restrict ν c hc).symm

end GeneralizedBulk.Analysis
