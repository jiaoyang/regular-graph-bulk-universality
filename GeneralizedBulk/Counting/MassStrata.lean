import GeneralizedBulk.Counting.CanonicalPresentation
import GeneralizedBulk.Counting.FiniteGlobalOccurrences

/-!
# Measurable total-mass strata and canonical mark label spaces

Finite total counting mass is an integer. Each finite stratum has the fixed
label space Fin m and the infinite stratum has Nat; no infinite-particle
assumption enters this pre-normalization construction.
-/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped Topology ENNReal
namespace GeneralizedBulk.Counting
open Gaussian

instance : MeasurableSpace (Option ℕ) := ⊤
instance : MeasurableSingletonClass (Option ℕ) := ⟨fun _ => by trivial⟩

def massClass (s : AnchoredCountingState) : Option ℕ :=
  if h : s.val.1.measure Set.univ = ∞ then none else
    some (finiteGlobalCount ⟨s.val.1,h⟩)

theorem massClass_eq_none_iff (s : AnchoredCountingState) :
    massClass s = none ↔ s.val.1.measure Set.univ = ∞ := by
  classical
  by_cases h : s.val.1.measure Set.univ = ∞ <;> simp [massClass,h]

theorem massClass_eq_some_iff (s : AnchoredCountingState) (m : ℕ) :
    massClass s = some m ↔ s.val.1.measure Set.univ = (m : ℝ≥0∞) := by
  classical
  by_cases h : s.val.1.measure Set.univ = ∞
  · simp [massClass,h]
  · have hm := finiteGlobal_mass_eq_count (⟨s.val.1,h⟩ : FiniteGlobalCountingMeasure)
    change s.val.1.measure Set.univ = (finiteGlobalCount ⟨s.val.1,h⟩ : ℝ≥0∞) at hm
    rw [massClass,dif_neg h]
    simp only [Option.some.injEq]
    rw [hm]
    exact_mod_cast (Iff.rfl : finiteGlobalCount ⟨s.val.1,h⟩ = m ↔ finiteGlobalCount ⟨s.val.1,h⟩ = m)

theorem measurable_anchored_mass :
    Measurable (fun s : AnchoredCountingState => s.val.1.measure Set.univ) :=
  (LocalCountingMeasure.measurable_mass MeasurableSet.univ).comp
    (measurable_fst.comp measurable_subtype_coe)

theorem measurable_massClass : Measurable massClass := by
  apply measurable_to_countable'
  intro i
  cases i with
  | none =>
      have heq : massClass ⁻¹' {none} = {s : AnchoredCountingState | s.val.1.measure Set.univ = ∞} := by
        ext s
        exact massClass_eq_none_iff s
      rw [heq]
      exact measurable_anchored_mass (measurableSet_singleton ∞)
  | some m =>
      have heq : massClass ⁻¹' {some m} = {s : AnchoredCountingState | s.val.1.measure Set.univ = (m : ℝ≥0∞)} := by
        ext s
        exact massClass_eq_some_iff s m
      rw [heq]
      exact measurable_anchored_mass (measurableSet_singleton (m : ℝ≥0∞))

abbrev MassState (i : Option ℕ) := {s : AnchoredCountingState // massClass s = i}

def MassLabels : Option ℕ → Type
  | none => ℕ
  | some m => Fin m

instance countable_massLabels (i : Option ℕ) : Countable (MassLabels i) := by
  cases i <;> dsimp [MassLabels] <;> infer_instance

def stratumPresentation : (i : Option ℕ) → MassState i → PresentedState (MassLabels i)
  | none,s => canonicalPresentation ⟨s.val,(massClass_eq_none_iff s.val).mp s.property⟩
  | some m,s => finiteMassPresentation m ⟨s.val,(massClass_eq_some_iff s.val m).mp s.property⟩

@[simp] theorem stratumPresentation_scalar (i : Option ℕ) (s : MassState i) :
    (stratumPresentation i s).scalar = s.val := by cases i <;> rfl

theorem measurable_stratumPresentation (i : Option ℕ) : Measurable (stratumPresentation i) := by
  cases i with
  | none =>
      have h : Measurable (fun s : MassState none =>
          (⟨s.val,(massClass_eq_none_iff s.val).mp s.property⟩ : InfiniteAnchoredState)) :=
        measurable_subtype_coe.subtype_mk
      exact measurable_canonicalPresentation.comp h
  | some m =>
      have h : Measurable (fun s : MassState (some m) =>
          (⟨s.val,(massClass_eq_some_iff s.val m).mp s.property⟩ : FiniteMassAnchoredState m)) :=
        measurable_subtype_coe.subtype_mk
      exact (measurable_finiteMassPresentation m).comp h

theorem measurableSet_massClass (i : Option ℕ) : MeasurableSet {s : AnchoredCountingState | massClass s = i} :=
  measurable_massClass (measurableSet_singleton i)

end GeneralizedBulk.Counting
