import GeneralizedBulk.Counting.FiniteOccurrences
import GeneralizedBulk.Gaussian.Presentation

/-! Canonical measurable presentations on every finite total-mass stratum. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators Topology ENNReal Classical
namespace GeneralizedBulk.Counting

/-- Finite total counting mass forces finitely many actual occurrence labels. -/
theorem finite_particleLabels_of_totalMass_ne_top (xi : LocalCountingMeasure)
    (hxi : xi.measure Set.univ ≠ ∞) : Finite xi.ParticleLabels := by
  classical
  by_cases h : Finite xi.ParticleLabels
  · exact h
  · letI : Infinite xi.ParticleLabels := not_finite_iff_infinite.mp h
    have heq := congrArg (fun mu : Measure ℝ => mu Set.univ) xi.measure_eq_sum_particles
    dsimp only at heq
    rw [Measure.sum_apply _ MeasurableSet.univ] at heq
    simp only [Measure.dirac_apply_of_mem (Set.mem_univ _)] at heq
    rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero] at heq
    exact False.elim (hxi heq)

/-- Every finite total-mass counting measure admits a sorted finite global
list, without any bound on the locations of its particles. -/
theorem orderedOccurrences_of_totalMass_ne_top (xi : LocalCountingMeasure)
    (hxi : xi.measure Set.univ ≠ ∞) : Nonempty (OrderedOccurrences xi.measure) := by
  letI : Finite xi.ParticleLabels := finite_particleLabels_of_totalMass_ne_top xi hxi
  letI := Fintype.ofFinite xi.ParticleLabels
  let e := Fintype.equivFin xi.ParticleLabels
  let x : Fin (Fintype.card xi.ParticleLabels) → ℝ := fun j => xi.particleLocation (e.symm j)
  have heq : xi.measure = ∑ j, Measure.dirac (x j) := by
    rw [xi.measure_eq_sum_particles]
    ext A hA
    rw [Measure.sum_apply _ hA,Measure.finset_sum_apply,tsum_fintype]
    exact Fintype.sum_equiv e _ _ (fun j => by simp [x])
  rw [heq]
  exact orderedOccurrences_of_finite_diracs x

abbrev FiniteGlobalCountingMeasure := {xi : LocalCountingMeasure // xi.measure Set.univ ≠ ∞}

def finiteGlobalMeasure (xi : FiniteGlobalCountingMeasure) : FiniteCountingMeasure :=
  ⟨xi.val.measure,orderedOccurrences_of_totalMass_ne_top xi.val xi.property⟩

theorem measurable_finiteGlobalMeasure : Measurable finiteGlobalMeasure :=
  (LocalCountingMeasure.measurable_measure.comp measurable_subtype_coe).subtype_mk

def finiteGlobalCount (xi : FiniteGlobalCountingMeasure) : ℕ := finiteCount (finiteGlobalMeasure xi)
def finiteGlobalOccurrence (xi : FiniteGlobalCountingMeasure) (k : ℕ) : ℝ := occurrence (finiteGlobalMeasure xi) k

theorem measurable_finiteGlobalOccurrence (k : ℕ) :
    Measurable (fun xi : FiniteGlobalCountingMeasure => finiteGlobalOccurrence xi k) :=
  (measurable_occurrence k).comp measurable_finiteGlobalMeasure

theorem finiteGlobal_mass_eq_count (xi : FiniteGlobalCountingMeasure) :
    xi.val.measure Set.univ = finiteGlobalCount xi := by
  have h := (chosenOccurrences (finiteGlobalMeasure xi)).mass_univ
  rw [← finiteCount_eq] at h
  exact h

theorem finiteGlobal_measure_eq_occurrences (xi : FiniteGlobalCountingMeasure) :
    xi.val.measure = ∑ k : Fin (finiteGlobalCount xi), Measure.dirac (finiteGlobalOccurrence xi k.val) := by
  let p := chosenOccurrences (finiteGlobalMeasure xi)
  have hc : finiteGlobalCount xi = p.count := finiteCount_eq (finiteGlobalMeasure xi)
  rw [hc]
  calc
    _ = ∑ k, Measure.dirac (p.location k) := p.measure_eq
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      change p.location k = (if h : k.val < p.count then p.location ⟨k.val,h⟩ else 0)
      rw [dif_pos k.isLt]

abbrev FiniteMassAnchoredState (m : ℕ) := {s : AnchoredCountingState // s.val.1.measure Set.univ = m}

def finiteCountingState {m : ℕ} (s : FiniteMassAnchoredState m) : FiniteGlobalCountingMeasure :=
  ⟨s.val.val.1,by rw [s.property]; exact ENNReal.natCast_ne_top m⟩

theorem measurable_finiteCountingState (m : ℕ) : Measurable (@finiteCountingState m) :=
  (measurable_fst.comp (measurable_subtype_coe.comp measurable_subtype_coe)).subtype_mk

theorem finiteCountingState_count {m : ℕ} (s : FiniteMassAnchoredState m) :
    finiteGlobalCount (finiteCountingState s) = m := by
  have h := finiteGlobal_mass_eq_count (finiteCountingState s)
  change s.val.val.1.measure Set.univ = (finiteGlobalCount (finiteCountingState s) : ℝ≥0∞) at h
  rw [s.property] at h
  exact_mod_cast h.symm

/-- The finite stratum gets its own fixed Fin m mark label space. -/
def finiteMassPresentation (m : ℕ) (s : FiniteMassAnchoredState m) : Gaussian.PresentedState (Fin m) :=
  ⟨(s.val,fun k => finiteGlobalOccurrence (finiteCountingState s) k.val),by
    have h := finiteGlobal_measure_eq_occurrences (finiteCountingState s)
    rw [finiteCountingState_count] at h
    change s.val.val.1.measure = Measure.sum (fun i : Fin m =>
      Measure.dirac (finiteGlobalOccurrence (finiteCountingState s) i.val))
    ext A hA
    rw [Measure.sum_apply _ hA,tsum_fintype]
    have hh := congrArg (fun mu : Measure ℝ => mu A) h
    dsimp only at hh
    rw [Measure.finset_sum_apply] at hh
    exact hh⟩

@[simp] theorem finiteMassPresentation_scalar (m : ℕ) (s : FiniteMassAnchoredState m) :
    (finiteMassPresentation m s).scalar = s.val := rfl

theorem measurable_finiteMassPresentation (m : ℕ) : Measurable (finiteMassPresentation m) := by
  apply Measurable.subtype_mk
  apply measurable_subtype_coe.prodMk
  exact measurable_pi_lambda _ (fun k =>
    (measurable_finiteGlobalOccurrence k.val).comp (measurable_finiteCountingState m))

end GeneralizedBulk.Counting
