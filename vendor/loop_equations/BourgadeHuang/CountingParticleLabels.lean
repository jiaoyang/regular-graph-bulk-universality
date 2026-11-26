import BourgadeHuang.CountingAtomicity
import BourgadeHuang.NevanlinnaPositivity

/-! A countable global particle list, including integer multiplicity, for an
actual locally finite counting measure. Integrable observables are genuine sums
over these labels, which supports canonical entire-product constructions. -/
noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory Filter
namespace BourgadeHuang

/-- Every singleton has its actual integer counting multiplicity. -/
def LocalCountingMeasure.atomMultiplicity (ξ : LocalCountingMeasure) (x : ℝ) : ℕ :=
  (ξ.integer_compacts {x} isCompact_singleton).choose

theorem LocalCountingMeasure.measure_singleton_eq_multiplicity
    (ξ : LocalCountingMeasure) (x : ℝ) : ξ.measure {x} = (ξ.atomMultiplicity x : ℝ≥0∞) :=
  (ξ.integer_compacts {x} isCompact_singleton).choose_spec

theorem LocalCountingMeasure.countable_atoms (ξ : LocalCountingMeasure) : ξ.atoms.Countable := by
  simpa only [LocalCountingMeasure.atoms, id_eq, Set.setOf_eq_eq_singleton, pos_iff_ne_zero] using
    Measure.countable_meas_level_set_pos (μ := ξ.measure) (g := id) measurable_id

/-- An atom of multiplicity m contributes exactly m distinct particle labels. -/
def LocalCountingMeasure.ParticleLabels (ξ : LocalCountingMeasure) :=
  (a : ξ.atoms) × Fin (ξ.atomMultiplicity a.val)

instance LocalCountingMeasure.countable_particleLabels (ξ : LocalCountingMeasure) :
    Countable ξ.ParticleLabels := by
  letI : Countable ξ.atoms := ξ.countable_atoms.to_subtype
  unfold LocalCountingMeasure.ParticleLabels
  infer_instance

def LocalCountingMeasure.particleLocation (ξ : LocalCountingMeasure) (i : ξ.ParticleLabels) : ℝ :=
  i.1.val

/-- The atomless remainder vanishes globally, not just after compact restriction. -/
theorem LocalCountingMeasure.measure_eq_sum_atoms (ξ : LocalCountingMeasure) :
    ξ.measure = Measure.sum (fun a : ξ.atoms => ξ.measure {a.val} • Measure.dirac a.val) := by
  classical
  letI : Countable ξ.atoms := ξ.countable_atoms.to_subtype
  have hr : ξ.measure.restrict ξ.atoms = ξ.measure :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr ξ.measure_compl_atoms)
  ext s hs
  have hsets : (⋃ a : ξ.atoms, s ∩ {a.val}) = s ∩ ξ.atoms := by
    ext x
    simp only [Set.mem_iUnion,Set.mem_inter_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨a,hxs,hxa⟩
      exact ⟨hxs,hxa ▸ a.property⟩
    · rintro ⟨hxs,hxa⟩
      exact ⟨⟨x,hxa⟩,hxs,rfl⟩
  have hdis : Pairwise (Function.onFun Disjoint (fun a : ξ.atoms => s ∩ {a.val})) := by
    intro a b hab
    apply Disjoint.mono Set.inter_subset_right Set.inter_subset_right
    exact Set.disjoint_singleton.mpr (fun h => hab (Subtype.ext h))
  calc
    ξ.measure s = ξ.measure (s ∩ ξ.atoms) := by
      have h := congrArg (fun μ : Measure ℝ => μ s) hr
      simpa only [Measure.restrict_apply hs] using h.symm
    _ = ∑' a : ξ.atoms, ξ.measure (s ∩ {a.val}) := by
      rw [← hsets]
      exact measure_iUnion hdis (fun a => hs.inter (measurableSet_singleton _))
    _ = _ := by
      rw [Measure.sum_apply _ hs]
      apply tsum_congr
      intro a
      by_cases ha : a.val ∈ s
      · have hsa : s ∩ {a.val} = {a.val} := Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr ha)
        simp [Measure.smul_apply,Measure.dirac_apply' _ hs,ha,hsa]
      · simp [Measure.smul_apply,Measure.dirac_apply' _ hs,ha,Set.inter_singleton_eq_empty.mpr ha]

/-- The actual measure is a countable sum of unit Dirac masses at its particle labels. -/
theorem LocalCountingMeasure.measure_eq_sum_particles (ξ : LocalCountingMeasure) :
    ξ.measure = Measure.sum (fun i : ξ.ParticleLabels => Measure.dirac (ξ.particleLocation i)) := by
  classical
  rw [ξ.measure_eq_sum_atoms]
  ext s hs
  rw [Measure.sum_apply _ hs,Measure.sum_apply _ hs]
  change (∑' a : ξ.atoms, (ξ.measure {a.val} • Measure.dirac a.val) s) =
    ∑' i : (a : ξ.atoms) × Fin (ξ.atomMultiplicity a.val), (Measure.dirac i.1.val) s
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro a
  rw [ξ.measure_singleton_eq_multiplicity]
  simp [Measure.smul_apply,tsum_fintype,nsmul_eq_mul]

/-- Bochner integrability supplies an actual convergent particle sum. -/
theorem LocalCountingMeasure.hasSum_particleLocations {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (ξ : LocalCountingMeasure) {f : ℝ → V} (hf : Integrable f ξ.measure) :
    HasSum (fun i : ξ.ParticleLabels => f (ξ.particleLocation i)) (∫ x, f x ∂ξ.measure) := by
  have hi : Integrable f (Measure.sum (fun i : ξ.ParticleLabels => Measure.dirac (ξ.particleLocation i))) := by
    rwa [← ξ.measure_eq_sum_particles]
  have hh := hasSum_integral_measure hi
  simpa only [integral_dirac,← ξ.measure_eq_sum_particles] using hh

theorem LocalCountingMeasure.summable_norm_particleLocations {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (ξ : LocalCountingMeasure) {f : ℝ → V} (hf : Integrable f ξ.measure) :
    Summable (fun i : ξ.ParticleLabels => ‖f (ξ.particleLocation i)‖) :=
  (ξ.hasSum_particleLocations hf.norm).summable

/-- The Nevanlinna weight is summable over the genuine global particle list. -/
theorem AnchoredCountingState.summable_particle_weight (s : AnchoredCountingState) :
    Summable (fun i : s.val.1.ParticleLabels => nevanlinnaWeight (s.val.1.particleLocation i)) :=
  (s.val.1.hasSum_particleLocations s.integrable_weight).summable

end BourgadeHuang
