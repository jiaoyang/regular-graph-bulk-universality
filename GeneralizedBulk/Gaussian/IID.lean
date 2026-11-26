import Mathlib

/-! # Actual independent product measures for particle marks -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GeneralizedBulk.Gaussian

def iidLaw {E : Type*} [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] (I : Type*) : Measure (I → E) :=
  Measure.infinitePi (fun _ : I => ν)

instance {E : Type*} [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] (I : Type*) : IsProbabilityMeasure (iidLaw ν I) := by
  unfold iidLaw
  infer_instance

theorem iidLaw_map_eval {E : Type*} [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] (I : Type*) (i : I) :
    Measure.map (fun ω : I → E => ω i) (iidLaw ν I) = ν := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  have heq : (fun ω : I → E => ω i) ⁻¹' s =
      Set.pi ({i} : Finset I) (fun _ => s) := by
    ext ω
    simp [Set.mem_pi]
  rw [heq, iidLaw, Measure.infinitePi_pi _ (fun j _ => hs)]
  simp

theorem iidLaw_eval_measurePreserving {E : Type*} [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] (I : Type*) (i : I) :
    MeasurePreserving (fun ω : I → E => ω i) (iidLaw ν I) ν :=
  ⟨measurable_pi_apply i, iidLaw_map_eval ν I i⟩

theorem iidLaw_eval_iIndepFun {E : Type*} [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] (I : Type*) :
    iIndepFun (fun i (ω : I → E) => ω i) (iidLaw ν I) := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  have heq : (⋂ i ∈ S, (fun ω : I → E => ω i) ⁻¹' sets i) = Set.pi S sets := by
    ext ω
    simp [Set.mem_pi]
  rw [heq, iidLaw, Measure.infinitePi_pi _ hsets]
  apply Finset.prod_congr rfl
  intro i hi
  have hm := congrArg (fun m : Measure E => m (sets i)) (iidLaw_map_eval ν I i)
  change Measure.map (fun ω : I → E => ω i) (iidLaw ν I) (sets i) = ν (sets i) at hm
  rw [Measure.map_apply (measurable_pi_apply i) (hsets i hi)] at hm
  exact hm.symm

theorem integral_iid_eval {E G : Type*} [MeasurableSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (ν : Measure E) [IsProbabilityMeasure ν] (I : Type*) (i : I)
    (f : E → G) (hf : AEStronglyMeasurable f ν) :
    (∫ ω : I → E, f (ω i) ∂iidLaw ν I) = ∫ x, f x ∂ν := by
  have hfm : AEStronglyMeasurable f (Measure.map (fun ω : I → E => ω i) (iidLaw ν I)) := by
    rw [iidLaw_map_eval]
    exact hf
  have h := integral_map (φ := fun ω : I → E => ω i) (f := f)
    (measurable_pi_apply i).aemeasurable hfm
  rw [iidLaw_map_eval] at h
  exact h.symm

def coordinateAction {E : Type*} (f : E → E) {I : Type*} (ω : I → E) (i : I) : E := f (ω i)

theorem measurable_coordinateAction {E : Type*} [MeasurableSpace E]
    {f : E → E} (hf : Measurable f) (I : Type*) :
    Measurable (coordinateAction f (I := I)) := by
  exact measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i))

/-- A measure-preserving transformation of one mark acts measure-preservingly
on the actual infinite independent product, for any particle label type. -/
theorem iidLaw_coordinateAction_invariant {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (I : Type*)
    (f : E → E) (hf : Measurable f) (hmap : Measure.map f ν = ν) :
    Measure.map (coordinateAction f (I := I)) (iidLaw ν I) = iidLaw ν I := by
  classical
  apply Measure.eq_infinitePi (fun _ : I => ν)
  intro S sets hsets
  rw [Measure.map_apply (measurable_coordinateAction hf I)
    (MeasurableSet.pi (Finset.countable_toSet S) (fun i hi => hsets i hi))]
  have heq : coordinateAction f ⁻¹' Set.pi S sets = Set.pi S (fun i => f ⁻¹' sets i) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, coordinateAction]
  rw [heq, iidLaw, Measure.infinitePi_pi _ (fun i hi => hf (hsets i hi))]
  apply Finset.prod_congr rfl
  intro i hi
  have h := congrArg (fun m : Measure E => m (sets i)) hmap
  change Measure.map f ν (sets i) = ν (sets i) at h
  rw [Measure.map_apply hf (hsets i hi)] at h
  exact h

theorem iidLaw_coordinateAction_measurePreserving {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (I : Type*)
    (f : E → E) (hf : Measurable f) (hmap : Measure.map f ν = ν) :
    MeasurePreserving (coordinateAction f (I := I)) (iidLaw ν I) (iidLaw ν I) :=
  ⟨measurable_coordinateAction hf I, iidLaw_coordinateAction_invariant ν I f hf hmap⟩

theorem iidLaw_map_injectiveSelection {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (I : Type*)
    {J : Type*} [Fintype J] (e : J → I) (he : Function.Injective e) :
    Measure.map (fun ω : I → E => fun j : J => ω (e j)) (iidLaw ν I) =
      Measure.pi (fun _ : J => ν) := by
  have hind := (iidLaw_eval_iIndepFun ν I).precomp he
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map
    (fun j : J => (measurable_pi_apply (e j)).aemeasurable)).mp hind
  simpa only [iidLaw_map_eval] using hmap

end GeneralizedBulk.Gaussian
