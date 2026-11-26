import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

/-! Actual independent coordinates of the infinite product probability measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BourgadeHuang

variable {ι : Type*} {V : ι → Type*} [∀ i, MeasurableSpace (V i)]
    [∀ i, StandardBorelSpace (V i)] (ν : ∀ i, Measure (V i))
    [∀ i, IsProbabilityMeasure (ν i)]

theorem infinitePi_eval_preimage (i : ι) (s : Set (V i)) (hs : MeasurableSet s) :
    Measure.infinitePi ν ((fun ω : ∀ i, V i => ω i) ⁻¹' s) = ν i s := by
  classical
  let t : ∀ j, Set (V j) := fun j => if h : j=i then h ▸ s else Set.univ
  have ht : ∀ j ∈ ({i} : Finset ι), MeasurableSet (t j) := by
    intro j hj
    have : j=i := Finset.mem_singleton.mp hj
    subst j
    simpa [t] using hs
  have he : ((fun ω : ∀ i, V i => ω i) ⁻¹' s) = Set.pi ({i}:Finset ι) t := by
    ext ω
    simp [Set.mem_pi, t]
  rw [he, Measure.infinitePi_pi ν ht]
  simp [t]

theorem infinitePi_map_eval (i : ι) :
    (Measure.infinitePi ν).map (fun ω : ∀ i, V i => ω i) = ν i := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs,
    infinitePi_eval_preimage ν i s hs]

theorem infinitePi_independent_coordinates :
    iIndepFun (fun i (ω : ∀ i, V i) => ω i) (Measure.infinitePi ν) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s t ht
  have he : (⋂ i ∈ s, (fun ω : ∀ i, V i => ω i) ⁻¹' t i) = Set.pi (s:Set ι) t := by
    ext ω
    simp [Set.mem_pi]
  rw [he, Measure.infinitePi_pi ν ht]
  apply Finset.prod_congr rfl
  intro i hi
  exact (infinitePi_eval_preimage ν i (t i) (ht i hi)).symm

end BourgadeHuang
