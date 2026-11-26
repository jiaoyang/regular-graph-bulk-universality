import GaussianWave.BS.Reused.Graph.UniformMarginals

/-! Uniform finite-source laws and exact projection identities. These
measure identities are independent of the target's dimension or topology. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph

def uniformAtomicLaw {A E : Type*} [Fintype A] [MeasurableSpace E] (mark : A → E) : Measure E :=
  (Fintype.card A : ENNReal)⁻¹ • ∑ a : A, Measure.dirac (mark a)

theorem uniformAtomicLaw_isProbability {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace E] (mark : A → E) : IsProbabilityMeasure (uniformAtomicLaw mark) := by
  constructor
  simp only [uniformAtomicLaw, Measure.smul_apply, Measure.finset_sum_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0))
    (ENNReal.natCast_ne_top _)

theorem uniformAtomicLaw_eq_map {A E : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace E] (mark : A → E) :
    uniformAtomicLaw mark = Measure.map mark (finiteUniform A) := by
  have hm : Measurable mark := measurable_of_finite _
  rw [finiteUniform, ← Measure.mapₗ_apply_of_measurable hm, map_smul, map_sum]
  simp only [Measure.mapₗ_apply_of_measurable hm, Measure.map_dirac hm, uniformAtomicLaw]

theorem uniformAtomicLaw_map {A E F : Type*} [Fintype A]
    [MeasurableSpace E] [MeasurableSpace F] (mark : A → E) (T : E → F) (hT : Measurable T) :
    Measure.map T (uniformAtomicLaw mark) = uniformAtomicLaw (T ∘ mark) := by
  rw [uniformAtomicLaw, ← Measure.mapₗ_apply_of_measurable hT, map_smul, map_sum]
  simp only [Measure.mapₗ_apply_of_measurable hT, Measure.map_dirac hT, uniformAtomicLaw,
    Function.comp_apply]

theorem uniformAtomicLaw_reindex {A B E : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace E] (e : A ≃ B) (mark : B → E) :
    uniformAtomicLaw (mark ∘ e) = uniformAtomicLaw mark := by
  unfold uniformAtomicLaw
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e (fun b => Measure.dirac (mark b))

theorem uniformAtomicLaw_prod_fst {A B E : Type*} [Fintype A] [Fintype B]
    [Nonempty B] [MeasurableSpace E] (mark : A → E) :
    uniformAtomicLaw (fun ab : A × B => mark ab.1) = uniformAtomicLaw mark := by
  have hcardB : (Fintype.card B : ENNReal) ≠ 0 :=
    by exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
  by_cases hA : Nonempty A
  · letI := hA
    letI : MeasurableSpace A := ⊤
    letI : MeasurableSpace B := ⊤
    letI : MeasurableSingletonClass A := ⟨fun _ => trivial⟩
    letI : MeasurableSingletonClass B := ⟨fun _ => trivial⟩
    have hfst : Measure.map (Prod.fst : A × B → A) (finiteUniform (A × B)) = finiteUniform A := by
      apply finiteUniform_map_of_fiber_card Prod.fst (Fintype.card B) Fintype.card_pos
      intro a
      rw [← Fintype.card_subtype]
      let e : {ab : A × B // ab.1 = a} ≃ B :=
        { toFun := fun z => z.val.2
          invFun := fun b => ⟨(a, b), rfl⟩
          left_inv := by rintro ⟨⟨a', b⟩, h⟩; cases h; rfl
          right_inv := fun _ => rfl }
      exact Fintype.card_congr e
    rw [uniformAtomicLaw_eq_map, uniformAtomicLaw_eq_map,
      ← hfst, Measure.map_map (measurable_of_finite mark) measurable_fst]
    rfl
  · haveI : IsEmpty A := not_nonempty_iff.mp hA
    simp [uniformAtomicLaw, Fintype.card_eq_zero]

/-- An exact retained-source/last-layer product decomposition proves
consistency of actual atomic laws. -/
theorem uniformAtomicLaw_projection {A B L E F : Type*}
    [Fintype A] [Fintype B] [Fintype L] [Nonempty L]
    [MeasurableSpace E] [MeasurableSpace F]
    (e : A ≃ B × L) (a : A → E) (b : B → F) (T : E → F) (hT : Measurable T)
    (h : ∀ z, T (a (e.symm z)) = b z.1) :
    Measure.map T (uniformAtomicLaw a) = uniformAtomicLaw b := by
  rw [uniformAtomicLaw_map a T hT]
  have he := uniformAtomicLaw_reindex e.symm (T ∘ a)
  rw [← he]
  have hf : (T ∘ a) ∘ e.symm = fun z : B × L => b z.1 := by
    funext z
    exact h z
  rw [hf]
  exact uniformAtomicLaw_prod_fst b

end GaussianWave.BS
