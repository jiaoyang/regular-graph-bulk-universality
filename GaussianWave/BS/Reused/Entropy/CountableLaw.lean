import GaussianWave.BS.Reused.Entropy.CountableTailSplit

/-! Countable laws are the actual masses of measurable fibers.  Pushforwards
and weighted sums below are identities for an arbitrary correlated law. -/
noncomputable section
open MeasureTheory Set Function
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Entropy

variable {Ω A B : Type*} [MeasurableSpace Ω] [Countable A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

def lawMass (μ : Measure Ω) (X : Ω → A) (a : A) : ℝ := μ.real (X ⁻¹' {a})

theorem lawMass_nonneg (μ : Measure Ω) (X : Ω → A) (a : A) : 0 ≤ lawMass μ X a :=
  measureReal_nonneg

theorem pairwiseDisjoint_fibers (X : Ω → A) : Pairwise (Disjoint on (fun a => X ⁻¹' {a})) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro x ha hb
  exact hab (ha.symm.trans hb)

theorem iUnion_fibers (X : Ω → A) : (⋃ a,X ⁻¹' {a}) = Set.univ := by
  ext x
  simp

theorem lawMass_hasSum (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A)
    (hX : Measurable X) : HasSum (lawMass μ X) 1 := by
  have h := hasSum_integral_iUnion (fun a => hX (measurableSet_singleton a))
    (pairwiseDisjoint_fibers X) ((integrable_const (1 : ℝ) (μ := μ)).integrableOn (s := ⋃ a,X ⁻¹' {a}))
  simpa [lawMass,iUnion_fibers] using h

theorem countablePush_lawMass (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A)
    (hX : Measurable X) (f : A → B) (b : B) :
    countablePush (lawMass μ X) f b = μ.real ((f ∘ X) ⁻¹' {b}) := by
  let E : {a : A // f a = b} → Set Ω := fun a => X ⁻¹' {a.val}
  have hm (a : {a : A // f a = b}) : MeasurableSet (E a) := hX (measurableSet_singleton _)
  have hd : Pairwise (Disjoint on E) := by
    intro a c hac
    exact pairwiseDisjoint_fibers X (fun he => hac (Subtype.ext he))
  have hu : (⋃ a,E a) = (f ∘ X) ⁻¹' {b} := by
    ext x
    simp only [mem_iUnion,mem_preimage,mem_singleton_iff,E,Function.comp_apply]
    constructor
    · rintro ⟨a,ha⟩
      exact (congrArg f ha).trans a.property
    · intro hx
      exact ⟨⟨X x,hx⟩,rfl⟩
  have h := hasSum_integral_iUnion hm hd ((integrable_const (1 : ℝ) (μ := μ)).integrableOn (s := ⋃ a,E a))
  simp only [setIntegral_const,smul_eq_mul,mul_one,hu] at h
  exact h.tsum_eq

theorem lawMass_weighted_hasSum (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (hX : Measurable X) (g : A → ℝ)
    (hg : Integrable (fun x => g (X x)) μ) :
    HasSum (fun a => lawMass μ X a*g a) (∫ x,g (X x) ∂μ) := by
  have h := hasSum_integral_iUnion (fun a => hX (measurableSet_singleton a))
    (pairwiseDisjoint_fibers X) (hg.integrableOn (s := ⋃ a,X ⁻¹' {a}))
  have he (a : A) : (∫ x in X ⁻¹' {a},g (X x) ∂μ) = lawMass μ X a*g a := by
    calc
      _ = ∫ _x in X ⁻¹' {a},g a ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (hX (measurableSet_singleton a))] with x hx
        rw [show X x = a from hx]
      _ = _ := by simp only [setIntegral_const,smul_eq_mul,lawMass]
  simpa only [he,iUnion_fibers,Measure.restrict_univ] using h

end GaussianWave.BS.Reused.Entropy
