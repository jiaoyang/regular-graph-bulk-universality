import GeneralizedBulk.Graph.CanonicalSpectralData
import GeneralizedBulk.Graph.ProposalFiberVariance
import Mathlib.Probability.ProductMeasure

/-! The actual countable product of uniform finite labelled graph laws.
Every evaluation marginal is exactly the original regularGraphLaw. -/
noncomputable section
open MeasureTheory
open scoped Classical

namespace GeneralizedBulk.Graph

variable (d : ℕ) (N : ℕ → ℕ)
variable [∀ n, Nonempty (RegularGraph (N n) d)]

def uniformEnsembleLaw : Measure (UniformEnsemble d N) := by
  letI (n : ℕ) : IsProbabilityMeasure (regularGraphLaw (N n) d) :=
    regularGraphLaw_isProbability _ _
  exact Measure.infinitePi (fun n => regularGraphLaw (N n) d)

instance uniformEnsembleLaw_isProbability : IsProbabilityMeasure (uniformEnsembleLaw d N) := by
  letI (n : ℕ) : IsProbabilityMeasure (regularGraphLaw (N n) d) :=
    regularGraphLaw_isProbability _ _
  unfold uniformEnsembleLaw
  infer_instance

theorem uniformEnsembleLaw_map_eval (n : ℕ) :
    Measure.map (fun ω : UniformEnsemble d N => ω n) (uniformEnsembleLaw d N) =
      regularGraphLaw (N n) d := by
  letI (j : ℕ) : IsProbabilityMeasure (regularGraphLaw (N j) d) :=
    regularGraphLaw_isProbability _ _
  let I : Finset ℕ := {n}
  letI : Unique I := {
    default := ⟨n,by simp [I]⟩
    uniq := fun x => Subtype.ext (by simpa only [I,Finset.mem_singleton] using x.property) }
  let e := MeasurableEquiv.piUnique (fun i : I => RegularGraph (N i) d)
  have he : (fun ω : UniformEnsemble d N => ω n) = e ∘ I.restrict := rfl
  have hr : Measurable (I.restrict : UniformEnsemble d N → ∀ i : I,RegularGraph (N i) d) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  rw [he,←Measure.map_map e.measurable hr]
  change Measure.map e ((Measure.infinitePi (fun j => regularGraphLaw (N j) d)).map I.restrict) = _
  rw [Measure.infinitePi_map_restrict]
  exact (measurePreserving_piUnique (fun i : I => regularGraphLaw (N i) d)).map_eq

theorem canonicalSpectralData_spectralRegularGraph
    (hN : ∀ n,0 < N n) (hlim : Filter.Tendsto N Filter.atTop Filter.atTop)
    (n : ℕ) (ω : UniformEnsemble d N) :
    (canonicalSpectralData d N hN hlim).spectralRegularGraph n ω = ω n := by
  apply Subtype.ext
  apply SimpleGraph.ext
  funext v w
  apply propext
  change ((ω n).val.adjMatrix ℝ v w = 1) ↔ (ω n).val.Adj v w
  by_cases h : (ω n).val.Adj v w <;> simp [SimpleGraph.adjMatrix_apply,h]

theorem canonicalSpectralData_uniform
    (hN : ∀ n,0 < N n) (hlim : Filter.Tendsto N Filter.atTop Filter.atTop) (n : ℕ) :
    Measure.map ((canonicalSpectralData d N hN hlim).spectralRegularGraph n)
      (uniformEnsembleLaw d N) = regularGraphLaw (N n) d := by
  have he : (canonicalSpectralData d N hN hlim).spectralRegularGraph n =
      (fun ω : UniformEnsemble d N => ω n) :=
    funext (canonicalSpectralData_spectralRegularGraph d N hN hlim n)
  rw [he]
  exact uniformEnsembleLaw_map_eval d N n

end GeneralizedBulk.Graph
