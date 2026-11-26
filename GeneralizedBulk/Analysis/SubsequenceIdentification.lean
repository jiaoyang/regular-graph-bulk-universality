import GeneralizedBulk.Analysis.WeakRelations

/-! Actual full-sequence weak convergence from the identification of every
further weak subsequence, including a continuously observed marginal. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Analysis

theorem weakLaw_of_subsequence_identification
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : ℕ → Measure E) (ν : Measure E)
    (hsub : ∀ r : ℕ → ℕ,StrictMono r → ∃ s : ℕ → ℕ,StrictMono s ∧
      External.WeakLawConverges (fun n => μ (r (s n))) ν) :
    External.WeakLawConverges μ ν := by
  intro F
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms,hms,hnsms⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨s,hs,hweak⟩ := hsub (ns ∘ ms) hnsms
  exact ⟨ms ∘ s,by simpa only [Function.comp_def] using hweak F⟩

theorem weakLaw_marginal_of_subsequence_identification
    {E F : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    (μ : ℕ → Measure E) (ν : Measure F) (f : E → F) (hf : Continuous f)
    (hsub : ∀ r : ℕ → ℕ,StrictMono r →
      ∃ (s : ℕ → ℕ) (limit : Measure E),StrictMono s ∧
        External.WeakLawConverges (fun n => μ (r (s n))) limit ∧ limit.map f=ν) :
    External.WeakLawConverges (fun n => (μ n).map f) ν := by
  apply weakLaw_of_subsequence_identification
  intro r hr
  obtain ⟨s,limit,hs,hweak,hidentified⟩ := hsub r hr
  refine ⟨s,hs,?_⟩
  rw [← hidentified]
  exact weakLaw_map _ limit hweak f hf

end GeneralizedBulk.Analysis
