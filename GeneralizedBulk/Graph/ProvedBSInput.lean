import GeneralizedBulk.BS.QualitativeInput
import GeneralizedBulk.Graph.HYResolventChannel

/-! The qualitative BS input is proved for the spectral regular-graph model.
The original uniform-graph pushforward assumption is sufficient: graph
measurability, degree handshake and cross-library sampling identities are
derived here. No BS, Gaussianity or HY estimate is a hypothesis. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem provedBS_spectralRegularGraph_eq (n : ℕ) (ω : Ω) :
    GaussianWave.SiblingBulk.spectralRegularGraph D n ω = D.spectralRegularGraph n ω := by
  apply Subtype.ext
  apply SimpleGraph.ext
  rfl

/-- The completed BS proof supplies the original bulk library's exact
qualitative contract from its original uniform-simple-RRG model assumption.
All degree parameters `d >= 3` are covered. -/
def provedBSQualitativeInput
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n, Measure.map (D.spectralRegularGraph n) P = regularGraphLaw (N n) d)
    (hd : 3 ≤ d) (K : Set ℝ) (hcompact : IsCompact K)
    (hstrict : ∀ x ∈ K, |x| < 2 * Real.sqrt (d - 1 : ℝ)) :
    BSQualitativeInput D P K := by
  cases d with
  | zero => omega
  | succ d =>
    cases d with
    | zero => omega
    | succ m =>
      have hm : 0 < m := by omega
      have hΩ : Nonempty Ω := ProbabilityMeasure.nonempty (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
      let ω₀ := Classical.choice hΩ
      have hNE (n : ℕ) : N n * (m + 2) = 2 * (N n * (m + 2) / 2) :=
        regularGraph_handshake (D.spectralRegularGraph n ω₀)
      have hgraph (n : ℕ) : Measurable (GaussianWave.SiblingBulk.spectralRegularGraph D n) := by
        have he : GaussianWave.SiblingBulk.spectralRegularGraph D n = D.spectralRegularGraph n :=
          funext (D.provedBS_spectralRegularGraph_eq n)
        rw [he]
        exact D.measurable_spectralRegularGraph n
      have hmodel (n : ℕ) : Measure.map (GaussianWave.SiblingBulk.spectralRegularGraph D n) P =
          GaussianWave.BS.Reused.Graph.regularGraphLaw (N n) (m + 2) := by
        have he : GaussianWave.SiblingBulk.spectralRegularGraph D n = D.spectralRegularGraph n :=
          funext (D.provedBS_spectralRegularGraph_eq n)
        rw [he]
        exact hUniform n
      apply GaussianWave.SiblingBulk.provedBSQualitativeInput hm D P
        (fun n => N n * (m + 2) / 2) hNE hgraph hmodel K hcompact
      intro x hx
      convert hstrict x hx using 1 <;> norm_num <;> ring

end GeneralizedBulk.External.RegularSpectralData
