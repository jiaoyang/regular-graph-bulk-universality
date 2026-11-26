import GeneralizedBulk.Graph.TruncationHeightComparison
import GeneralizedBulk.Graph.MeasurableSpectralVariance

/-! Actual joint measurability of the finite centered truncation error. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem measurable_proposalQuadratic (n : ℕ) (k : Fin (N n)) (i j : Fin 4)
    (t : ProposalSample (N n) d) : Measurable (fun ω => D.proposalQuadratic n ω k i j t) := by
  have hi := D.measurable_selectedEigenvector n (fun _ => k)
    (fun ω => D.proposalEndpoints n ω t i) measurable_const (D.measurable_proposalEndpoints n t i)
  have hj := D.measurable_selectedEigenvector n (fun _ => k)
    (fun ω => D.proposalEndpoints n ω t j) measurable_const (D.measurable_proposalEndpoints n t j)
  exact (hi.const_mul (N n:ℝ)).mul hj

theorem measurable_centeredProposalQuadratic (n : ℕ) (hd : 0 < d)
    (k : Fin (N n)) (i j : Fin 4) (t : ProposalSample (N n) d) :
    Measurable (fun ω => D.centeredProposalQuadratic n ω k i j t) := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0,D.size_pos n⟩,⟨0,hd⟩⟩⟩
  have hm : Measurable (fun ω => ∫ t,D.proposalQuadratic n ω k i j t
      ∂uniformOrientedProposals (N n) d) := by
    simp_rw [show uniformOrientedProposals (N n) d=finiteUniform (ProposalSample (N n) d) from rfl,
      integral_finiteUniform]
    exact (Finset.measurable_sum _ (fun t _ => D.measurable_proposalQuadratic n k i j t)).const_mul _
  exact (D.measurable_proposalQuadratic n k i j t).sub hm

theorem measurable_window_centeredPartial (n : ℕ) (hd : 0 < d)
    (E eta : ℝ) (z : ℂ) (i j : Fin 4) (t : ProposalSample (N n) d) :
    Measurable (fun ω => D.centeredPartialProposalResolvent n ω
      (D.eigenvalueWindow n ω E eta) z i j t) := by
  simp only [centeredPartialProposalResolvent,eigenvalueWindow,Finset.sum_filter]
  apply Finset.measurable_sum
  intro k hk
  have he := D.measurable_eigenvalue n k
  have hb : MeasurableSet {ω : Ω | |D.eigenvalue n ω k-E| ≤ eta} :=
    measurableSet_le (he.sub_const E).abs measurable_const
  exact Measurable.ite hb
    ((((he.complex_ofReal.sub_const z).inv.const_mul ((N n:ℂ)⁻¹)).mul
      (D.measurable_centeredProposalQuadratic n hd k i j t).complex_ofReal)) measurable_const

theorem measurable_resolventProposalEntry (n : ℕ) (z : ℂ) (hz : z.im ≠ 0)
    (i j : Fin 4) (t : ProposalSample (N n) d) :
    Measurable (fun ω => D.resolvent n ω z (D.proposalEndpoints n ω t i)
      (D.proposalEndpoints n ω t j)) := by
  have heq (ω : Ω) := D.resolvent_entry n ω z hz
    (D.proposalEndpoints n ω t i) (D.proposalEndpoints n ω t j)
  simp_rw [heq]
  apply Finset.measurable_sum
  intro k hk
  have hi := (D.measurable_selectedEigenvector n (fun _ => k)
    (fun ω => D.proposalEndpoints n ω t i) measurable_const (D.measurable_proposalEndpoints n t i)).complex_ofReal
  have hj := (D.measurable_selectedEigenvector n (fun _ => k)
    (fun ω => D.proposalEndpoints n ω t j) measurable_const (D.measurable_proposalEndpoints n t j)).complex_ofReal
  exact ((((D.measurable_eigenvalue n k).complex_ofReal.sub_const z).inv.mul hi).mul hj)

theorem measurable_proposalMean_entry (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) (i j : Fin 4) :
    Measurable (fun ω => D.proposalMean n ω z i j) := by
  unfold proposalMean complexAverage
  exact (Finset.measurable_sum _ (fun t _ => D.measurable_resolventProposalEntry n z hz i j t)).const_mul _

def microscopicCenteredTruncationError (n : ℕ) (E sigma : ℝ) (hsigma : 0 < sigma)
    (w : GraphNonreal) (R : ℝ) (i j : Fin 4) (z : Ω × ProposalSample (N n) d) : ℂ :=
  D.resolvent n z.1 (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1
      (D.proposalEndpoints n z.1 z.2 i) (D.proposalEndpoints n z.1 z.2 j) -
    D.proposalMean n z.1 (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j -
    D.centeredPartialProposalResolvent n z.1
      (D.eigenvalueWindow n z.1 E (microscopicStep (N n) sigma*R))
      (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j z.2

theorem measurable_microscopicCenteredTruncationError (n : ℕ) (hd : 0 < d)
    (E sigma : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) (R : ℝ) (i j : Fin 4) :
    Measurable (D.microscopicCenteredTruncationError n E sigma hsigma w R i j) := by
  apply measurable_from_prod_countable
  intro t
  exact ((D.measurable_resolventProposalEntry n _
    (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).property i j t).sub
    (D.measurable_proposalMean_entry n _
      (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).property i j)).sub
    (D.measurable_window_centeredPartial n hd E (microscopicStep (N n) sigma*R) _ i j t)

end GeneralizedBulk.External.RegularSpectralData
