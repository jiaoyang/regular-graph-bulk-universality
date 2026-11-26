import GeneralizedBulk.Graph.PolynomialVariance

/-! Measurability of literal finite spectral proposal means and variances. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph

theorem measurable_finiteUniform_variance
    {A Ω : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace Ω] (F : Ω → A → ℂ) (hF : ∀ a, Measurable (fun ω => F ω a)) :
    Measurable (fun ω => ∫ a, ‖F ω a - ∫ x, F ω x ∂finiteUniform A‖ ^ 2 ∂finiteUniform A) := by
  have hmean : Measurable (fun ω => ∫ x, F ω x ∂finiteUniform A) := by
    have heq : (fun ω => ∫ x, F ω x ∂finiteUniform A) =
        (fun ω => (Fintype.card A : ℂ)⁻¹ * ∑ a, F ω a) :=
      funext (fun ω => integral_finiteUniform_complex (F ω))
    rw [heq]
    exact (Finset.measurable_sum _ (fun a _ => hF a)).const_mul _
  have heq : (fun ω => ∫ a, ‖F ω a - ∫ x, F ω x ∂finiteUniform A‖ ^ 2 ∂finiteUniform A) =
      (fun ω => (Fintype.card A : ℝ)⁻¹ * ∑ a, ‖F ω a - ∫ x, F ω x ∂finiteUniform A‖ ^ 2) :=
    funext (fun ω => integral_finiteUniform _)
  rw [heq]
  exact (Finset.measurable_sum _ (fun a _ => ((hF a).sub hmean).norm.pow_const 2)).const_mul _

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ)

theorem measurable_proposalEndpoints (s : ProposalSample (N n) d) (i : Fin 4) :
    Measurable (fun ω => D.proposalEndpoints n ω s i) := by
  fin_cases i
  · exact measurable_const
  · exact D.measurable_neighbor n s.1.1 s.1.2
  · exact measurable_const
  · exact D.measurable_neighbor n s.2.1 s.2.2

theorem measurable_spectralProposalEntry (f : ℝ → ℂ) (hf : Measurable f)
    (i j : Fin 4) (s : ProposalSample (N n) d) :
    Measurable (fun ω => D.spectralMultiplier n ω f (D.proposalEndpoints n ω s i)
      (D.proposalEndpoints n ω s j)) := by
  change Measurable (fun ω => ∑ k : Fin (N n), f (D.eigenvalue n ω k) *
    (D.eigenvector n ω k (D.proposalEndpoints n ω s i) : ℂ) *
      (D.eigenvector n ω k (D.proposalEndpoints n ω s j) : ℂ))
  apply Finset.measurable_sum
  intro k hk
  have hi := (D.measurable_selectedEigenvector n (fun _ => k)
    (fun ω => D.proposalEndpoints n ω s i) measurable_const (D.measurable_proposalEndpoints n s i)).complex_ofReal
  have hj := (D.measurable_selectedEigenvector n (fun _ => k)
    (fun ω => D.proposalEndpoints n ω s j) measurable_const (D.measurable_proposalEndpoints n s j)).complex_ofReal
  exact ((hf.comp (D.measurable_eigenvalue n k)).mul hi).mul hj

theorem measurable_polynomialProposalEntry (Q : Polynomial ℝ) (i j : Fin 4)
    (s : ProposalSample (N n) d) : Measurable (fun ω => D.polynomialProposalEntry n ω Q i j s) := by
  have heq : (fun ω => D.polynomialProposalEntry n ω Q i j s) =
      (fun ω => D.spectralMultiplier n ω (fun x => ((Q.eval x : ℝ) : ℂ))
        (D.proposalEndpoints n ω s i) (D.proposalEndpoints n ω s j)) := by
    funext ω
    exact congrArg (fun M : Matrix (Fin (N n)) (Fin (N n)) ℂ =>
      M (D.proposalEndpoints n ω s i) (D.proposalEndpoints n ω s j))
      (D.polynomialMatrix_eq_spectralMultiplier n ω Q)
  rw [heq]
  exact D.measurable_spectralProposalEntry n _ Q.continuous.measurable.complex_ofReal i j s

theorem measurable_polynomialProposalVariance (hd : 0 < d) (Q : Polynomial ℝ) (i j : Fin 4) :
    Measurable (fun ω => D.polynomialProposalVariance n ω Q i j) := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0,D.size_pos n⟩,⟨0,hd⟩⟩⟩
  exact measurable_finiteUniform_variance (fun ω s => D.polynomialProposalEntry n ω Q i j s)
    (fun s => D.measurable_polynomialProposalEntry n Q i j s)

end GeneralizedBulk.External.RegularSpectralData
