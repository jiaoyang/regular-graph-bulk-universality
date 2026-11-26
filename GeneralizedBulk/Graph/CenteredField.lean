import GeneralizedBulk.Graph.WindowField
import GeneralizedBulk.Graph.TruncationErrorMeasurable

/-! The literal full covariance-centered finite compression with scalar state. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Gaussian
variable {d : ℕ} {N : ℕ → ℕ} {Ω V : Type*} [MeasurableSpace Ω] [Fintype V]
variable (D : RegularSpectralData d N Ω)

def microscopicCenteredMatrix (n : ℕ) (E : ℝ) (parameters : Parameters)
    (w : GraphNonreal) (z : Ω × ProposalSample (N n) d) : EndpointMatrix :=
  fun i j => D.resolvent n z.1
    (microscopicParameter (N n) (D.size_pos n) E parameters.scale parameters.scale_pos w).val
      (D.proposalEndpoints n z.1 z.2 i) (D.proposalEndpoints n z.1 z.2 j) -
    D.proposalMean n z.1
      (microscopicParameter (N n) (D.size_pos n) E parameters.scale parameters.scale_pos w).val i j

theorem measurable_microscopicCenteredMatrix (n : ℕ) (E : ℝ) (parameters : Parameters)
    (w : GraphNonreal) : Measurable (D.microscopicCenteredMatrix n E parameters w) := by
  change @Measurable _ (Fin 4 → Fin 4 → ℂ) _ (borel _) _
  rw [← @BorelSpace.measurable_eq (Fin 4 → Fin 4 → ℂ) _ MeasurableSpace.pi (by infer_instance)]
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  apply measurable_from_prod_countable
  intro t
  exact (D.measurable_resolventProposalEntry n _
    (microscopicParameter (N n) (D.size_pos n) E parameters.scale parameters.scale_pos w).property i j t).sub
    (D.measurable_proposalMean_entry n _
      (microscopicParameter (N n) (D.size_pos n) E parameters.scale parameters.scale_pos w).property i j)

def microscopicCenteredState (n : ℕ) (E center : ℝ) (parameters : Parameters)
    (w : V → GraphNonreal) (z : Ω × ProposalSample (N n) d) : WindowFieldState V :=
  (D.microscopicCountingState n z.1 E parameters.scale center,
    fun v => D.microscopicCenteredMatrix n E parameters (w v) z)

theorem measurable_microscopicCenteredState (n : ℕ) (E center : ℝ) (parameters : Parameters)
    (w : V → GraphNonreal) : Measurable (D.microscopicCenteredState n E center parameters w) :=
  ((D.measurable_microscopicCountingState n E parameters.scale center).comp measurable_fst).prodMk
    (measurable_pi_lambda _ (fun v => D.measurable_microscopicCenteredMatrix n E parameters (w v)))

end GeneralizedBulk.External.RegularSpectralData
namespace GeneralizedBulk.Gaussian
variable {V : Type*} [Fintype V]
variable (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
variable (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)

def massCenteredState (parameters : Parameters) (spectral : V → ℂ × Bool)
    (z : MassMarkedSample ν) : WindowFieldState V :=
  (massScalarState ν z,fun v => massCenteredField ν hm parameters (spectral v) z)

theorem measurable_massCenteredState (parameters : Parameters) (spectral : V → ℂ × Bool) :
    Measurable (massCenteredState ν hm parameters spectral) :=
  (measurable_massScalarState ν).prodMk
    (measurable_pi_lambda _ (fun v => measurable_massCenteredField ν hm parameters (spectral v)))

end GeneralizedBulk.Gaussian
