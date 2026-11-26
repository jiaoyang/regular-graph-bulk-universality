import GeneralizedBulk.Graph.ScalarTail
import GeneralizedBulk.Graph.SpectralCompression

/-!
# Transport of the proved spectral variances to physical graph fibers

The port sampler is exactly equivalent to the actual two-dart graph fiber.
Thus the selected eigenchannel covariance estimates feed the finite scalar
tail theorem without an extra conditional-law hypothesis.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph Exterior
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def spectralRegularGraph : RegularGraph (N n) d := ⟨D.simpleGraph n ω, D.simpleGraph_regular n ω⟩

/-- The independent root/neighbor-index sampler enumerates exactly once each
ordered pair of graph darts, hence every sample of its graph fiber. -/
def proposalFiberEquiv : ProposalSample (N n) d ≃
    {s : EdgePairState (N n) d // edgePairGraph s = D.spectralRegularGraph n ω} :=
  (Equiv.prodCongr (D.portDartEquiv n ω) (D.portDartEquiv n ω)).trans
    (edgePairGraphFiberEquiv (D.spectralRegularGraph n ω)).symm

theorem proposalFiberEquiv_val (s : ProposalSample (N n) d) :
    (D.proposalFiberEquiv n ω s).val.val = (D.simpleGraph n ω, D.proposalEndpoints n ω s) := rfl

theorem simpleGraph_adjacency_complex :
    (D.simpleGraph n ω).adjMatrix ℂ = (D.adjacency n ω).map Complex.ofReal := by
  ext v w
  rcases D.entry_zero_one n ω v w with hzero | hone
  · simp [SimpleGraph.adjMatrix_apply, simpleGraph, Matrix.map_apply, hzero]
  · simp [SimpleGraph.adjMatrix_apply, simpleGraph, Matrix.map_apply, hone]

theorem graphResolvent_simpleGraph (z : ℂ) :
    graphResolvent (D.simpleGraph n ω) z = D.resolvent n ω z := by
  rw [graphResolvent, D.simpleGraph_adjacency_complex n ω]
  rfl

theorem graphNormalizedScalar_simpleGraph (z : ℂ) :
    graphNormalizedScalar (D.simpleGraph n ω) z = D.scalarResolvent n ω z := by
  rw [graphNormalizedScalar, D.graphResolvent_simpleGraph n ω]
  rfl

theorem graphDeviation_proposalFiberEquiv (hd : 0 < d) (z : ℂ) (hz : z.im ≠ 0)
    (s : ProposalSample (N n) d) (i j : Fin 4) :
    graphDeviation (D.proposalFiberEquiv n ω s).val z i j =
      D.resolvent n ω z (D.proposalEndpoints n ω s i) (D.proposalEndpoints n ω s j) -
        D.proposalMean n ω z i j := by
  change graphBoundary (D.simpleGraph n ω) (D.proposalEndpoints n ω s) z i j -
    finiteMean (N n) d z (graphNormalizedScalar (D.simpleGraph n ω) z) i j = _
  rw [D.graphNormalizedScalar_simpleGraph n ω, ← D.proposalMean_eq_finiteMean n ω hd z hz]
  change graphResolvent (D.simpleGraph n ω) z (D.proposalEndpoints n ω s i)
    (D.proposalEndpoints n ω s j) - _ = _
  rw [D.graphResolvent_simpleGraph n ω]

/-- Conditional graph-fiber variance is exactly the literal independent
port-proposal variance that was estimated from eigenchannel covariances. -/
theorem graphFiber_variance_eq_proposal_variance (hd : 0 < d) (z : ℂ) (hz : z.im ≠ 0) (i j : Fin 4) :
    (∫ s : {s : EdgePairState (N n) d // edgePairGraph s = D.spectralRegularGraph n ω},
      ‖graphDeviation s.val z i j‖ ^ 2
      ∂finiteUniform {s : EdgePairState (N n) d // edgePairGraph s = D.spectralRegularGraph n ω}) =
    (∫ s, ‖D.resolvent n ω z (D.proposalEndpoints n ω s i) (D.proposalEndpoints n ω s j) -
      D.proposalMean n ω z i j‖ ^ 2 ∂uniformOrientedProposals (N n) d) := by
  rw [← finiteUniform_map_equiv (D.proposalFiberEquiv n ω),
    integral_map (measurable_of_finite _).aemeasurable (measurable_of_finite _).aestronglyMeasurable]
  simp_rw [D.graphDeviation_proposalFiberEquiv n ω hd z hz]
  rfl

/-- Actual bulk-window covariance bounds therefore give the conditional
variance required by the scalar-tail mechanism on the physical graph fiber. -/
theorem graphFiber_variance_le_bulk_window (hd : 0 < d)
    (s : Finset (Fin (N n))) (E eta gap : ℝ) (heta : eta ≠ 0) (hgap : 0 < gap)
    (hs : sᶜ ⊆ D.remoteEigenvalues n ω E gap)
    (C epsilon : ℝ) (hC : 0 ≤ C) (i j : Fin 4)
    (hcov : ∀ k ∈ s, ∀ l ∈ s, |∫ t, D.centeredProposalQuadratic n ω k i j t *
        D.centeredProposalQuadratic n ω l i j t ∂uniformOrientedProposals (N n) d| ≤
      C * (if k = l then 1 else 0) + epsilon) :
    (∫ t : {t : EdgePairState (N n) d // edgePairGraph t = D.spectralRegularGraph n ω},
      ‖graphDeviation t.val (spectralParameter E eta) i j‖ ^ 2
      ∂finiteUniform {t : EdgePairState (N n) d // edgePairGraph t = D.spectralRegularGraph n ω}) ≤
      2 * (C * ((D.scalarResolvent n ω (spectralParameter E eta)).im / ((N n : ℝ) * eta)) +
        epsilon * (∑ k ∈ s,
          ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - spectralParameter E eta)⁻¹‖) ^ 2) +
        2 * (2 / gap) ^ 2 := by
  rw [D.graphFiber_variance_eq_proposal_variance n ω hd _ (by simpa using heta)]
  exact D.proposal_resolvent_variance_le_bulk_window n ω hd s E eta gap heta hgap hs C epsilon hC i j hcov

/-- If the explicitly retained off-diagonal covariance error is bounded,
the fiber second moment grows at most linearly in the scalar height. -/
theorem graphFiber_variance_le_linear_height (hd : 0 < d)
    (s : Finset (Fin (N n))) (E eta gap cstar : ℝ) (heta : 0 < eta) (hgap : 0 < gap)
    (hcstar : 0 < cstar) (hheight : cstar ≤ (N n : ℝ) * eta)
    (hs : sᶜ ⊆ D.remoteEigenvalues n ω E gap)
    (C epsilon B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (i j : Fin 4)
    (hcov : ∀ k ∈ s, ∀ l ∈ s, |∫ t, D.centeredProposalQuadratic n ω k i j t *
        D.centeredProposalQuadratic n ω l i j t ∂uniformOrientedProposals (N n) d| ≤
      C * (if k = l then 1 else 0) + epsilon)
    (herror : epsilon * (∑ k ∈ s,
      ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - spectralParameter E eta)⁻¹‖) ^ 2 ≤ B) :
    (∫ t : {t : EdgePairState (N n) d // edgePairGraph t = D.spectralRegularGraph n ω},
      ‖graphDeviation t.val (spectralParameter E eta) i j‖ ^ 2
      ∂finiteUniform {t : EdgePairState (N n) d // edgePairGraph t = D.spectralRegularGraph n ω}) ≤
      (2 * C / cstar + 2 * B + 2 * (2 / gap) ^ 2) *
        (1 + graphHeight (D.spectralRegularGraph n ω) (spectralParameter E eta)) := by
  have hp := D.graphFiber_variance_le_bulk_window n ω hd s E eta gap heta.ne' hgap hs C epsilon hC i j hcov
  have hscalar : (D.scalarResolvent n ω (spectralParameter E eta)).im / ((N n : ℝ) * eta) ≤
      ‖D.scalarResolvent n ω (spectralParameter E eta)‖ / cstar := by
    calc
      _ ≤ ‖D.scalarResolvent n ω (spectralParameter E eta)‖ / ((N n : ℝ) * eta) :=
        div_le_div_of_nonneg_right (Complex.im_le_norm _) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (norm_nonneg _) hcstar hheight
  have hprod := mul_le_mul_of_nonneg_left hscalar hC
  have hg : graphHeight (D.spectralRegularGraph n ω) (spectralParameter E eta) =
      ‖D.scalarResolvent n ω (spectralParameter E eta)‖ := by
    change ‖graphNormalizedScalar (D.simpleGraph n ω) _‖ = _
    rw [D.graphNormalizedScalar_simpleGraph n ω]
  rw [hg]
  have hcoef : 0 ≤ 2 * C / cstar := by positivity
  have hconst : 0 ≤ 2 * B + 2 * (2 / gap) ^ 2 := by positivity
  have hcross := mul_nonneg hconst (norm_nonneg (D.scalarResolvent n ω (spectralParameter E eta)))
  calc
    _ ≤ 2 * (C * (‖D.scalarResolvent n ω (spectralParameter E eta)‖ / cstar) + B) +
        2 * (2 / gap) ^ 2 := by linarith only [hp, hprod, herror]
    _ = (2 * C / cstar) * ‖D.scalarResolvent n ω (spectralParameter E eta)‖ +
        (2 * B + 2 * (2 / gap) ^ 2) := by ring
    _ ≤ _ := by nlinarith only [hcoef, hcross]

end GeneralizedBulk.External.RegularSpectralData
