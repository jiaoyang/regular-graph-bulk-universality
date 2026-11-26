import GaussianWave.BS.ProcessBallEntropyComparison
import GaussianWave.BS.ProcessBallGaussianPropagation
import GaussianWave.BS.ProcessStarRelativeUpper

/-!
# Smooth normalized joint eigenprocess classification

At a common strict-bulk energy, an actual invariant normalized joint tree
eigenprocess with the all-radius finite recoloring property is the actual
joint Gaussian-wave process. The analytic smoothness input is only ordinary
positive finite-entropy witnesses for the actual raw ball marginals.

The proof derives the entropy lower bound, both relative SSA gaps, their
vanishing, the Gaussian star base case, all-radius gluing propagation, and
whole-process equality. None of those conclusions is a theorem hypothesis.
-/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

theorem smooth_normalized_eigenprocess_eq_jointGaussian {r m : ℕ} (hm : 0 < m)
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ChannelTreeInvariant μ) (hi : ∀ av, Integrable (fun x => x av ^ 2) μ)
    (energy : ℝ) (hbulk : |energy| < 2 * Real.sqrt (m + 1))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0)
    (hroot : HasIdentitySecondMoments (rootChannelLaw μ))
    (hfinite : ∀ k, Lower.HasFiniteRecoloringEntropyLower (vertexSiteFirstProcessLaw μ k)
      (edgeSiteFirstProcessLaw μ k) (Lower.rootProcessWindow m μ) ((m + 2 : ℝ) / 2))
    (C : ∀ k, PositiveEntropyDensity (volume : Measure ((Fin r × VertexBallInnovation (m + 2) k) → ℝ)))
    (E : ∀ k, PositiveEntropyDensity (volume : Measure ((Fin r × EdgeBallInnovation (m + 2) k) → ℝ)))
    (hC : ∀ k, (C k).law = jointVertexInnovationProcessLaw μ k)
    (hEE : ∀ k, (E k).law = jointEdgeInnovationProcessLaw μ k) :
    μ = jointGaussianTreeProcessLaw r m energy := by
  let he := abs_energy_lt_degree_of_strict_bulk m energy hbulk
  let c := fun k => vertexBallRelativeEntropy (Fin r) m k energy he (C k)
  let e := fun k => edgeBallRelativeEntropy (Fin r) m k energy he (E k)
  have hupper := process_star_relative_upper_and_gaussian_equality hm μ hμ hi energy hbulk
    hE hroot (C 0) (E 0) (hC 0) (hEE 0)
  have hmono : Antitone (relativeBallBalance c e (m + 2)) :=
    process_relative_entropy_balance_antitone μ hμ energy he hE C E hC hEE
  have hlower (k) : 0 ≤ relativeBallBalance c e (m + 2) k :=
    process_relative_entropy_balance_nonneg hm μ hμ hi energy hbulk hE hfinite C E hC hEE k
  have hzero (k) : relativeBallBalance c e (m + 2) k = 0 :=
    le_antisymm ((hmono (Nat.zero_le k)).trans hupper.1) (hlower k)
  have hCgaps (k) : 0 ≤ vertexOverlapGap c e (m + 2) k :=
    process_vertex_relative_ssa_nonneg μ hμ energy he hE C E hC hEE k
  have hEgaps (k) : 0 ≤ edgeOverlapGap c e k :=
    process_edge_relative_ssa_nonneg μ hμ energy he hE C E hC hEE k
  have hgaps := overlapGaps_zero_of_balances_zero c e (m + 2) (by positivity) hCgaps hEgaps hzero
  have hC0 := hupper.2 (hzero 0)
  apply process_eq_jointGaussian_of_zero_gaps μ hμ energy he hE C E hC hEE hC0
  · intro k
    exact (hgaps k).1
  · intro k
    exact (hgaps k).2

end GaussianWave.BS
