import GaussianWave.BS.ProcessEntropyLower
import GaussianWave.BS.EntropySequenceAlgebra

/-!
# The genuine relative entropy lower bound for smooth joint eigenprocesses

Both overlap SSA inequalities are derived from the actual process laws.
The all-radius finite recoloring property is the discrete graph-counting
input, rather than a differential entropy inequality. The independent
Gaussian intrinsic reference asymptotic and actual chart invariance then
prove nonnegativity of every relative C/E entropy balance.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GaussianWave.BS

section
variable {r m : ℕ} (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    (hμ : ChannelTreeInvariant μ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0)
    (C : ∀ k, PositiveEntropyDensity (volume : Measure ((Fin r × VertexBallInnovation (m + 2) k) → ℝ)))
    (E : ∀ k, PositiveEntropyDensity (volume : Measure ((Fin r × EdgeBallInnovation (m + 2) k) → ℝ)))
    (hC : ∀ k, (C k).law = jointVertexInnovationProcessLaw μ k)
    (hEE : ∀ k, (E k).law = jointEdgeInnovationProcessLaw μ k)

include hμ hE hC hEE

theorem process_vertex_relative_ssa_nonneg (k : ℕ) :
    0 ≤ vertexOverlapGap
      (fun n => vertexBallRelativeEntropy (Fin r) m n energy he (C n))
      (fun n => edgeBallRelativeEntropy (Fin r) m n energy he (E n)) (m + 2) k := by
  apply vertexBall_relative_ssa_nonneg (Fin r) m k energy he (C (k + 1)) (E (k + 1)) (C k)
  · intro a
    rw [hC, jointVertexInnovationProcessLaw_local μ hμ k energy
      (ne_of_lt ((le_abs_self energy).trans_lt he)) hE, ← hEE]
  · rw [hC, jointVertexInnovationProcessLaw_core μ k energy
      (ne_of_lt ((le_abs_self energy).trans_lt he)) hE, ← hC]

theorem process_edge_relative_ssa_nonneg (k : ℕ) :
    0 ≤ edgeOverlapGap
      (fun n => vertexBallRelativeEntropy (Fin r) m n energy he (C n))
      (fun n => edgeBallRelativeEntropy (Fin r) m n energy he (E n)) k := by
  apply edgeBall_relative_ssa_nonneg (Fin r) m k energy he (E (k + 1)) (C k) (E k)
  · intro b
    rw [hEE, jointEdgeInnovationProcessLaw_local μ hμ k energy
      (ne_of_lt ((le_abs_self energy).trans_lt he)) hE, ← hC]
  · rw [hEE, jointEdgeInnovationProcessLaw_core μ k energy hE, ← hEE]

theorem process_relative_entropy_balance_antitone :
    Antitone (relativeBallBalance
      (fun n => vertexBallRelativeEntropy (Fin r) m n energy he (C n))
      (fun n => edgeBallRelativeEntropy (Fin r) m n energy he (E n)) (m + 2)) :=
  relativeBallBalance_antitone _ _ _ (by positivity)
    (process_vertex_relative_ssa_nonneg μ hμ energy he hE C E hC hEE)
    (process_edge_relative_ssa_nonneg μ hμ energy he hE C E hC hEE)

end

theorem process_relative_entropy_balance_nonneg {r m : ℕ} (hm : 0 < m)
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ChannelTreeInvariant μ) (hi : ∀ av, Integrable (fun x => x av ^ 2) μ)
    (energy : ℝ) (hbulk : |energy| < 2 * Real.sqrt (m + 1))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0)
    (hfinite : ∀ k, Lower.HasFiniteRecoloringEntropyLower (vertexSiteFirstProcessLaw μ k)
      (edgeSiteFirstProcessLaw μ k) (Lower.rootProcessWindow m μ) ((m + 2 : ℝ) / 2))
    (C : ∀ k, PositiveEntropyDensity (volume : Measure ((Fin r × VertexBallInnovation (m + 2) k) → ℝ)))
    (E : ∀ k, PositiveEntropyDensity (volume : Measure ((Fin r × EdgeBallInnovation (m + 2) k) → ℝ)))
    (hC : ∀ k, (C k).law = jointVertexInnovationProcessLaw μ k)
    (hEE : ∀ k, (E k).law = jointEdgeInnovationProcessLaw μ k) (k : ℕ) :
    0 ≤ relativeBallBalance
      (fun n => vertexBallRelativeEntropy (Fin r) m n energy (abs_energy_lt_degree_of_strict_bulk m energy hbulk) (C n))
      (fun n => edgeBallRelativeEntropy (Fin r) m n energy (abs_energy_lt_degree_of_strict_bulk m energy hbulk) (E n)) (m + 2) k := by
  let he := abs_energy_lt_degree_of_strict_bulk m energy hbulk
  let X := fun n => (C n |>.linearEquiv (coloredVertexInnovationToIntrinsic (Fin r) m n energy he)).entropy -
    (m + 2 : ℝ) / 2 * (E n |>.linearEquiv (coloredEdgeInnovationToIntrinsic (Fin r) m n energy he)).entropy
  let G := fun n => (jointVertexIntrinsicFlatReference (Fin r) m n energy he).entropy -
    (m + 2 : ℝ) / 2 * (jointEdgeIntrinsicFlatReference (Fin r) m n energy he).entropy
  have hX (n) : 0 ≤ X n := process_intrinsic_entropy_lower μ hi n energy he hE (hfinite n)
    (C n) (E n) (hC n) (hEE n)
  have hG : Tendsto G atTop (𝓝 0) := by
    simpa only [G, jointVertexIntrinsicFlatReference_entropy, jointEdgeIntrinsicFlatReference_entropy] using
      joint_gaussian_ball_reference_entropy_tendsto_zero r m hm energy hbulk
  have hb (n) : X n - G n = relativeBallBalance
      (fun n => vertexBallRelativeEntropy (Fin r) m n energy he (C n))
      (fun n => edgeBallRelativeEntropy (Fin r) m n energy he (E n)) (m + 2) n := by
    rw [relativeBallBalance, vertexBallRelativeEntropy_eq_intrinsic, edgeBallRelativeEntropy_eq_intrinsic]
    dsimp only [X, G]
    ring
  have hmono := process_relative_entropy_balance_antitone μ hμ energy he hE C E hC hEE
  have hmono' : Antitone (fun n => X n - G n) := by
    intro i j hij
    change X j - G j ≤ X i - G i
    rw [hb, hb]
    exact hmono hij
  have h := entropyBalance_lower_of_antitone_sub_reference X G hX hG hmono' k
  rw [hb] at h
  exact h

end GaussianWave.BS
