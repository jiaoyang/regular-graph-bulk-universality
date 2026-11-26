import BourgadeHuang.EdgeCMS.Basic
import BourgadeHuang.CMS.GeneralGauge

/-! Exact analytic exponential conjugation for the edge CMS operator. -/
noncomputable section
open scoped BigOperators Topology

namespace BourgadeHuang.EdgeCMS
open CMS

def conjugatedEdgeOperator {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (L : Point d → ℂ) (i : Fin d) (W : Point d → ℂ) (z : Point d) : ℂ :=
  secondPartial i W z + 2 * coordDeriv i L z * coordDeriv i W z +
    (secondPartial i L z + (coordDeriv i L z) ^ 2 - c i ^ 2 * z i) * W z +
    (2 / β) * ∑ j ∈ Finset.univ.erase i,
      (c i * c j * coordDeriv i W z - c i ^ 2 * coordDeriv j W z +
        (c i * c j * coordDeriv i L z - c i ^ 2 * coordDeriv j L z) * W z) /
          (z i - z j)

theorem conjugatedEdgeOperator_eq_bulk_sub {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (L : Point d → ℂ) (i : Fin d) (W : Point d → ℂ) (z : Point d) :
    conjugatedEdgeOperator β c L i W z =
      conjugatedDeformedOperator β c L i W z - c i ^ 2 * (z i + 1) * W z := by
  unfold conjugatedEdgeOperator conjugatedDeformedOperator
  ring

theorem edgeOperator_exp_mul {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    {L W : Point d → ℂ} {z : Point d} (hL : AnalyticAt ℂ L z)
    (hW : AnalyticAt ℂ W z) (i : Fin d) :
    edgeOperator β c i (fun w => Complex.exp (L w) * W w) z =
      Complex.exp (L z) * conjugatedEdgeOperator β c L i W z := by
  rw [edgeOperator_eq_bulk_sub, deformedOperator_exp_mul β c hL hW,
    conjugatedEdgeOperator_eq_bulk_sub]
  ring

theorem edgeOperator_exp_mul_eq_zero_iff {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    {L W : Point d → ℂ} {z : Point d} (hL : AnalyticAt ℂ L z)
    (hW : AnalyticAt ℂ W z) (i : Fin d) :
    edgeOperator β c i (fun w => Complex.exp (L w) * W w) z = 0 ↔
      conjugatedEdgeOperator β c L i W z = 0 := by
  rw [edgeOperator_exp_mul β c hL hW, mul_eq_zero]
  simp [Complex.exp_ne_zero]

end BourgadeHuang.EdgeCMS
