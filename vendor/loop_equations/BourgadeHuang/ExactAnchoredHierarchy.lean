import BourgadeHuang.NevanlinnaGrowth
import BourgadeHuang.AnchoredStateBorel

/-! Exact reconstructed loop identities for anchored counting-state laws. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- Every reconstructed loop expectation exists and vanishes. -/
def ExactAnchoredHierarchy (ν : Measure AnchoredCountingState) (β : Beta) : Prop :=
  ∀ n : ℕ, ∀ w : ℂ, w.im ≠ 0 → ∀ aux : Fin n → ℂ, (∀ a, (aux a).im ≠ 0) →
    Integrable (fun s => anchoredLoopIntegrand β s w aux) ν ∧
      (∫ s, anchoredLoopIntegrand β s w aux ∂ν) = 0

end BourgadeHuang
