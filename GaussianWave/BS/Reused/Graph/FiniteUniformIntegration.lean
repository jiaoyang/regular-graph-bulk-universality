import GaussianWave.BS.Reused.Graph.UniformSwitching

/-! Generic finite-uniform integration, extracted from the sibling project's
`Graph/OrientedEdgeSampling.lean` to keep this counting closure independent of
spectral-data interfaces. The proof is copied with namespace adaptation. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph

theorem integral_finiteUniform {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    (∫ x, f x ∂finiteUniform α) = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  rw [finiteUniform, integral_smul_measure, integral_finset_sum_measure (fun _ _ => integrable_dirac)]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

end GaussianWave.BS.Reused.Graph
