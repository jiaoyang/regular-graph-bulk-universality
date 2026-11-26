import GeneralizedBulk.Graph.OuterAveraged

/-! The actual microscopic exterior reparameterization removes the centered outer tail. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace GeneralizedBulk.Graph

/-- The literal microscopic spectral point converges to the real bulk center. -/
theorem microscopicParameter_tendsto_center
    (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (E sigma : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) :
    Tendsto (fun n => (microscopicParameter (N n) (hNpos n) E sigma hsigma w).val)
      atTop (𝓝 (E : ℂ)) := by
  have hReal : Tendsto (fun n => microscopicStep (N n) sigma) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)).mul_const sigma⁻¹
    simpa only [microscopicStep, mul_inv_rev, mul_comm, Function.comp_def, zero_mul, mul_zero] using h
  have hComplex : Tendsto (fun n => (microscopicStep (N n) sigma : ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hReal
  have h : Tendsto (fun n => (E : ℂ) + (microscopicStep (N n) sigma : ℂ) * w.val) atTop
      (𝓝 ((E : ℂ) + 0 * w.val)) := tendsto_const_nhds.add (hComplex.mul_const w.val)
  simpa only [microscopicParameter, zero_mul, add_zero] using h

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

/-- Centered outer marks vanish in full graph/proposal second mean under
the actual microscopic scaling, with only HY's finite geometry external. -/
theorem integral_microscopic_outerVariance_tendsto_zero
    {P : Measure Ω} [IsProbabilityMeasure P] (H : HYGeometryInput D P) (hd : 0 < d)
    (E gap sigma : ℝ) (hgap : 0 < gap) (hsigma : 0 < sigma) (w : GraphNonreal) (i j : Fin 4) :
    Tendsto (fun n => ∫ ω, D.outerProposalVariance n ω E gap
      (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).val i j ∂P) atTop (𝓝 0) :=
  D.integral_outerProposalVariance_tendsto_zero H hd E gap hgap _
    (microscopicParameter_tendsto_center N D.size_pos D.size_tendsto E sigma hsigma w) i j

end GeneralizedBulk.External.RegularSpectralData
