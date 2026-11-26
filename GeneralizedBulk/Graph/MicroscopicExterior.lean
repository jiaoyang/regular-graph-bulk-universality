import GeneralizedBulk.Graph.ExteriorLimit
import GeneralizedBulk.Graph.SwitchingProbability

/-!
# Literal microscopic exterior fields of the uniform regular graph model

The microscopic scalar and matrix are obtained by the actual spectral map
`z = E + w/(N sigma)`. The scalar exterior is scaled by `(N sigma)⁻¹` and
centered by `a/sigma`; the matrix exterior is reparameterized. This operation
commutes with endpoint conjugation, so the proved finite switch law passes to
all finite-dimensional weak limits with an explicit vanishing error.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Graph
open Exterior

def microscopicStep (N : ℕ) (sigma : ℝ) : ℝ := ((N : ℝ) * sigma)⁻¹

theorem microscopicStep_pos (N : ℕ) (hN : 0 < N) (sigma : ℝ) (hsigma : 0 < sigma) :
    0 < microscopicStep N sigma := inv_pos.mpr (mul_pos (Nat.cast_pos.mpr hN) hsigma)

def microscopicParameter (N : ℕ) (hN : 0 < N) (E sigma : ℝ) (hsigma : 0 < sigma)
    (w : GraphNonreal) : GraphNonreal :=
  ⟨(E : ℂ) + (microscopicStep N sigma : ℂ) * w.1, by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      zero_add, mul_zero, zero_mul, add_zero]
    exact mul_ne_zero (ne_of_gt (microscopicStep_pos N hN sigma hsigma)) w.2⟩

/-- The finite exterior uses exactly this scalar rescaling and centering. -/
def microscopicExteriorTransform (N : ℕ) (hN : 0 < N) (E sigma a : ℝ) (hsigma : 0 < sigma)
    (x : GraphExteriorState) : GraphExteriorState :=
  (fun w => (microscopicStep N sigma : ℂ) * x.1 (microscopicParameter N hN E sigma hsigma w) -
      ((a / sigma : ℝ) : ℂ),
    fun w => x.2 (microscopicParameter N hN E sigma hsigma w))

theorem measurable_microscopicExteriorTransform (N : ℕ) (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) :
    Measurable (microscopicExteriorTransform N hN E sigma a hsigma) := by
  have ht : Measurable (fun x : GraphExteriorState => fun w : GraphNonreal =>
      (microscopicStep N sigma : ℂ) * x.1 (microscopicParameter N hN E sigma hsigma w) -
        ((a / sigma : ℝ) : ℂ)) := by
    apply measurable_pi_lambda
    intro w
    have hs : Measurable (fun x : GraphExteriorState => x.1 (microscopicParameter N hN E sigma hsigma w)) :=
      (measurable_pi_apply _).comp measurable_fst
    exact (hs.const_mul (microscopicStep N sigma : ℂ)).sub_const _
  have hm : Measurable (fun x : GraphExteriorState => fun w : GraphNonreal =>
      x.2 (microscopicParameter N hN E sigma hsigma w)) :=
    measurable_pi_lambda _ (fun w => (measurable_pi_apply _).comp measurable_snd)
  exact ht.prodMk hm

/-- Spectral reparameterization and the literal scalar normalization commute
with conjugation of the joint exterior field. -/
theorem microscopicExteriorTransform_action (N : ℕ) (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (Q : Mat) (x : GraphExteriorState) :
    microscopicExteriorTransform N hN E sigma a hsigma (action Q x) =
      action Q (microscopicExteriorTransform N hN E sigma a hsigma x) := rfl

/-- The transform is precisely the exterior scalar of `s_N=(m_N-a)/sigma`
and the boundary derivative in the microscopic variable. -/
theorem microscopicExterior_scalar_formula
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (e : Fin 4 → V)
    (N : ℕ) (hN : 0 < N) (E sigma a : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) :
    (microscopicExteriorTransform N hN E sigma a hsigma (graphExterior G e)).1 w =
      rawExteriorScalar
        (((N : ℂ)⁻¹ * Matrix.trace (graphResolvent G (microscopicParameter N hN E sigma hsigma w).1) -
          (a : ℂ)) / (sigma : ℂ))
        (graphBoundary G e (microscopicParameter N hN E sigma hsigma w).1)
        ((microscopicStep N sigma : ℂ) •
          graphBoundaryDerivative G e (microscopicParameter N hN E sigma hsigma w).1) := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hsc : (sigma : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hsigma)
  simp only [microscopicExteriorTransform, graphExterior, graphExteriorScalar, rawExteriorScalar,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, microscopicStep,
    Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast]
  field_simp
  ring

def microscopicEdgePairExterior {N d : ℕ} (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (s : EdgePairState N d) : GraphExteriorState :=
  microscopicExteriorTransform N hN E sigma a hsigma (edgePairExterior s)

/-- Exact accepted-switch equivariance survives the literal microscopic
normalization, with the scalar and all matrix values kept jointly. -/
theorem microscopicEdgePairExterior_proposalSwitch {N d : ℕ} (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (s : EdgePairState N d) (hs : Accepted s) :
    microscopicEdgePairExterior hN E sigma a hsigma (proposalSwitch s) =
      action (GeneralizedSwitching.endpointPermutation : Mat)
        (microscopicEdgePairExterior hN E sigma a hsigma s) := by
  unfold microscopicEdgePairExterior
  rw [edgePairExterior_proposalSwitch s hs, microscopicExteriorTransform_action]

/-- Exact finite microscopic bounded-test discrepancy. -/
theorem microscopicEdgePairExterior_approximate_switch_invariance
    {N d : ℕ} [Nonempty (EdgePairState N d)] (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma)
    (F : GraphExteriorState → ℝ) (B : ℝ) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∫ s, F (action (GeneralizedSwitching.endpointPermutation : Mat)
        (microscopicEdgePairExterior hN E sigma a hsigma s)) ∂edgePairLaw N d) -
      (∫ s, F (microscopicEdgePairExterior hN E sigma a hsigma s) ∂edgePairLaw N d)‖ ≤
      2 * B * (edgePairLaw N d {s | ¬Accepted s}).toReal := by
  have h := edgePairExterior_approximate_switch_invariance (N := N) (d := d)
    (fun x => F (microscopicExteriorTransform N hN E sigma a hsigma x)) B (fun x => hF _)
  simpa only [microscopicExteriorTransform_action, microscopicEdgePairExterior] using h

/-- The rejection probability of the actual uniform graph/proposal model
vanishes whenever its number of vertices tends to infinity. -/
theorem edgePairLaw_rejection_tendsto_zero
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hNlimit : Tendsto N atTop atTop)
    (d : ℕ) (hd : 0 < d) [∀ n, Nonempty (RegularGraph (N n) d)] :
    Tendsto (fun n => (edgePairLaw (N n) d {s | ¬Accepted s}).toReal) atTop (𝓝 0) := by
  have hreal : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNlimit
  have hu : Tendsto (fun n => (4 + 2 * (d : ℝ)) / (N n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hreal))
  exact squeeze_zero (fun n => ENNReal.toReal_nonneg)
    (fun n => edgePairLaw_rejection_probability_bound (hN n) hd) hu

/-- Any finite-dimensional weak limit of the actual microscopic uniform-graph
exteriors has the full joint endpoint-switch symmetry. The switch error and
its convergence to zero are both proved from the concrete finite graph model. -/
theorem microscopicExterior_limit_switch_invariant
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hNlimit : Tendsto N atTop atTop)
    (d : ℕ) (hd : 0 < d) [∀ n, Nonempty (RegularGraph (N n) d)]
    (E sigma a : ℝ) (hsigma : 0 < sigma)
    (nu : Measure GraphExteriorState) [IsFiniteMeasure nu]
    (hweak : ∀ s : Finset GraphNonreal, External.WeakLawConverges
      (fun n => Measure.map (exteriorProjection s)
        (Measure.map (microscopicEdgePairExterior (d := d) (hN n) E sigma a hsigma)
          (edgePairLaw (N n) d)))
      (Measure.map (exteriorProjection s) nu)) :
    Measure.map (action (GeneralizedSwitching.endpointPermutation : Mat)) nu = nu := by
  letI : ∀ n, Nonempty (EdgePairState (N n) d) := fun n => edgePairState_nonempty (hN n) hd
  let fN := fun n => microscopicEdgePairExterior (d := d) (hN n) E sigma a hsigma
  let mu := fun n => Measure.map (fN n) (edgePairLaw (N n) d)
  let epsilon := fun n => 2 * (edgePairLaw (N n) d {s | ¬Accepted s}).toReal
  have hepsilon : Tendsto epsilon atTop (𝓝 0) := by
    simpa only [epsilon, mul_zero] using tendsto_const_nhds.mul
      (edgePairLaw_rejection_tendsto_zero N hN hNlimit d hd)
  apply exterior_law_symmetry_of_finite_weak_limits mu nu
    GeneralizedSwitching.endpointPermutation epsilon hepsilon hweak
  intro s n f
  have hfN : Measurable (fN n) := measurable_of_finite _
  have htest : Measurable (fun x : GraphExteriorState => f (exteriorProjection s x)) :=
    f.continuous.measurable.comp (measurable_exteriorProjection s)
  have htestQ : Measurable (fun x : GraphExteriorState =>
      f (exteriorProjection s (action (GeneralizedSwitching.endpointPermutation : Mat) x))) :=
    htest.comp (measurable_action _)
  change ‖(∫ x, f (exteriorProjection s (action (GeneralizedSwitching.endpointPermutation : Mat) x))
      ∂Measure.map (fN n) (edgePairLaw (N n) d)) -
    (∫ x, f (exteriorProjection s x) ∂Measure.map (fN n) (edgePairLaw (N n) d))‖ ≤
      ‖f‖ * epsilon n
  rw [integral_map hfN.aemeasurable htestQ.aestronglyMeasurable,
    integral_map hfN.aemeasurable htest.aestronglyMeasurable]
  have hb := microscopicEdgePairExterior_approximate_switch_invariance
    (N := N n) (d := d) (hN n) E sigma a hsigma
    (fun x => f (exteriorProjection s x)) ‖f‖ (fun x => f.norm_coe_le_norm _)
  convert hb using 1 <;> dsimp only [epsilon] <;> ring

end GeneralizedBulk.Graph
