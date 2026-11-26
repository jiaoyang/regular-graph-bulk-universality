import GeneralizedBulk.Exterior.Flow
import GeneralizedBulk.Exterior.Reconstruction
import GeneralizedBulk.Analysis.StationaryExpectation
import BourgadeHuang.Particles

/-!
# Unconditional stationary polynomial responses

The polynomial expected response is proved from the constructed exterior path,
its actual derivative, and the switch/ordinary-rotation symmetries. It is not
an assumption. Integrability at angle zero is the moment input needed by FTC.
-/
noncomputable section
open MeasureTheory ProbabilityTheory BourgadeHuang
open scoped BigOperators ComplexOrder
namespace GeneralizedBulk.Exterior

@[simp] theorem action_one {A I : Type*} (state : A × (I → Mat)) : action (1 : Mat) state = state := by
  apply Prod.ext
  · rfl
  · funext w
    simp [action]

/-- Simultaneous rotation as a jointly measurable time/sample map. -/
def jointAction {I : Type*} (z : ℝ × JetState I) : JetState I :=
  action (rotation z.1) z.2

theorem measurable_jointAction {I : Type*} : Measurable (jointAction (I := I)) := by
  have hQ : Measurable (fun z : ℝ × JetState I => rotation (z.1 : ℂ)) :=
    (continuous_rotation.comp Complex.continuous_ofReal).measurable.comp measurable_fst
  have hQT : Measurable (fun z : ℝ × JetState I => (rotation (z.1 : ℂ)).transpose) :=
    continuous_id.matrix_transpose.measurable.comp hQ
  refine (measurable_fst.comp measurable_snd).prodMk (measurable_pi_lambda _ fun w => ?_)
  have hK : Measurable (fun z : ℝ × JetState I => z.2.2 w) :=
    (measurable_pi_apply w).comp (measurable_snd.comp measurable_snd)
  exact (hQ.mul hK).mul hQT

@[simp] theorem reconstructedMatrix_action {I : Type*} (state : JetState I) (w : I) (t : ℝ) :
    reconstructedMatrix (action (rotation t) state) w = resolventPath (state.2 (w, false)) t := by
  simp only [reconstructedMatrix, action, resolventPath, exteriorPath_eq_transpose]

@[simp] theorem reconstructedScalar_action {I : Type*} (state : JetState I) (w : I) (t : ℝ) :
    reconstructedScalar (action (rotation t) state) w =
      scalarPath (state.1 w) (state.2 (w, false)) (state.2 (w, true)) t := by
  simp only [reconstructedScalar, action, reconstructedMatrix, scalarPath, resolventPath,
    exteriorPath_eq_transpose]

@[simp] theorem reconstructedDerivative_action {I : Type*} (state : JetState I) (w : I) (t : ℝ) :
    reconstructedDerivative (action (rotation t) state) w =
      resolventPath (state.2 (w, false)) t * exteriorPath (state.2 (w, true)) t *
        resolventPath (state.2 (w, false)) t := by
  rw [reconstructedDerivative, reconstructedMatrix_action]
  rw [exteriorPath_eq_transpose]
  rfl

def signObservable {I : Type*} (state : JetState I) (w : I) : ℂ :=
  Matrix.trace (signMatrix * reconstructedMatrix state w)

def signResponse {I : Type*} (state : JetState I) (w : I) : ℂ :=
  Matrix.trace (signMatrix * matrixResponse (reconstructedMatrix state w))

def scalarResponse {I : Type*} (state : JetState I) (w : I) : ℂ :=
  2 * Matrix.trace (signMatrix * reconstructedDerivative state w)

def polynomialObservable {I : Type*} {n : ℕ} (w : I) (aux : Fin n → I) (state : JetState I) : ℂ :=
  signObservable state w * ∏ j, reconstructedScalar state (aux j)

def polynomialResponse {I : Type*} {n : ℕ} (w : I) (aux : Fin n → I) (state : JetState I) : ℂ :=
  signResponse state w * ∏ j, reconstructedScalar state (aux j) +
    ∑ j, (signObservable state w * scalarResponse state (aux j)) *
      excludedProduct (fun a => reconstructedScalar state (aux a)) j

private theorem measurable_matrixResponse : Measurable (matrixResponse (R := ℂ)) := by
  exact ((measurable_id.const_mul rotationGenerator).sub
    (measurable_id.mul_const rotationGenerator)).add
      (((measurable_id.mul_const signMatrix).mul measurable_id).const_smul (2 : ℂ))

theorem measurable_signObservable {I : Type*} (w : I) : Measurable (fun state : JetState I => signObservable state w) :=
  continuous_id.matrix_trace.measurable.comp ((measurable_reconstructedMatrix w).const_mul signMatrix)

theorem measurable_signResponse {I : Type*} (w : I) : Measurable (fun state : JetState I => signResponse state w) :=
  continuous_id.matrix_trace.measurable.comp
    ((measurable_matrixResponse.comp (measurable_reconstructedMatrix w)).const_mul signMatrix)

theorem measurable_scalarResponse {I : Type*} (w : I) : Measurable (fun state : JetState I => scalarResponse state w) :=
  (continuous_id.matrix_trace.measurable.comp
    ((measurable_reconstructedDerivative w).const_mul signMatrix)).const_mul 2

theorem measurable_polynomialObservable {I : Type*} {n : ℕ} (w : I) (aux : Fin n → I) :
    Measurable (polynomialObservable w aux) :=
  (measurable_signObservable w).mul
    (Finset.measurable_prod _ fun j _ => measurable_reconstructedScalar (aux j))

theorem measurable_polynomialResponse {I : Type*} {n : ℕ} (w : I) (aux : Fin n → I) :
    Measurable (polynomialResponse w aux) := by
  refine ((measurable_signResponse w).mul
    (Finset.measurable_prod _ fun j _ => measurable_reconstructedScalar (aux j))).add ?_
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_signObservable w).mul (measurable_scalarResponse (aux j))).mul
    (Finset.measurable_prod _ fun a _ => measurable_reconstructedScalar (aux a))

/-- Actual differentiation along the constructed exterior path. -/
theorem hasDerivAt_polynomialObservable {I : Type*} {n : ℕ}
    (state : JetState I) (w : I) (aux : Fin n → I)
    (hpos : ∀ u : I, ImaginarySignDefinite (state.2 (u, false))) (t : ℝ) :
    HasDerivAt (fun a : ℝ => polynomialObservable w aux (action (rotation a) state))
      (polynomialResponse w aux (action (rotation t) state)) t := by
  have hh : HasDerivAt (fun a : ℝ => signObservable (action (rotation a) state) w)
      (signResponse (action (rotation t) state) w) t := by
    simpa only [signObservable, signResponse, reconstructedMatrix_action] using
      hasDerivAt_signTracePath (state.2 (w, false)) (hpos w) t
  have hs (j : Fin n) :
      HasDerivAt (fun a : ℝ => reconstructedScalar (action (rotation a) state) (aux j))
        (scalarResponse (action (rotation t) state) (aux j)) t := by
    simpa only [reconstructedScalar_action, scalarResponse, reconstructedDerivative_action,
      Matrix.mul_assoc] using hasDerivAt_scalarPath (state.1 (aux j))
      (state.2 (aux j, false)) (state.2 (aux j, true)) (hpos (aux j)) t
  have hp := HasDerivAt.finset_prod (u := Finset.univ) (fun j _ => hs j)
  convert hh.mul hp using 1
  simp only [polynomialResponse, excludedProduct, smul_eq_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The full polynomial response has zero expectation, derived using FTC and
Fubini from the explicit law symmetries and one-angle moment integrability. -/
theorem integral_polynomialResponse_eq_zero
    {I : Type*} {n : ℕ} (μ : Measure (JetState I)) [SFinite μ]
    (w : I) (aux : Fin n → I)
    (hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation) μ = μ)
    (hordinary : ∀ t : ℝ, Measure.map (action (ordinaryRotation t)) μ = μ)
    (hpos : ∀ᵐ state ∂μ, ∀ u : I, ImaginarySignDefinite (state.2 (u, false)))
    (hF : Integrable (polynomialObservable w aux) μ)
    (hG : Integrable (polynomialResponse w aux) μ) :
    (∫ state, polynomialResponse w aux state ∂μ) = 0 := by
  let F : ℝ → JetState I → ℂ := fun t state => polynomialObservable w aux (action (rotation t) state)
  let G : ℝ → JetState I → ℂ := fun t state => polynomialResponse w aux (action (rotation t) state)
  have hFzero : F 0 = polynomialObservable w aux := by funext state; simp [F]
  have hGzero : G 0 = polynomialResponse w aux := by funext state; simp [G]
  have hjoint : Measurable (fun z : ℝ × JetState I => G z.1 z.2) :=
    (measurable_polynomialResponse w aux).comp measurable_jointAction
  have hderiv : ∀ᵐ state ∂μ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun a => F a state) (G t state) t := by
    filter_upwards [hpos] with state hp
    intro t _
    exact hasDerivAt_polynomialObservable state w aux hp t
  have hFs : IdentDistrib (F 1) (F 0) μ μ := by
    rw [hFzero]
    exact observable_identDistrib μ 1 hswitch (hordinary 1) _ (measurable_polynomialObservable w aux)
  have hGs : ∀ t ∈ Set.Ioc (0 : ℝ) 1, IdentDistrib (G t) (G 0) μ μ := by
    intro t _
    rw [hGzero]
    exact observable_identDistrib μ t hswitch (hordinary t) _ (measurable_polynomialResponse w aux)
  have hz := GeneralizedBulk.Analysis.integral_response_eq_zero μ F G
    (by rw [hFzero]; exact hF) (by rw [hGzero]; exact hG)
    hjoint.aestronglyMeasurable hderiv hFs hGs
  simpa only [hGzero] using hz

set_option maxHeartbeats 1000000 in
/-- Source-space version of stationary differentiation. Positivity is checked
on the actual sample, so no uncountable positivity predicate in the jet-space
pushforward needs to be declared measurable. -/
theorem integral_polynomialResponse_pullback_eq_zero
    {Ω I : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [SFinite P] (jet : Ω → JetState I) (hjet : Measurable jet)
    (w : I) (aux : Fin n → I)
    (hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation) (Measure.map jet P) =
      Measure.map jet P)
    (hordinary : ∀ t : ℝ, Measure.map (action (ordinaryRotation t)) (Measure.map jet P) =
      Measure.map jet P)
    (hpos : ∀ᵐ ω ∂P, ∀ u : I, ImaginarySignDefinite ((jet ω).2 (u, false)))
    (hF : Integrable (fun ω => polynomialObservable w aux (jet ω)) P)
    (hG : Integrable (fun ω => polynomialResponse w aux (jet ω)) P) :
    (∫ ω, polynomialResponse w aux (jet ω) ∂P) = 0 := by
  let F : ℝ → Ω → ℂ := fun t ω => polynomialObservable w aux (action (rotation t) (jet ω))
  let G : ℝ → Ω → ℂ := fun t ω => polynomialResponse w aux (action (rotation t) (jet ω))
  have hFzero : F 0 = fun ω => polynomialObservable w aux (jet ω) := by funext ω; simp [F]
  have hGzero : G 0 = fun ω => polynomialResponse w aux (jet ω) := by funext ω; simp [G]
  have hpair : Measurable (fun z : ℝ × Ω => (z.1, jet z.2)) :=
    measurable_fst.prodMk (hjet.comp measurable_snd)
  have haction : Measurable (fun z : ℝ × Ω => action (rotation z.1) (jet z.2)) :=
    (measurable_jointAction (I := I)).comp hpair
  have hjoint : Measurable (fun z : ℝ × Ω => G z.1 z.2) :=
    (measurable_polynomialResponse w aux).comp haction
  have hderiv : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun a => F a ω) (G t ω) t := by
    filter_upwards [hpos] with ω hp
    intro t _
    exact hasDerivAt_polynomialObservable (jet ω) w aux hp t
  have hFs : IdentDistrib (F 1) (F 0) P P := by
    rw [hFzero]
    exact observable_pullback_identDistrib P jet hjet 1 hswitch (hordinary 1) _
      (measurable_polynomialObservable w aux)
  have hGs : ∀ t ∈ Set.Ioc (0 : ℝ) 1, IdentDistrib (G t) (G 0) P P := by
    intro t _
    rw [hGzero]
    exact observable_pullback_identDistrib P jet hjet t hswitch (hordinary t) _
      (measurable_polynomialResponse w aux)
  have hz := GeneralizedBulk.Analysis.integral_response_eq_zero P F G
    (by rw [hFzero]; exact hF) (by rw [hGzero]; exact hG)
    hjoint.aestronglyMeasurable hderiv hFs hGs
  simpa only [hGzero] using hz

end GeneralizedBulk.Exterior
