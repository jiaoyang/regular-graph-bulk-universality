import GeneralizedBulk.Graph.CovarianceCentering
import BourgadeHuang.FiniteCountingConfiguration

/-!
# The actual finite graph scalar as an anchored counting state

The finite microscopic eigenvalues and normalized trace are constructed from
the given real eigensystem. Their identification with the repository's
counting Nevanlinna state is proved by the exact spectral expansion.
-/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def microscopicEigenvalue (n : ℕ) (ω : Ω) (E sigma : ℝ) (k : Fin (N n)) : ℝ :=
  (N n : ℝ) * sigma * (D.eigenvalue n ω k - E)

def microscopicScalar (n : ℕ) (ω : Ω) (E sigma a : ℝ) (hsigma : 0 < sigma)
    (w : GraphNonreal) : ℂ :=
  (D.scalarResolvent n ω (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 -
    (a : ℂ)) / (sigma : ℂ)

/-- Each microscopic coefficient has the exact scale sigma. This identity
also holds at zero denominators, using totalized field inversion. -/
theorem microscopic_coefficient_eq (n : ℕ) (ω : Ω) (E sigma : ℝ)
    (hsigma : 0 < sigma) (w : GraphNonreal) (k : Fin (N n)) :
    (N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) -
      (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1)⁻¹ =
      (sigma : ℂ) * ((D.microscopicEigenvalue n ω E sigma k : ℂ) - w.1)⁻¹ := by
  let c := microscopicStep (N n) sigma
  have hN : (N n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have hc : ((c : ℂ)⁻¹) = (N n : ℂ) * (sigma : ℂ) := by
    simp [c, microscopicStep]
  have heq : (D.eigenvalue n ω k : ℂ) -
      (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 =
      (c : ℂ) * ((D.microscopicEigenvalue n ω E sigma k : ℂ) - w.1) := by
    dsimp [microscopicParameter, microscopicEigenvalue, c, microscopicStep]
    push_cast
    have hsig : (sigma : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hsigma)
    field_simp
    ring
  rw [heq, mul_inv_rev, hc]
  field_simp

/-- The normalized finite trace is literally the finite microscopic
Stieltjes transform with its real bulk centering. -/
theorem microscopicScalar_eq_finite (n : ℕ) (ω : Ω) (E sigma a : ℝ)
    (hsigma : 0 < sigma) (w : GraphNonreal) :
    D.microscopicScalar n ω E sigma a hsigma w =
      microscopicResolvent (D.microscopicEigenvalue n ω E sigma) (a / sigma) w.1 := by
  rw [microscopicScalar, D.scalarResolvent_eq_spectral n ω _
    (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).2, Finset.mul_sum]
  simp_rw [D.microscopic_coefficient_eq n ω E sigma hsigma w]
  rw [← Finset.mul_sum]
  unfold microscopicResolvent
  push_cast
  have hsig : (sigma : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hsigma)
  field_simp
  ring

/-- The finite graph particle configuration retains multiplicities. -/
def microscopicCountingState (n : ℕ) (ω : Ω) (E sigma a : ℝ) : AnchoredCountingState :=
  ⟨(finiteCountingConfiguration (D.microscopicEigenvalue n ω E sigma),
      microscopicResolvent (D.microscopicEigenvalue n ω E sigma) (a / sigma) Complex.I),
    validAnchoredCountingState_finite _ _ _ (finiteCountingConfiguration_measure _)⟩

/-- The anchored state reconstructs the actual graph scalar at every
nonreal microscopic point, without a separate analytic limit assumption. -/
theorem microscopicCountingState_scalar (n : ℕ) (ω : Ω) (E sigma a : ℝ)
    (hsigma : 0 < sigma) (w : GraphNonreal) :
    anchoredNevanlinna (D.microscopicCountingState n ω E sigma a) w.1 =
      D.microscopicScalar n ω E sigma a hsigma w := by
  rw [D.microscopicScalar_eq_finite n ω E sigma a hsigma w]
  exact anchoredNevanlinna_eq_finite _ _ _ (finiteCountingConfiguration_measure _) w.2

/-- The actual finite graph state is measurable in the graph sample. -/
theorem measurable_microscopicCountingState (n : ℕ) (E sigma a : ℝ) :
    Measurable (fun ω => D.microscopicCountingState n ω E sigma a) := by
  have hx : Measurable (fun ω => D.microscopicEigenvalue n ω E sigma) := by
    apply measurable_pi_lambda
    intro k
    exact ((D.measurable_eigenvalue n k).sub_const E).const_mul _
  apply Measurable.subtype_mk
  apply ((measurable_finiteCountingConfiguration (N n)).comp hx).prodMk
  unfold microscopicResolvent
  apply Measurable.sub_const
  apply Finset.measurable_sum
  intro k hk
  exact (((measurable_pi_apply k).comp hx).complex_ofReal.sub_const Complex.I).inv

end GeneralizedBulk.External.RegularSpectralData
