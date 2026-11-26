import GeneralizedBulk.Analysis.FiniteDifferenceJets
import GeneralizedBulk.Graph.RawPairCompactness
import GeneralizedBulk.Exterior.RawCoordinates

/-! The finite raw value/derivative coordinate transform to the joint
exterior scalar and self-energy is measurable, and continuous at actual
invertible raw matrices. -/
noncomputable section
open MeasureTheory
open scoped Topology
namespace GeneralizedBulk.Exterior
open Graph Analysis
variable {I : Type*} [Fintype I]

abbrev FiniteRawJet (I : Type*) := (I × Bool × RawComplexCoordinate) → ℂ

def finiteRawJetMatrix (v : FiniteRawJet I) (i : I) (b : Bool) : Mat :=
  fun a c => v (i,b,Sum.inr (a,c))

def finiteJetExterior (v : FiniteRawJet I) : I → RawValue :=
  fun i => (rawExteriorScalar (v (i,false,Sum.inl ()))
    (finiteRawJetMatrix v i false) (finiteRawJetMatrix v i true),
    rawExterior (finiteRawJetMatrix v i false))

theorem continuous_finiteRawJetMatrix (i : I) (b : Bool) :
    Continuous (fun v : FiniteRawJet I => finiteRawJetMatrix v i b) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro c
  exact continuous_apply _

theorem measurable_finiteJetExterior : Measurable (finiteJetExterior (I := I)) := by
  apply measurable_pi_lambda
  intro i
  have hM := (continuous_finiteRawJetMatrix (I := I) i false).measurable
  have hL := (continuous_finiteRawJetMatrix (I := I) i true).measurable
  have hi := measurable_matrix_inverse.comp hM
  apply Measurable.prodMk
  · exact (measurable_pi_apply (i,false,Sum.inl ())).sub
      (continuous_id.matrix_trace.measurable.comp (hi.mul hL))
  · exact measurable_const.sub hi

theorem continuousAt_finiteJetExterior (v : FiniteRawJet I)
    (hu : ∀ i,IsUnit (finiteRawJetMatrix v i false)) : ContinuousAt finiteJetExterior v := by
  apply continuousAt_pi.mpr
  intro i
  have hM := (continuous_finiteRawJetMatrix (I := I) i false).continuousAt (x := v)
  have hL := (continuous_finiteRawJetMatrix (I := I) i true).continuousAt (x := v)
  have hd : (finiteRawJetMatrix v i false).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (hu i))
  have hinv : ContinuousAt (fun A : Mat => A⁻¹) (finiteRawJetMatrix v i false) :=
    continuousAt_matrix_inv _ (by
      have he : (Ring.inverse : ℂ → ℂ) = (fun z : ℂ => z⁻¹) := by
        funext z
        exact Ring.inverse_eq_inv z
      rw [he]
      exact continuousAt_inv₀ hd)
  have hi := hinv.comp (x := v) hM
  apply ContinuousAt.prodMk
  · exact (continuous_apply (i,false,Sum.inl ())).continuousAt.sub
      (continuous_id.matrix_trace.continuousAt.comp (hi.mul hL))
  · exact continuousAt_const.sub hi

end GeneralizedBulk.Exterior
