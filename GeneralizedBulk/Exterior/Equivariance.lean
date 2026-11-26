import GeneralizedBulk.Exterior.RawStationarity

/-! # Equivariance of the actual raw-to-exterior coordinate transformation -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Exterior

/-- Orthogonal conjugation respects products, with the middle inverses
cancelled in their correct noncommutative order. -/
theorem conjugate_mul (Q A B : Mat) (hQ : Q * Q.transpose = 1) :
    (Q * A * Q.transpose) * (Q * B * Q.transpose) = Q * (A * B) * Q.transpose := by
  have hQt : Q.transpose * Q = 1 := Matrix.mul_eq_one_comm.mpr hQ
  calc
    _ = Q * (A * (Q.transpose * Q) * B) * Q.transpose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hQt]; simp only [mul_one, Matrix.mul_assoc]

/-- Totalized inverse is equivariant as well; positivity later ensures it is
an ordinary inverse on the marked-field support. -/
theorem inverse_conjugate (Q A : Mat) (hQ : Q * Q.transpose = 1) :
    (Q * A * Q.transpose)⁻¹ = Q * A⁻¹ * Q.transpose := by
  have hi : Q⁻¹ = Q.transpose := Matrix.inv_eq_right_inv hQ
  simp only [Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, hi,
    Matrix.transpose_transpose, Matrix.mul_assoc]

theorem trace_conjugate (Q A : Mat) (hQ : Q * Q.transpose = 1) :
    Matrix.trace (Q * A * Q.transpose) = Matrix.trace A := by
  have hQt : Q.transpose * Q = 1 := Matrix.mul_eq_one_comm.mpr hQ
  rw [Matrix.trace_mul_cycle, hQt, one_mul]

theorem rawExterior_conjugate (Q M : Mat) (hQ : Q * Q.transpose = 1)
    (hJ : Q * GeneralizedSwitching.edgeMatrix = GeneralizedSwitching.edgeMatrix * Q) :
    rawExterior (Q * M * Q.transpose) = Q * rawExterior M * Q.transpose := by
  have hfix : Q * GeneralizedSwitching.edgeMatrix * Q.transpose =
      (GeneralizedSwitching.edgeMatrix : Mat) := by
    rw [hJ, Matrix.mul_assoc, hQ, mul_one]
  simp only [rawExterior, inverse_conjugate Q M hQ, Matrix.mul_sub, Matrix.sub_mul, hfix]

theorem rawExteriorDerivative_conjugate (Q M L : Mat) (hQ : Q * Q.transpose = 1) :
    rawExteriorDerivative (Q * M * Q.transpose) (Q * L * Q.transpose) =
      Q * rawExteriorDerivative M L * Q.transpose := by
  simp only [rawExteriorDerivative, inverse_conjugate Q M hQ]
  rw [conjugate_mul Q M⁻¹ L hQ, conjugate_mul Q (M⁻¹ * L) M⁻¹ hQ]

theorem rawExteriorScalar_conjugate (s : ℂ) (Q M L : Mat) (hQ : Q * Q.transpose = 1) :
    rawExteriorScalar s (Q * M * Q.transpose) (Q * L * Q.transpose) = rawExteriorScalar s M L := by
  simp only [rawExteriorScalar, inverse_conjugate Q M hQ]
  rw [conjugate_mul Q M⁻¹ L hQ, trace_conjugate Q (M⁻¹ * L) hQ]

/-- The full exterior jet transforms by the same ordinary rotation. -/
theorem jetOfRaw_conjugate {I : Type*} (s : I → ℂ) (M L : I → Mat)
    (Q : Mat) (hQ : Q * Q.transpose = 1)
    (hJ : Q * GeneralizedSwitching.edgeMatrix = GeneralizedSwitching.edgeMatrix * Q) :
    jetOfRaw s (fun w => Q * M w * Q.transpose) (fun w => Q * L w * Q.transpose) =
      action Q (jetOfRaw s M L) := by
  apply Prod.ext
  · funext w
    exact rawExteriorScalar_conjugate (s w) Q (M w) (L w) hQ
  · funext slot
    rcases slot with ⟨w, b⟩
    cases b
    · exact rawExterior_conjugate Q (M w) hQ hJ
    · exact rawExteriorDerivative_conjugate Q (M w) (L w) hQ

/-- Measure-preserving symmetry of the actual mark sample pushes to the
exterior law once equivariance of the constructed analytic field is proved. -/
theorem exterior_law_of_measurePreserving
    {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (jet : Ω → JetState I) (hjet : Measurable jet) (R : Ω → Ω)
    (hR : MeasurePreserving R P P) (Q : Mat)
    (hequiv : (fun ω => jet (R ω)) =ᵐ[P] (fun ω => action Q (jet ω))) :
    Measure.map (action Q) (Measure.map jet P) = Measure.map jet P := by
  rw [Measure.map_map (measurable_action Q) hjet]
  change Measure.map (fun ω => action Q (jet ω)) P = Measure.map jet P
  rw [← Measure.map_congr hequiv]
  change Measure.map (jet ∘ R) P = Measure.map jet P
  rw [← Measure.map_map hjet hR.measurable, hR.map_eq]

end GeneralizedBulk.Exterior
