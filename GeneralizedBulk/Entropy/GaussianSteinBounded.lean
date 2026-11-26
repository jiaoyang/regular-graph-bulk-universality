import GeneralizedBulk.Entropy.ChaosDecomposition

/-! Gaussian integration by parts for actual bounded C¹ functions with
bounded continuous derivative, with boundary integrability proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped NNReal
namespace GeneralizedBulk.Entropy.Hermite
open GeneralizedBulk.Gaussian

/-- The actual Gaussian creation-adjoint identity beyond polynomial tests.
Both the primitive and its derivative are integrable before FTC is applied. -/
theorem gaussian_creation_adjoint_bounded (P : ℝ[X]) (f g : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    (M L : ℝ) (hM : ∀ x, |f x| ≤ M) (hL : ∀ x, |g x| ≤ L) :
    (∫ x : ℝ, g x * P.eval x ∂standardNormal) =
      ∫ x : ℝ, f x * (X * P - P.derivative).eval x ∂standardNormal := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hfg (Q : ℝ[X]) : Integrable (fun x => f x * Q.eval x) standardNormal :=
    (integrable_polynomial Q).bdd_mul hfc.aestronglyMeasurable ⟨M, hM⟩
  have hgg (Q : ℝ[X]) : Integrable (fun x => g x * Q.eval x) standardNormal :=
    (integrable_polynomial Q).bdd_mul hg.aestronglyMeasurable ⟨L, hL⟩
  let A := fun x : ℝ => g x * P.eval x - f x * (X * P - P.derivative).eval x
  have hA : Integrable A standardNormal := (hgg P).sub (hfg _)
  have hprimitive : Integrable (fun x => gaussianPDFReal 0 1 x * (f x * P.eval x)) :=
    integrable_pdf_mul (hfg P)
  have hderivative := integrable_pdf_mul hA
  have hd (x : ℝ) : HasDerivAt (fun y => gaussianPDFReal 0 1 y * (f y * P.eval y))
      (gaussianPDFReal 0 1 x * A x) x := by
    convert (hasDerivAt_pdf x).mul ((hf x).mul (P.hasDerivAt x)) using 1
    dsimp only [A]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
    ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd hderivative hprimitive
  have hgauss : (∫ x : ℝ, A x ∂standardNormal) = 0 := by
    rw [standardNormal, ProbabilityTheory.integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
    exact hz
  change (∫ x : ℝ, g x * P.eval x - f x * (X * P - P.derivative).eval x ∂standardNormal) = 0 at hgauss
  rw [integral_sub (hgg P) (hfg _)] at hgauss
  exact sub_eq_zero.mp hgauss

end GeneralizedBulk.Entropy.Hermite
