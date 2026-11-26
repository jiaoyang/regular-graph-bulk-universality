import GeneralizedBulk.Entropy.RetainedKernelSymmetry

/-! The literal projected finite-signal symmetry yields Gaussian channel admissibility. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.Hermite
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

/-- All nonanalytic hypotheses are finite coordinate identities and equality
of weighted functions of the projected signal. The Gaussian conditional
operator and its reversal symmetry are proved here. -/
theorem subspaceConditionalL2_centered_mixture_symmetry
    (O R Q : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (hR : R * R.transpose = 1) (hQ : Q * Q.transpose = 1) (observed : Finset I)
    (hinv : ∀ y, Q.mulVec (Q.mulVec y) = y)
    (hcomm : ∀ y, coordinateProjection observed (Q.mulVec y) = Q.mulVec (coordinateProjection observed y))
    (hcoordinates : ∀ x, O.transpose.mulVec (R.mulVec x) = Q.mulVec (O.transpose.mulVec x))
    (weight : S → ℝ) (signal : S → I → ℝ)
    (hsym : ∀ F : (I → ℝ) → ℝ,
      (∑ s, weight s * F (Q.mulVec (coordinateProjection observed (O.transpose.mulVec (signal s))))) =
        ∑ s, weight s * F (coordinateProjection observed (O.transpose.mulVec (signal s))))
    (a : ℝ) (ha : 0 < 1 - a ^ 2) (f : Lp ℝ 2 (standardGaussian I))
    (hf : (f : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
      (fun x => finiteMixtureKernel weight signal a x - 1)) :
    gaussianPullback R hR (subspaceConditionalL2 O hO observed f) = subspaceConditionalL2 O hO observed f := by
  have hc := subspaceConditionalL2_centered_mixture_ae O hO observed weight signal a ha f hf
  have hcR := (standardGaussian_matrixAction_measurePreserving R hR).quasiMeasurePreserving.ae_eq_comp hc
  apply Lp.ext
  filter_upwards [gaussianPullback_ae R hR (subspaceConditionalL2 O hO observed f), hcR, hc] with x hx hy hz
  simp only [Function.comp_apply] at hy
  rw [hx, hy, hz, hcoordinates x]
  exact congrArg (fun t : ℝ => t - 1)
    (retained_mixture_symmetry observed Q hQ hinv hcomm weight
      (fun s => O.transpose.mulVec (signal s)) hsym a (O.transpose.mulVec x))

end GeneralizedBulk.Entropy.Mehler
