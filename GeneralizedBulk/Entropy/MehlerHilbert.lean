import GeneralizedBulk.Entropy.NormalizedFiniteSignal
import GeneralizedBulk.Entropy.MehlerRotation
import GeneralizedBulk.Analysis.MeasurePreservingIntegral

/-! Actual centered Gaussian-mixture vectors and their observation energies. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.Hermite GeneralizedBulk.Analysis
namespace NormalizedFiniteSignal
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]
variable (D : NormalizedFiniteSignal I S)

/-- The actual signal seen in an orthogonal observation channel. -/
def observedSignal (O : Matrix I I ℝ) (hO : O * O.transpose = 1) (observed : Finset I) :
    NormalizedFiniteSignal observed S :=
  (D.rotate O.transpose (by simpa using Matrix.mul_eq_one_comm.mpr hO)).restrict observed

theorem observedSignal_bound (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (observed : Finset I) (B : ℝ) (hB : ∀ s, coordinateL1 (D.signal s) ≤ B) (s : S) :
    coordinateL1 ((D.observedSignal O hO observed).signal s) ≤ (Fintype.card I : ℝ) * B := by
  exact ((D.rotate O.transpose (by simpa using Matrix.mul_eq_one_comm.mpr hO)).restrict_coordinateL1_le observed s).trans
    ((D.rotate_coordinateL1_le O.transpose (by simpa using Matrix.mul_eq_one_comm.mpr hO) s).trans
      (mul_le_mul_of_nonneg_left (hB s) (Nat.cast_nonneg _)))

variable (B a : ℝ) (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
variable (hsmall : a * B ≤ 1 / 2) (hsignal : ∀ s, coordinateL1 (D.signal s) ≤ B)

def centeredL2 : Lp ℝ 2 (standardGaussian I) :=
  ((D.centered_memLp_three B a hB ha ha1 hsmall hsignal).mono_exponent
    (by norm_num : (2 : ENNReal) ≤ 3)).toLp (fun z => D.density a z - 1)

theorem centeredL2_ae :
    (D.centeredL2 B a hB ha ha1 hsmall hsignal : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
      (fun z => D.density a z - 1) := MemLp.coeFn_toLp _

theorem centeredL2_norm_sq :
    ‖D.centeredL2 B a hB ha ha1 hsmall hsignal‖ ^ 2 =
      ∫ z, (D.density a z - 1) ^ 2 ∂standardGaussian I :=
  lp_two_norm_sq_of_ae _ _ (D.centeredL2_ae B a hB ha ha1 hsmall hsignal)

theorem channel_centeredL2_ae (O : Matrix I I ℝ) (hO : O * O.transpose = 1) (observed : Finset I) :
    (subspaceConditionalL2 O hO observed (D.centeredL2 B a hB ha ha1 hsmall hsignal) : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
      (fun x => (D.observedSignal O hO observed).density a
        (retainedCoordinates observed (O.transpose.mulVec x)) - 1) := by
  have hden : 0 < 1 - a ^ 2 := by
    nlinarith [mul_nonneg ha (show 0 ≤ 1 / 2 - a by linarith)]
  exact subspaceConditionalL2_centered_mixture_ae O hO observed D.weight D.signal a hden _
    (D.centeredL2_ae B a hB ha ha1 hsmall hsignal)

theorem channel_centeredL2_norm_sq (O : Matrix I I ℝ) (hO : O * O.transpose = 1) (observed : Finset I) :
    ‖subspaceConditionalL2 O hO observed (D.centeredL2 B a hB ha ha1 hsmall hsignal)‖ ^ 2 =
      ∫ z, ((D.observedSignal O hO observed).density a z - 1) ^ 2 ∂standardGaussian observed := by
  rw [lp_two_norm_sq_of_ae _ _ (D.channel_centeredL2_ae B a hB ha ha1 hsmall hsignal O hO observed)]
  have hOt : O.transpose * O.transpose.transpose = 1 := by
    simpa using Matrix.mul_eq_one_comm.mpr hO
  have hmp := (retainedCoordinates_measurePreserving observed).comp
    (standardGaussian_matrixAction_measurePreserving O.transpose hOt)
  exact integral_comp_measurePreserving hmp _
    (((D.observedSignal O hO observed).density_continuous a).sub continuous_const |>.pow 2).aestronglyMeasurable

/-- The lifted actual marginal density and the lower-dimensional signal have
exactly the same relative entropy. -/
theorem channel_centeredL2_relativeEntropy (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (observed : Finset I) :
    relativeEntropy (standardGaussian I)
      (fun x => 1 + subspaceConditionalL2 O hO observed (D.centeredL2 B a hB ha ha1 hsmall hsignal) x) =
      relativeEntropy (standardGaussian observed) ((D.observedSignal O hO observed).density a) := by
  have he := D.channel_centeredL2_ae B a hB ha ha1 hsmall hsignal O hO observed
  unfold relativeEntropy
  calc
    _ = ∫ x, (D.observedSignal O hO observed).density a
        (retainedCoordinates observed (O.transpose.mulVec x)) *
      Real.log ((D.observedSignal O hO observed).density a
        (retainedCoordinates observed (O.transpose.mulVec x))) ∂standardGaussian I := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
      congr 2 <;> ring
    _ = _ := by
      have hOt : O.transpose * O.transpose.transpose = 1 := by
        simpa using Matrix.mul_eq_one_comm.mpr hO
      have hmp := (retainedCoordinates_measurePreserving observed).comp
        (standardGaussian_matrixAction_measurePreserving O.transpose hOt)
      exact integral_comp_measurePreserving hmp _
        (Real.continuous_mul_log.comp ((D.observedSignal O hO observed).density_continuous a)).aestronglyMeasurable

end NormalizedFiniteSignal
end GeneralizedBulk.Entropy.Mehler
