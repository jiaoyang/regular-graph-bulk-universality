import GeneralizedBulk.Entropy.MehlerMarginal
import GeneralizedBulk.Entropy.GaussianSubspaceChannels

/-! Actual orthogonal transport and subspace marginals of smoothing densities. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.Hermite
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem orthogonal_dotProduct (O : Matrix I I ℝ) (hO : O * O.transpose = 1) (y z : I → ℝ) :
    (∑ i, O.mulVec y i * O.mulVec z i) = ∑ i, y i * z i := by
  change O.mulVec y ⬝ᵥ O.mulVec z = y ⬝ᵥ z
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.mul_eq_one_comm.mpr hO, Matrix.vecMul_one]

theorem vectorKernel_orthogonal (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (a : ℝ) (y z : I → ℝ) : vectorKernel a (O.mulVec y) (O.mulVec z) = vectorKernel a y z := by
  unfold vectorKernel
  rw [orthogonal_dotProduct O hO z y]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [pow_two, orthogonal_dotProduct O hO]

theorem vectorKernel_pullback (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (a : ℝ) (y z : I → ℝ) : vectorKernel a y (O.mulVec z) = vectorKernel a (O.transpose.mulVec y) z := by
  have h := vectorKernel_orthogonal O hO a (O.transpose.mulVec y) z
  rw [Matrix.mulVec_mulVec, hO, Matrix.one_mulVec] at h
  exact h

variable {S : Type*} [Fintype S]

theorem finiteMixtureKernel_pullback (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (weight : S → ℝ) (signal : S → I → ℝ) (a : ℝ) (z : I → ℝ) :
    finiteMixtureKernel weight signal a (O.mulVec z) =
      finiteMixtureKernel weight (fun s => O.transpose.mulVec (signal s)) a z := by
  unfold finiteMixtureKernel
  simp_rw [vectorKernel_pullback O hO]

/-- A concrete representative formula for the actual subspace conditional
operator on a Gaussian-mixture density. The observation covariance and the
conditional density are constructed, rather than postulated. -/
theorem subspaceConditionalL2_mixture_ae (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (observed : Finset I) (weight : S → ℝ) (signal : S → I → ℝ)
    (a : ℝ) (ha : 0 < 1 - a ^ 2) (f : Lp ℝ 2 (standardGaussian I))
    (hf : (f : (I → ℝ) → ℝ) =ᵐ[standardGaussian I] finiteMixtureKernel weight signal a) :
    (subspaceConditionalL2 O hO observed f : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
      (fun x => finiteMixtureKernel weight
        (fun s => fun i : observed => O.transpose.mulVec (signal s) i)
        a (retainedCoordinates observed (O.transpose.mulVec x))) := by
  have hOt : O.transpose * O.transpose.transpose = 1 := by
    simpa using Matrix.mul_eq_one_comm.mpr hO
  have hpull : (gaussianPullback O hO f : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
      finiteMixtureKernel weight (fun s => O.transpose.mulVec (signal s)) a := by
    have he := (standardGaussian_matrixAction_measurePreserving O hO).quasiMeasurePreserving.ae_eq_comp hf
    filter_upwards [gaussianPullback_ae O hO f, he] with x hx hy
    simp only [Function.comp_apply] at hy
    rw [hx, hy]
    exact finiteMixtureKernel_pullback O hO weight signal a x
  have hc := (coordinateConditionalL2_ae observed (gaussianPullback O hO f)).trans
    ((condExp_congr_ae hpull).trans
      (condExp_finiteMixtureKernel observed weight (fun s => O.transpose.mulVec (signal s)) a ha))
  have htrans := (standardGaussian_matrixAction_measurePreserving O.transpose hOt).quasiMeasurePreserving.ae_eq_comp hc
  have hp := gaussianPullback_ae O.transpose hOt
    (coordinateConditionalL2 observed (gaussianPullback O hO f))
  exact hp.trans htrans

theorem subspaceConditionalL2_centered_mixture_ae (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (observed : Finset I) (weight : S → ℝ) (signal : S → I → ℝ)
    (a : ℝ) (ha : 0 < 1 - a ^ 2) (f : Lp ℝ 2 (standardGaussian I))
    (hf : (f : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
      (fun x => finiteMixtureKernel weight signal a x - 1)) :
    (subspaceConditionalL2 O hO observed f : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
      (fun x => finiteMixtureKernel weight
        (fun s => fun i : observed => O.transpose.mulVec (signal s) i)
        a (retainedCoordinates observed (O.transpose.mulVec x)) - 1) := by
  have hOt : O.transpose * O.transpose.transpose = 1 := by
    simpa using Matrix.mul_eq_one_comm.mpr hO
  have hpull : (gaussianPullback O hO f : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
      (fun x => finiteMixtureKernel weight (fun s => O.transpose.mulVec (signal s)) a x - 1) := by
    have he := (standardGaussian_matrixAction_measurePreserving O hO).quasiMeasurePreserving.ae_eq_comp hf
    filter_upwards [gaussianPullback_ae O hO f, he] with x hx hy
    simp only [Function.comp_apply] at hy
    rw [hx, hy, finiteMixtureKernel_pullback O hO]
  have hsub := condExp_sub
    (integrable_finiteMixtureKernel weight (fun s => O.transpose.mulVec (signal s)) a ha)
    (integrable_const (μ := standardGaussian I) (1 : ℝ)) (coordinateSigma observed)
  have hcond : (standardGaussian I)[
      (fun x => finiteMixtureKernel weight (fun s => O.transpose.mulVec (signal s)) a x - 1) |
        coordinateSigma observed] =ᵐ[standardGaussian I]
      (fun x => finiteMixtureKernel weight
        (fun s => fun i : observed => O.transpose.mulVec (signal s) i)
        a (retainedCoordinates observed x) - 1) := by
    filter_upwards [hsub, condExp_finiteMixtureKernel observed weight
      (fun s => O.transpose.mulVec (signal s)) a ha] with x hx hy
    simpa only [Pi.sub_apply, condExp_const (coordinateSigma_le observed), hy] using hx
  have hc := (coordinateConditionalL2_ae observed (gaussianPullback O hO f)).trans
    ((condExp_congr_ae hpull).trans hcond)
  have htrans := (standardGaussian_matrixAction_measurePreserving O.transpose hOt).quasiMeasurePreserving.ae_eq_comp hc
  exact (gaussianPullback_ae O.transpose hOt
    (coordinateConditionalL2 observed (gaussianPullback O hO f))).trans htrans

end GeneralizedBulk.Entropy.Mehler
