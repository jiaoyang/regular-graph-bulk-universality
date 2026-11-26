import GeneralizedBulk.Gaussian.SeriesActual
import GeneralizedBulk.Gaussian.SeriesEquivariance
import GeneralizedBulk.Gaussian.Invariant

/-! # Actual Gaussian mark rotation acts equivariantly on the infinite L² anchor -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators

namespace GeneralizedBulk.Gaussian

/-- The centered quadratic of a rotated mark is its matrix conjugate. -/
theorem rawQuadratic_matrixAction (p : ℝ) (O : Matrix (Fin 4) (Fin 4) ℝ)
    (hO : O * covarianceMatrix p * O.transpose = covarianceMatrix p)
    (y : Fin 4 → ℝ) (i j : Fin 4) :
    rawQuadratic p i j (O.mulVec y) =
      ∑ a : Fin 4, ∑ b : Fin 4, (O i a * O j b) * rawQuadratic p a b y := by
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) hO
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four] at hc
  simp only [rawQuadratic, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  linear_combination hc

variable {Ω κ : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

theorem coeFn_finset_sum_L2 (s : Finset κ) (f : κ → Lp ℂ 2 μ) :
    (fun ω => (∑ a ∈ s, f a) ω) =ᵐ[μ] (fun ω => ∑ a ∈ s, f a ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero ℂ 2 μ)
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (f a) (∑ b ∈ s, f b), ih] with ω hω hi
      simp only [Pi.add_apply, hi] at hω
      exact hω

/-- L² endpoint conjugation has the expected pointwise representative. -/
theorem conjugateL2_ae (O : EndpointMatrix)
    (M : Matrix (Fin 4) (Fin 4) (Lp ℂ 2 μ)) (i j : Fin 4) :
    (fun ω => conjugateL2 μ O M i j ω) =ᵐ[μ]
      (fun ω => ∑ a : Fin 4, ∑ b : Fin 4, (O i a * O j b) * M a b ω) := by
  have hi : ∀ᵐ ω ∂μ, ∀ a : Fin 4,
      (∑ b : Fin 4, (O i a * O j b) • M a b) ω =
        ∑ b : Fin 4, ((O i a * O j b) • M a b) ω :=
    ae_all_iff.mpr (fun a => coeFn_finset_sum_L2 μ Finset.univ _)
  have hs : ∀ᵐ ω ∂μ, ∀ a b : Fin 4,
      ((O i a * O j b) • M a b) ω = (O i a * O j b) * M a b ω :=
    ae_all_iff.mpr (fun a => ae_all_iff.mpr (fun b => by
      simpa only [Pi.smul_apply, smul_eq_mul] using Lp.coeFn_smul (O i a * O j b) (M a b)))
  filter_upwards [coeFn_finset_sum_L2 μ Finset.univ
    (fun a => ∑ b : Fin 4, (O i a * O j b) • M a b), hi, hs] with ω ho hi hs
  change (∑ a : Fin 4, ∑ b : Fin 4, (O i a * O j b) • M a b) ω = _
  rw [ho]
  simp only [hi, hs]

/-- Actual Gaussian quadratic marks satisfy the finite L² equivariance needed
by the infinite-series pullback theorem. -/
theorem markQuadraticLp_equivariant (p : ℝ) (hp : |p| < 1)
    (O : Matrix (Fin 4) (Fin 4) ℝ)
    (hO : O * covarianceMatrix p * O.transpose = covarianceMatrix p)
    (I : Type*) (n : I) (i j : Fin 4) :
    pullbackL2 (iidLaw (markLaw p) I)
      (coordinateAction (fun y : Fin 4 → ℝ => O.mulVec y))
      (markFamily_matrixAction_measurePreserving p hp O hO I) (markQuadraticLp p n i j) =
    conjugateL2 (iidLaw (markLaw p) I) (O.map Complex.ofReal)
      (fun a b => markQuadraticLp p n a b) i j := by
  let μ := iidLaw (markLaw p) I
  let T := coordinateAction (fun y : Fin 4 → ℝ => O.mulVec y) (I := I)
  have hT := markFamily_matrixAction_measurePreserving p hp O hO I
  have ht := hT.quasiMeasurePreserving.ae_eq_comp (markQuadraticLp_ae p n i j)
  have hr : ∀ᵐ ω ∂μ, ∀ a b : Fin 4,
      markQuadraticLp p n a b ω = (markQuadraticFamily p n a b ω : ℂ) :=
    ae_all_iff.mpr (fun a => ae_all_iff.mpr (fun b => markQuadraticLp_ae p n a b))
  apply Lp.ext
  filter_upwards [pullbackL2_ae μ T hT (markQuadraticLp p n i j), ht,
    conjugateL2_ae μ (O.map Complex.ofReal) (fun a b => markQuadraticLp p n a b) i j, hr]
      with ω hpull hraw hconj hr
  rw [hpull, hconj]
  change markQuadraticLp p n i j (T ω) = _ at hraw
  rw [hraw]
  simp only [Matrix.map_apply, hr]
  change ((rawQuadratic p i j (O.mulVec (ω n)) : ℝ) : ℂ) =
    ∑ a : Fin 4, ∑ b : Fin 4, ((O i a : ℝ) : ℂ) * (O j b : ℂ) *
      (rawQuadratic p a b (ω n) : ℂ)
  exact_mod_cast rawQuadratic_matrixAction p O hO (ω n) i j

/-- The genuine covariance-preserving iid Gaussian action conjugates every
L² marked-series slot, including the anchor and spectral derivative slots. -/
theorem gaussianSeries_L2_equivariant (parameters : Parameters) (s : AnchoredCountingState)
    (O : Matrix (Fin 4) (Fin 4) ℝ)
    (hO : O * covarianceMatrix parameters.p * O.transpose = covarianceMatrix parameters.p)
    (v : ℂ × Bool) (i j : Fin 4) :
    pullbackL2 (iidLaw (markLaw parameters.p) s.val.1.ParticleLabels)
      (coordinateAction (fun y : Fin 4 → ℝ => O.mulVec y))
      (markFamily_matrixAction_measurePreserving _ parameters.abs_p_lt_one O hO _)
      (l2Series (iidLaw (markLaw parameters.p) s.val.1.ParticleLabels)
        (fun n => markQuadraticLp parameters.p n i j)
        (fun n => (parameters.scale : ℂ) * particleCoefficient (s.val.1.particleLocation n) v)) =
    conjugateL2 (iidLaw (markLaw parameters.p) s.val.1.ParticleLabels) (O.map Complex.ofReal)
      (fun a b => l2Series (iidLaw (markLaw parameters.p) s.val.1.ParticleLabels)
        (fun n => markQuadraticLp parameters.p n a b)
        (fun n => (parameters.scale : ℂ) * particleCoefficient (s.val.1.particleLocation n) v)) i j := by
  apply l2Series_equivariant
  · intro a b
    apply summable_weighted_orthogonal _ _ 2
      (fun n m hnm => markQuadraticLp_inner_off _ parameters.abs_p_lt_one hnm a b)
      (by norm_num) (fun n => markQuadraticLp_norm_sq_le_two _ parameters.abs_p_lt_one n a b)
    simpa only [norm_mul, mul_pow] using (summable_particleCoefficient_sq s v).mul_left (‖(parameters.scale : ℂ)‖ ^ 2)
  · intro n a b
    exact markQuadraticLp_equivariant _ parameters.abs_p_lt_one O hO _ n a b

end GeneralizedBulk.Gaussian
