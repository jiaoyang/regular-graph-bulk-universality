import GeneralizedBulk.Entropy.ColoredFourthCoercivity

/-! Continuous coefficient recovery and pointwise evaluation on actual finite
Gaussian chaos. These identify admissibility as a closed finite-dimensional
condition without assuming operator-norm continuity on the whole L² space. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
variable (I : Type*) [Fintype I] [DecidableEq I]

def fullChaosEquiv (degree : ℕ) : (DegreeIndex I degree → ℝ) ≃ₗ[ℝ] fullChaosSpace I degree :=
  LinearEquiv.ofInjective (fullChaosMap I degree) (fullChaosMap_injective I degree)

def fullChaosCoordinates (degree : ℕ) : fullChaosSpace I degree →L[ℝ] (DegreeIndex I degree → ℝ) :=
  (fullChaosEquiv I degree).symm.toContinuousLinearMap

theorem fullChaosCoordinates_spec (degree : ℕ) (f : fullChaosSpace I degree) :
    fullChaosMap I degree (fullChaosCoordinates I degree f) = (f : Lp ℝ 2 (standardGaussian I)) := by
  exact congrArg (fun g : fullChaosSpace I degree => (g : Lp ℝ 2 (standardGaussian I)))
    ((fullChaosEquiv I degree).apply_symm_apply f)

@[simp] theorem fullChaosCoordinates_apply_map (degree : ℕ) (coeff : DegreeIndex I degree → ℝ) :
    fullChaosCoordinates I degree (fullChaosEquiv I degree coeff) = coeff :=
  (fullChaosEquiv I degree).symm_apply_apply coeff

/-- Evaluation is a genuine continuous linear functional on the actual
finite-dimensional L² chaos, with the canonical polynomial representative. -/
def fullChaosEval (degree : ℕ) (x : I → ℝ) : fullChaosSpace I degree →L[ℝ] ℝ :=
  ∑ a : DegreeIndex I degree, (multiHermite I (degreeIndexNat I a) x) •
    ((ContinuousLinearMap.proj a).comp (fullChaosCoordinates I degree))

theorem fullChaosEval_apply (degree : ℕ) (x : I → ℝ) (f : fullChaosSpace I degree) :
    fullChaosEval I degree x f = chaosFunction (degreeIndexNat I) (fullChaosCoordinates I degree f) x := by
  simp only [fullChaosEval, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, chaosFunction, mul_comm]

/-- Joint pointwise evaluation is continuous both in the actual L² chaos
vector and in its Euclidean argument. -/
theorem continuous_fullChaosEval (degree : ℕ) :
    Continuous (fun z : fullChaosSpace I degree × (I → ℝ) => fullChaosEval I degree z.2 z.1) := by
  simp_rw [fullChaosEval_apply, chaosFunction]
  apply continuous_finset_sum
  intro a ha
  exact ((continuous_apply a).comp ((fullChaosCoordinates I degree).continuous.comp continuous_fst)).mul
    ((continuous_multiHermite I (degreeIndexNat I a)).comp continuous_snd)

/-- L² reversal equality is equivalent to the corresponding pointwise
polynomial identity, so its closed graph can be checked by actual evaluation. -/
theorem fullChaos_pullback_eq_iff (degree : ℕ) (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (f : fullChaosSpace I degree) :
    gaussianPullback O hO (f : Lp ℝ 2 (standardGaussian I)) = f ↔
      ∀ x, fullChaosEval I degree (O.mulVec x) f = fullChaosEval I degree x f := by
  let coeff := fullChaosCoordinates I degree f
  have hf : chaosLp (degreeIndexNat I) coeff = (f : Lp ℝ 2 (standardGaussian I)) := fullChaosCoordinates_spec I degree f
  simp_rw [fullChaosEval_apply]
  constructor
  · intro h x
    have hh : chaosLp (degreeIndexNat I) coeff = gaussianPullback O hO (chaosLp (degreeIndexNat I) coeff) := by rw [hf, h]
    have hp := chaosFunction_eq_pullback_of_lp_eq (degreeIndexNat I) coeff (degreeIndexNat I) coeff
      O hO degree (fun a => (degreeIndexNat_sum I a).le) (fun a => (degreeIndexNat_sum I a).le) hh
    exact (congrFun hp x).symm
  · intro h
    apply Lp.ext
    have hae := (standardGaussian_matrixAction_measurePreserving O hO).quasiMeasurePreserving.ae_eq_comp
      (chaosLp_ae (degreeIndexNat I) coeff)
    filter_upwards [gaussianPullback_ae O hO (f : Lp ℝ 2 (standardGaussian I)), hae,
      chaosLp_ae (degreeIndexNat I) coeff] with x hp hc hx
    simp only [Function.comp_apply] at hc
    rw [hf] at hc hx
    rw [hp, hc, hx]
    exact h x

end GeneralizedBulk.Entropy.Hermite
