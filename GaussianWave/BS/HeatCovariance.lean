import GaussianWave.BS.WhiteSecondMoments

/-!
# Actual directional second moments along the heat flow

A unit directional projection is a genuine one-row orthonormal observation.
Commutation of that observation with heat flow and the proved convolution
moment formula give its variance. No Gaussianity of the input is used.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

theorem integrable_linearForm_sq_of_squareRadius
    {I : Type*} [Fintype I] (μ : Measure (I → ℝ))
    (hμ : Integrable (squareRadius (I := I)) μ) (v : I → ℝ) :
    Integrable (fun x => finiteLinearForm v x ^ 2) μ := by
  refine (hμ.const_mul (squareRadius v)).mono'
    ((continuous_finiteLinearForm v).pow 2).measurable.aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v x

theorem integrable_heatedLaw_linearForm_sq
    {I : Type*} [Fintype I] (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (t : ℝ) (v : I → ℝ) :
    Integrable (fun x => finiteLinearForm v x ^ 2) (heatedLaw μ t) :=
  integrable_linearForm_sq_of_squareRadius _ (integrable_heatedLaw_squareRadius μ hμ t) v

/-- Every actual unit-direction second moment becomes exactly 1+2t. -/
theorem integral_heatedLaw_unitLinearForm_sq
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (hmom : HasIdentitySecondMoments μ)
    {t : ℝ} (ht : 0 < t) (v : I → ℝ) (hv : squareRadius v = 1) :
    (∫ x, finiteLinearForm v x ^ 2 ∂heatedLaw μ t) = 1 + 2 * t := by
  let O : Matrix (Fin 1) I ℝ := fun _ => v
  have hO : O * O.transpose = 1 := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, O, squareRadius, pow_two] using hv
  let ν := Measure.map (fun x => O.mulVec x) μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map (measurable_finiteMatrixAction O).aemeasurable
  have hν : Integrable (squareRadius (I := Fin 1)) ν := integrable_squareRadius_matrixImage μ hμ O
  have hmoment : (∫ x, squareRadius x ∂ν) = 1 := by
    simpa using integral_squareRadius_projection_of_identitySecondMoments μ hμ hmom O hO
  have h := integral_heatedLaw_squareRadius ν hν t
  rw [hmoment, coe_heatVariance ht.le] at h
  simp only [Fintype.card_fin, Nat.cast_one, one_mul] at h
  rw [← heatedLaw_map_orthonormal_rows μ O hO,
    integral_map (measurable_finiteMatrixAction O).aemeasurable
      continuous_squareRadius.measurable.aestronglyMeasurable] at h
  simpa only [squareRadius, Fin.sum_univ_one, O, Matrix.mulVec, dotProduct, finiteLinearForm] using h

theorem integrable_heatDensity_mul_linearForm_sq
    {I : Type*} [Fintype I] (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) (v : I → ℝ) :
    Integrable (fun x => heatDensity μ t x * finiteLinearForm v x ^ 2) := by
  have hi := integrable_heatedLaw_linearForm_sq μ hμ t v
  rw [heatedLaw_eq_withDensity μ ht] at hi
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_heatDensity μ t).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hi
  simpa only [ENNReal.toReal_ofReal (heatDensity_nonneg _ _ _), smul_eq_mul] using h

theorem integral_heatDensity_mul_unitLinearForm_sq
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (hmom : HasIdentitySecondMoments μ)
    {t : ℝ} (ht : 0 < t) (v : I → ℝ) (hv : squareRadius v = 1) :
    (∫ x, heatDensity μ t x * finiteLinearForm v x ^ 2) = 1 + 2 * t := by
  have h := integral_withDensity_eq_integral_toReal_smul
    (μ := (volume : Measure (I → ℝ))) (measurable_heatDensity μ t).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) (fun x => finiteLinearForm v x ^ 2)
  simp only [ENNReal.toReal_ofReal (heatDensity_nonneg _ _ _), smul_eq_mul] at h
  rw [← h, ← heatedLaw_eq_withDensity μ ht]
  exact integral_heatedLaw_unitLinearForm_sq μ hμ hmom ht v hv

theorem integral_heatedLaw_linearForm_sq
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (hmom : HasIdentitySecondMoments μ)
    {t : ℝ} (ht : 0 < t) (v : I → ℝ) :
    (∫ x, finiteLinearForm v x ^ 2 ∂heatedLaw μ t) = (1 + 2 * t) * squareRadius v := by
  by_cases hzero : squareRadius v = 0
  · have hvzero : v = 0 := by
      ext i
      have hi : v i ^ 2 ≤ squareRadius v :=
        Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
      rw [hzero] at hi
      simpa using (sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _)))
    simp [hvzero, finiteLinearForm, squareRadius]
  · let s := Real.sqrt (squareRadius v)
    have hs : 0 < s := Real.sqrt_pos.mpr
      (lt_of_le_of_ne (squareRadius_nonneg v) (Ne.symm hzero))
    have hs2 : s ^ 2 = squareRadius v := Real.sq_sqrt (squareRadius_nonneg v)
    let w : I → ℝ := fun i => v i / s
    have hw : squareRadius w = 1 := by
      simp only [squareRadius, w, div_pow, ← Finset.sum_div]
      change squareRadius v / s ^ 2 = 1
      rw [hs2, div_self hzero]
    have hvw : v = fun i => s * w i := by
      ext i
      dsimp [w]
      field_simp
    have heq : (fun x => finiteLinearForm v x ^ 2) =
        (fun x => s ^ 2 * finiteLinearForm w x ^ 2) := by
      funext x
      rw [hvw, finiteLinearForm_scale_coeff, mul_pow]
    rw [heq, integral_const_mul, integral_heatedLaw_unitLinearForm_sq μ hμ hmom ht w hw, hs2]
    ring

theorem integrable_linearForm_mul_of_squareRadius
    {I : Type*} [Fintype I] (μ : Measure (I → ℝ))
    (hμ : Integrable (squareRadius (I := I)) μ) (u v : I → ℝ) :
    Integrable (fun x => finiteLinearForm u x * finiteLinearForm v x) μ := by
  have heq : (fun x => finiteLinearForm u x * finiteLinearForm v x) =
      (fun x => (1 / 2 : ℝ) * ((finiteLinearForm (u + v) x ^ 2 - finiteLinearForm u x ^ 2) -
        finiteLinearForm v x ^ 2)) := by
    funext x
    have hadd : finiteLinearForm (u + v) x = finiteLinearForm u x + finiteLinearForm v x := by
      simp [finiteLinearForm, add_mul, Finset.sum_add_distrib]
    rw [hadd]
    ring
  rw [heq]
  exact (((integrable_linearForm_sq_of_squareRadius μ hμ (u + v)).sub
    (integrable_linearForm_sq_of_squareRadius μ hμ u)).sub
    (integrable_linearForm_sq_of_squareRadius μ hμ v)).const_mul _

/-- Full directional covariance after heating, including cross-channel and
cross-transverse directions; the claim is not restricted to rank-one tests. -/
theorem integral_heatedLaw_linearForm_mul
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (hmom : HasIdentitySecondMoments μ)
    {t : ℝ} (ht : 0 < t) (u v : I → ℝ) :
    (∫ x, finiteLinearForm u x * finiteLinearForm v x ∂heatedLaw μ t) =
      (1 + 2 * t) * ∑ i, u i * v i := by
  have heq : (fun x => finiteLinearForm u x * finiteLinearForm v x) =
      (fun x => (1 / 2 : ℝ) * ((finiteLinearForm (u + v) x ^ 2 - finiteLinearForm u x ^ 2) -
        finiteLinearForm v x ^ 2)) := by
    funext x
    have hadd : finiteLinearForm (u + v) x = finiteLinearForm u x + finiteLinearForm v x := by
      simp [finiteLinearForm, add_mul, Finset.sum_add_distrib]
    rw [hadd]
    ring
  have hu := integrable_heatedLaw_linearForm_sq μ hμ t u
  have hv := integrable_heatedLaw_linearForm_sq μ hμ t v
  have huv := integrable_heatedLaw_linearForm_sq μ hμ t (u + v)
  rw [heq, integral_const_mul,
    integral_sub (f := fun x => finiteLinearForm (u + v) x ^ 2 - finiteLinearForm u x ^ 2)
      (huv.sub hu) hv,
    integral_sub (f := fun x => finiteLinearForm (u + v) x ^ 2) huv hu]
  simp_rw [integral_heatedLaw_linearForm_sq μ hμ hmom ht]
  have hq : squareRadius (u + v) = squareRadius u + 2 * (∑ i, u i * v i) + squareRadius v := by
    unfold squareRadius
    simp only [Pi.add_apply]
    simp_rw [add_sq]
    simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [hq]
  ring

theorem integral_heatDensity_mul_linearForm_mul
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (hmom : HasIdentitySecondMoments μ)
    {t : ℝ} (ht : 0 < t) (u v : I → ℝ) :
    (∫ x, heatDensity μ t x * (finiteLinearForm u x * finiteLinearForm v x)) =
      (1 + 2 * t) * ∑ i, u i * v i := by
  have h := integral_withDensity_eq_integral_toReal_smul
    (μ := (volume : Measure (I → ℝ))) (measurable_heatDensity μ t).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))
    (fun x => finiteLinearForm u x * finiteLinearForm v x)
  simp only [ENNReal.toReal_ofReal (heatDensity_nonneg _ _ _), smul_eq_mul] at h
  rw [← h, ← heatedLaw_eq_withDensity μ ht]
  exact integral_heatedLaw_linearForm_mul μ hμ hmom ht u v

end GaussianWave.BS
