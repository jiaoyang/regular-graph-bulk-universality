import GeneralizedBulk.Entropy.DirectionalLp

/-! Derivative commutation and Pythagoras for the genuine Gaussian channels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]

/-- Retained-coordinate differentiation commutes with genuine conditional
expectation on every finite Gaussian polynomial. -/
theorem coordinateConditionalL2_derivative (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (i : I) (hi : i ∈ observed) :
    coordinateConditionalL2 observed (chaosDerivativeLp a coeff i) =
      chaosDerivativeLp a (fun k => if supportedOn observed (a k) then coeff k else 0) i := by
  classical
  have hd : chaosDerivativeLp a coeff i =
      chaosLp (fun k => lower (a k) i) (fun k => coeff k * (a k i : ℝ)) := by
    simp only [chaosDerivativeLp, derivativeLp, chaosLp, smul_smul]
  rw [hd, coordinateConditionalL2_chaosLp]
  unfold projectedChaosLp chaosLp chaosDerivativeLp derivativeLp
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only
  simp only [supportedOn_lower_iff observed (a k) i hi]
  split_ifs <;> simp [smul_smul]

/-- Every retained linear combination of derivatives also commutes. -/
theorem coordinateConditionalL2_directional (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (v : I → ℝ)
    (hv : ∀ i, i ∉ observed → v i = 0) :
    coordinateConditionalL2 observed (directionalLp a coeff v) =
      directionalLp a (fun k => if supportedOn observed (a k) then coeff k else 0) v := by
  classical
  simp only [directionalLp, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hio : i ∈ observed
  · rw [coordinateConditionalL2_derivative observed a coeff i hio]
  · simp [hv i hio]

/-- Pythagoras holds for the actual rotated conditional expectation on all
Gaussian L² random variables. -/
theorem subspaceConditionalL2_pythagoras (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (observed : Finset I) (f : Lp ℝ 2 (standardGaussian I)) :
    ‖f - subspaceConditionalL2 O hO observed f‖ ^ 2 =
      ‖f‖ ^ 2 - ‖subspaceConditionalL2 O hO observed f‖ ^ 2 := by
  have hi := subspaceConditionalL2_inner_of_measurable O hO observed f
    (subspaceConditionalL2 O hO observed f) (subspaceConditionalL2_measurable O hO observed f)
  rw [real_inner_self_eq_norm_sq] at hi
  rw [norm_sub_sq_real, ← hi]
  ring

/-- Polynomial directional differentiation commutes with the actual observation
in arbitrary orthogonal coordinates, whenever that direction is retained. -/
theorem subspaceConditionalL2_directional {J : Type*} [Fintype J]
    (O : Matrix I I ℝ) (hO : O * O.transpose = 1) (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (b : J → I → ℕ) (other : J → ℝ)
    (degree : ℕ) (ha : ∀ k, (∑ i, a k i) ≤ degree) (hb : ∀ j, (∑ i, b j i) ≤ degree)
    (heq : chaosLp b other = subspaceConditionalL2 O hO observed (chaosLp a coeff))
    (v : I → ℝ) (hv : ∀ i, i ∉ observed → O.transpose.mulVec v i = 0) :
    subspaceConditionalL2 O hO observed (directionalLp a coeff v) = directionalLp b other v := by
  classical
  have hOt : O.transpose * O.transpose.transpose = 1 := by simpa using Matrix.mul_eq_one_comm.mpr hO
  have hrot := gaussianPullback_mem_lpFiltration O hO degree (chaosLp_mem_lpFiltration I a coeff degree ha)
  obtain ⟨g, hg⟩ := exists_lpFiltration_coefficients I hrot
  let t := O.transpose.mulVec v
  have hOt_v : O.mulVec t = v := by
    simp only [t, Matrix.mulVec_mulVec, hO, Matrix.one_mulVec]
  have hga := directionalLp_pullback a coeff (atMostIndexNat I) g O hO degree ha
    (atMostIndexNat_degree I) hg t
  rw [hOt_v] at hga
  let p := fun k => if supportedOn observed (atMostIndexNat I k) then g k else 0
  have hproj : chaosLp (atMostIndexNat I) p = gaussianPullback O hO (chaosLp b other) := by
    rw [heq, subspaceConditionalL2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, gaussianPullback_transpose_inverse]
    change chaosLp (atMostIndexNat I) p = coordinateConditionalL2 observed (gaussianPullback O hO (chaosLp a coeff))
    rw [← hg, coordinateConditionalL2_chaosLp]
    rfl
  have hgb := directionalLp_pullback b other (atMostIndexNat I) p O hO degree hb
    (atMostIndexNat_degree I) hproj t
  rw [hOt_v] at hgb
  have hcomm := coordinateConditionalL2_directional observed (atMostIndexNat I) g t hv
  change coordinateConditionalL2 observed (directionalLp (atMostIndexNat I) g t) =
    directionalLp (atMostIndexNat I) p t at hcomm
  have hh : gaussianPullback O hO
      (subspaceConditionalL2 O hO observed (directionalLp a coeff v)) =
      gaussianPullback O hO (directionalLp b other v) := by
    rw [subspaceConditionalL2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, gaussianPullback_transpose_inverse]
    change coordinateConditionalL2 observed (gaussianPullback O hO (directionalLp a coeff v)) = _
    rw [← hga, hcomm, hgb]
  exact (gaussianPullback O hO).injective hh


/-- A Gaussian observation polynomial has zero derivative in every discarded
coordinate; the statement is a literal identity in Gaussian L². -/
theorem projectedChaosLp_derivative_eq_zero (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (i : I) (hi : i ∉ observed) :
    chaosDerivativeLp a (fun k => if supportedOn observed (a k) then coeff k else 0) i = 0 := by
  classical
  unfold chaosDerivativeLp derivativeLp
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hs : supportedOn observed (a k)
  · simp [hs, hs i hi]
  · simp [hs]

theorem projectedChaosLp_directional_eq_zero (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (v : I → ℝ)
    (hv : ∀ i, i ∈ observed → v i = 0) :
    directionalLp a (fun k => if supportedOn observed (a k) then coeff k else 0) v = 0 := by
  classical
  unfold directionalLp
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hio : i ∈ observed
  · simp [hv i hio]
  · rw [projectedChaosLp_derivative_eq_zero observed a coeff i hio, smul_zero]

/-- The actual channel output has no derivative orthogonal to the observation
subspace, proved using its concrete Gaussian conditional representation. -/
theorem subspaceConditionalL2_directional_eq_zero {J : Type*} [Fintype J]
    (O : Matrix I I ℝ) (hO : O * O.transpose = 1) (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (b : J → I → ℕ) (other : J → ℝ)
    (degree : ℕ) (ha : ∀ k, (∑ i, a k i) ≤ degree) (hb : ∀ j, (∑ i, b j i) ≤ degree)
    (heq : chaosLp b other = subspaceConditionalL2 O hO observed (chaosLp a coeff))
    (v : I → ℝ) (hv : ∀ i, i ∈ observed → O.transpose.mulVec v i = 0) :
    directionalLp b other v = 0 := by
  classical
  have hrot := gaussianPullback_mem_lpFiltration O hO degree (chaosLp_mem_lpFiltration I a coeff degree ha)
  obtain ⟨g, hg⟩ := exists_lpFiltration_coefficients I hrot
  let t := O.transpose.mulVec v
  have hOt_v : O.mulVec t = v := by
    simp only [t, Matrix.mulVec_mulVec, hO, Matrix.one_mulVec]
  let p := fun k => if supportedOn observed (atMostIndexNat I k) then g k else 0
  have hproj : chaosLp (atMostIndexNat I) p = gaussianPullback O hO (chaosLp b other) := by
    rw [heq, subspaceConditionalL2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, gaussianPullback_transpose_inverse]
    change chaosLp (atMostIndexNat I) p = coordinateConditionalL2 observed (gaussianPullback O hO (chaosLp a coeff))
    rw [← hg, coordinateConditionalL2_chaosLp]
    rfl
  have hgb := directionalLp_pullback b other (atMostIndexNat I) p O hO degree hb
    (atMostIndexNat_degree I) hproj t
  rw [hOt_v] at hgb
  have hz := projectedChaosLp_directional_eq_zero observed (atMostIndexNat I) g t hv
  change directionalLp (atMostIndexNat I) p t = 0 at hz
  apply (gaussianPullback O hO).injective
  rw [map_zero, ← hgb, hz]


/-- The gradient of the actual observation polynomial belongs pointwise to
its observation subspace. No sample-dependent exceptional set is used. -/
theorem subspaceConditionalL2_gradient_retained {J : Type*} [Fintype J]
    (O : Matrix I I ℝ) (hO : O * O.transpose = 1) (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (b : J → I → ℕ) (other : J → ℝ)
    (degree : ℕ) (ha : ∀ k, (∑ i, a k i) ≤ degree) (hb : ∀ j, (∑ i, b j i) ≤ degree)
    (heq : chaosLp b other = subspaceConditionalL2 O hO observed (chaosLp a coeff))
    (x : I → ℝ) (i : I) (hi : i ∉ observed) :
    O.transpose.mulVec (fun j => chaosDerivativeFunction b other j x) i = 0 := by
  classical
  let v : I → ℝ := O.mulVec (Pi.single i 1)
  have hv : ∀ j, j ∈ observed → O.transpose.mulVec v j = 0 := by
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    change O.transpose.mulVec (O.mulVec (Pi.single i 1)) j = 0
    rw [Matrix.mulVec_mulVec, Matrix.mul_eq_one_comm.mpr hO, Matrix.one_mulVec]
    simp [hji]
  have hz := subspaceConditionalL2_directional_eq_zero O hO observed a coeff b other degree ha hb heq v hv
  have hp := fderiv_eq_zero_of_directionalLp_eq_zero b other v degree hb hz x
  rw [fderiv_chaosFunction_apply] at hp
  simpa only [v, Matrix.mulVec_single_one, Matrix.mulVec, dotProduct, Matrix.transpose_apply] using hp

end GeneralizedBulk.Entropy.Hermite
