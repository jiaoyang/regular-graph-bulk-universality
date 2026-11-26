import GeneralizedBulk.Entropy.GaussianDerivativeChannels

/-! An actual Gaussian polynomial is fixed by an observation exactly when its
discarded polynomial derivatives vanish. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]

@[simp] theorem directionalLp_single (a : K → I → ℕ) (coeff : K → ℝ) (i : I) :
    directionalLp a coeff (Pi.single i 1) = chaosDerivativeLp a coeff i := by
  classical
  simp [directionalLp, Pi.single_apply, Finset.sum_ite_eq']

/-- Derivative vanishing removes every Hermite coefficient using a discarded
coordinate, via the proved actual Gaussian factorial energy. -/
theorem coeff_zero_of_derivative_zero (a : K → I → ℕ) (ha : Function.Injective a)
    (coeff : K → ℝ) (i : I) (hzero : chaosDerivativeLp a coeff i = 0)
    (k : K) (hai : 0 < a k i) : coeff k = 0 := by
  classical
  have hs := chaosDerivativeLp_norm_sq a ha coeff i
  rw [hzero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
  have hterm := Finset.single_le_sum (s := Finset.univ)
    (f := fun l => coeff l ^ 2 * (a l i : ℝ) * multiFactorial I (a l))
    (fun l _ => mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (multiFactorial_pos I _).le)
    (Finset.mem_univ k)
  have hz : coeff k ^ 2 * (a k i : ℝ) * multiFactorial I (a k) = 0 := by
    apply le_antisymm
    · exact hterm.trans_eq hs.symm
    · exact mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (multiFactorial_pos I _).le
  have hsq := (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (ne_of_gt (multiFactorial_pos I _)))).resolve_right
    (by exact_mod_cast ne_of_gt hai)
  exact pow_eq_zero hsq

theorem projectedChaosLp_eq_self_of_derivatives_zero (observed : Finset I)
    (a : K → I → ℕ) (ha : Function.Injective a) (coeff : K → ℝ)
    (hzero : ∀ i, i ∉ observed → chaosDerivativeLp a coeff i = 0) :
    projectedChaosLp observed a coeff = chaosLp a coeff := by
  classical
  unfold projectedChaosLp
  congr 1
  funext k
  by_cases hs : supportedOn observed (a k)
  · simp only [hs, ↓reduceIte]
  · simp only [hs, ↓reduceIte]
    unfold supportedOn at hs
    push_neg at hs
    obtain ⟨i, hi, hai⟩ := hs
    exact (coeff_zero_of_derivative_zero a ha coeff i (hzero i hi) k (Nat.pos_of_ne_zero hai)).symm

/-- The actual rotated conditional expectation fixes a polynomial if every
actual directional derivative orthogonal to the observation vanishes. -/
theorem subspaceConditionalL2_eq_self_of_discarded_derivatives_zero
    (O : Matrix I I ℝ) (hO : O * O.transpose = 1) (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (degree : ℕ) (ha : ∀ k, (∑ i, a k i) ≤ degree)
    (hzero : ∀ v : I → ℝ, (∀ i, i ∈ observed → O.transpose.mulVec v i = 0) → directionalLp a coeff v = 0) :
    subspaceConditionalL2 O hO observed (chaosLp a coeff) = chaosLp a coeff := by
  classical
  have hrot := gaussianPullback_mem_lpFiltration O hO degree (chaosLp_mem_lpFiltration I a coeff degree ha)
  obtain ⟨g, hg⟩ := exists_lpFiltration_coefficients I hrot
  have hderiv (i : I) (hi : i ∉ observed) : chaosDerivativeLp (atMostIndexNat I) g i = 0 := by
    let v : I → ℝ := O.mulVec (Pi.single i 1)
    have hv : ∀ j, j ∈ observed → O.transpose.mulVec v j = 0 := by
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      change O.transpose.mulVec (O.mulVec (Pi.single i 1)) j = 0
      rw [Matrix.mulVec_mulVec, Matrix.mul_eq_one_comm.mpr hO, Matrix.one_mulVec]
      simp [hji]
    have hz := hzero v hv
    have hh := directionalLp_pullback a coeff (atMostIndexNat I) g O hO degree ha
      (atMostIndexNat_degree I) hg (Pi.single i 1)
    rw [directionalLp_single, hz, map_zero] at hh
    exact hh
  have hfix := projectedChaosLp_eq_self_of_derivatives_zero observed (atMostIndexNat I)
    (atMostIndexNat_injective I degree) g hderiv
  apply (gaussianPullback O hO).injective
  rw [subspaceConditionalL2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, gaussianPullback_transpose_inverse]
  change coordinateConditionalL2 observed (gaussianPullback O hO (chaosLp a coeff)) = _
  rw [← hg, coordinateConditionalL2_chaosLp, hfix]


/-- A literal polynomial invariant under a linear projection has zero actual
L² derivative in its kernel. -/
theorem directionalLp_eq_zero_of_linear_invariance (a : K → I → ℕ) (coeff : K → ℝ)
    (P : (I → ℝ) →L[ℝ] (I → ℝ))
    (hinv : ∀ x, chaosFunction a coeff (P x) = chaosFunction a coeff x)
    (v : I → ℝ) (hv : P v = 0) : directionalLp a coeff v = 0 := by
  have hf : Differentiable ℝ (chaosFunction a coeff) :=
    (contDiff_chaosFunction a coeff).differentiable (by simp)
  have hfun : chaosFunction a coeff ∘ P = chaosFunction a coeff := funext hinv
  have hz (x : I → ℝ) : fderiv ℝ (chaosFunction a coeff) x v = 0 := by
    have hh := ((hf (P x)).hasFDerivAt).comp x P.hasFDerivAt
    rw [hfun] at hh
    rw [hh.fderiv, ContinuousLinearMap.comp_apply, hv, map_zero]
  apply Lp.ext
  filter_upwards [directionalLp_ae_fderiv a coeff v, Lp.coeFn_zero ℝ 2 (standardGaussian I)] with x hx h0
  rw [hx, h0, hz]
  rfl

end GeneralizedBulk.Entropy.Hermite
