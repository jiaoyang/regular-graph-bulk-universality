import GeneralizedBulk.Entropy.HermiteDerivatives

/-! Coordinate Gaussian observation channels, computed as actual averaging
integrals on the finite product Gaussian probability space. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Retain the observed coordinates and integrate every other coordinate
against a fresh independent standard Gaussian. -/
def coordinateAverage (observed : Finset I) (f : (I → ℝ) → ℝ) (x : I → ℝ) : ℝ :=
  ∫ z, f (fun i => if i ∈ observed then x i else z i) ∂standardGaussian I

def supportedOn (observed : Finset I) (a : I → ℕ) : Prop :=
  ∀ i, i ∉ observed → a i = 0

instance (observed : Finset I) (a : I → ℕ) : Decidable (supportedOn observed a) := by
  unfold supportedOn
  infer_instance

/-- Every averaging section of a Hermite polynomial is genuinely integrable. -/
theorem integrable_average_multiHermite (observed : Finset I) (a : I → ℕ) (x : I → ℝ) :
    Integrable (fun z => multiHermite I a (fun i => if i ∈ observed then x i else z i))
      (standardGaussian I) := by
  letI : MeasureSpace ℝ := ⟨GeneralizedBulk.Gaussian.standardNormal⟩
  letI : IsProbabilityMeasure (volume : Measure ℝ) :=
    (inferInstance : IsProbabilityMeasure GeneralizedBulk.Gaussian.standardNormal)
  have hf (i : I) : Integrable (fun t : ℝ => (hermite (a i)).eval (if i ∈ observed then x i else t)) := by
    by_cases hi : i ∈ observed
    · simpa only [hi, ↓reduceIte] using (integrable_const ((hermite (a i)).eval (x i)))
    · simpa only [hi, ↓reduceIte] using (integrable_polynomial (hermite (a i)))
  simpa only [multiHermite, standardGaussian, volume_pi] using Integrable.fintype_prod hf

/-- Gaussian coordinate averaging discards precisely the Hermite factors of
positive degree in an unobserved coordinate. -/
theorem coordinateAverage_multiHermite (observed : Finset I) (a : I → ℕ) (x : I → ℝ) :
    coordinateAverage observed (multiHermite I a) x =
      if supportedOn observed a then multiHermite I a x else 0 := by
  classical
  have hfub : coordinateAverage observed (multiHermite I a) x =
      ∏ i, ∫ t : ℝ, (hermite (a i)).eval (if i ∈ observed then x i else t)
        ∂GeneralizedBulk.Gaussian.standardNormal := by
    letI : MeasureSpace ℝ := ⟨GeneralizedBulk.Gaussian.standardNormal⟩
    letI : IsProbabilityMeasure (volume : Measure ℝ) :=
      (inferInstance : IsProbabilityMeasure GeneralizedBulk.Gaussian.standardNormal)
    simpa only [coordinateAverage, multiHermite, standardGaussian, volume_pi] using
      integral_fintype_prod_eq_prod I
        (fun i : I => fun t : ℝ => (hermite (a i)).eval (if i ∈ observed then x i else t))
  rw [hfub]
  by_cases ha : supportedOn observed a
  · simp only [ha, ↓reduceIte, multiHermite]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hoi : i ∈ observed
    · simp only [hoi, ↓reduceIte, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
    · simp only [hoi, ↓reduceIte, ha i hoi, hermite_zero, Polynomial.eval_one,
        integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  · simp only [ha, ↓reduceIte]
    obtain ⟨i, hi, hai⟩ : ∃ i, i ∉ observed ∧ a i ≠ 0 := by
      simpa only [supportedOn, not_forall, _root_.not_imp, exists_prop] using ha
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hi, ↓reduceIte]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hai
    rw [hn, integral_hermite_succ]

/-- Coordinate projection preserves each actual finite homogeneous Gaussian
chaos, since surviving Hermite degrees are unchanged. -/
def projectedChaosLp {K : Type*} [Fintype K] (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) : Lp ℝ 2 (standardGaussian I) := by
  classical
  exact chaosLp a (fun k => if supportedOn observed (a k) then coeff k else 0)

theorem coordinateAverage_chaosFunction {K : Type*} [Fintype K] (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (x : I → ℝ) :
    coordinateAverage observed (chaosFunction a coeff) x =
      ∑ k, if supportedOn observed (a k) then coeff k * multiHermite I (a k) x else 0 := by
  classical
  unfold coordinateAverage chaosFunction
  rw [integral_finset_sum _ (fun k _ => (integrable_average_multiHermite observed (a k) x).const_mul (coeff k))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul]
  change coeff k * coordinateAverage observed (multiHermite I (a k)) x = _
  rw [coordinateAverage_multiHermite]
  split_ifs with h <;> simp [h]

/-- The computed projected L² vector represents the actual Gaussian averaging
integral, not an abstract projection postulated to have its desired law. -/
theorem projectedChaosLp_ae {K : Type*} [Fintype K] (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) :
    (projectedChaosLp observed a coeff : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
      coordinateAverage observed (chaosFunction a coeff) := by
  classical
  filter_upwards [chaosLp_ae a (fun k => if supportedOn observed (a k) then coeff k else 0)] with x hx
  rw [coordinateAverage_chaosFunction]
  change chaosLp a (fun k => if supportedOn observed (a k) then coeff k else 0) x = _
  rw [hx]
  unfold chaosFunction
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with h <;> simp [h]

/-- The concrete Gaussian averaging channel is an L² contraction on every
finite chaos, proved from its actual factorial-normalized coefficients. -/
theorem projectedChaosLp_norm_le {K : Type*} [Fintype K] (observed : Finset I)
    (a : K → I → ℕ) (ha : Function.Injective a) (coeff : K → ℝ) :
    ‖projectedChaosLp observed a coeff‖ ≤ ‖chaosLp a coeff‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [projectedChaosLp, chaosLp_norm_sq a ha, chaosLp_norm_sq a ha]
  apply Finset.sum_le_sum
  intro k hk
  split_ifs
  · rfl
  · simpa using mul_nonneg (sq_nonneg (coeff k)) (multiFactorial_pos I (a k)).le

omit [Fintype I] in
/-- Lowering a retained coordinate does not change which unobserved Hermite
coordinates occur. This is the algebra behind derivative commutation. -/
theorem supportedOn_lower_iff (observed : Finset I) (a : I → ℕ) (i : I) (hi : i ∈ observed) :
    supportedOn observed (lower a i) ↔ supportedOn observed a := by
  constructor <;> intro h j hj
  · have hji : j ≠ i := fun heq => hj (heq ▸ hi)
    simpa only [lower, Function.update_of_ne hji] using h j hj
  · have hji : j ≠ i := fun heq => hj (heq ▸ hi)
    simpa only [lower, Function.update_of_ne hji] using h j hj

/-- Averaging a finite chaos is exactly coefficient truncation as an actual
pointwise polynomial, simultaneously at every input. -/
theorem coordinateAverage_chaosFunction_eq {K : Type*} [Fintype K] (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) :
    coordinateAverage observed (chaosFunction a coeff) =
      chaosFunction a (fun k => if supportedOn observed (a k) then coeff k else 0) := by
  classical
  funext x
  rw [coordinateAverage_chaosFunction]
  unfold chaosFunction
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with h <;> simp [h]

/-- The projected chaos has the same exact derivative-energy identity, since
Gaussian averaging has been proved to retain its Hermite degree. -/
theorem projected_chaos_derivative_energy {K : Type*} [Fintype K] (observed : Finset I)
    (a : K → I → ℕ) (ha : Function.Injective a) (coeff : K → ℝ)
    (degree : ℕ) (hdegree : ∀ k, ∑ i, a k i = degree) :
    (∑ i, ‖chaosDerivativeLp a (fun k => if supportedOn observed (a k) then coeff k else 0) i‖ ^ 2) =
      (degree : ℝ) * ‖projectedChaosLp observed a coeff‖ ^ 2 := by
  classical
  exact chaos_derivative_energy a ha _ degree hdegree

/-- Gaussian averaging commutes with each retained coordinate derivative;
this is an equality of actual polynomial Gaussian integrals. -/
theorem coordinateAverage_derivativeFunction {K : Type*} [Fintype K] (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (i : I) (hi : i ∈ observed) (x : I → ℝ) :
    coordinateAverage observed (chaosDerivativeFunction a coeff i) x =
      chaosDerivativeFunction a (fun k => if supportedOn observed (a k) then coeff k else 0) i x := by
  classical
  unfold coordinateAverage chaosDerivativeFunction
  rw [integral_finset_sum _ (fun k _ =>
    (integrable_average_multiHermite observed (lower (a k) i) x).const_mul (coeff k * (a k i : ℝ)))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul]
  change (coeff k * (a k i : ℝ)) * coordinateAverage observed (multiHermite I (lower (a k) i)) x = _
  rw [coordinateAverage_multiHermite]
  simp only [supportedOn_lower_iff observed (a k) i hi]
  split_ifs with h <;> simp [h]

/-- The commutation identity is compatible with actual differentiation,
not merely a formal lowering symbol on Hermite coefficients. -/
theorem hasDerivAt_coordinateAverage_retained {K : Type*} [Fintype K] (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (i : I) (hi : i ∈ observed) (x : I → ℝ) :
    HasDerivAt (fun t : ℝ => coordinateAverage observed (chaosFunction a coeff)
      (Function.update x i (x i + t)))
      (coordinateAverage observed (chaosDerivativeFunction a coeff i) x) 0 := by
  classical
  rw [coordinateAverage_chaosFunction_eq, coordinateAverage_derivativeFunction observed a coeff i hi x]
  exact hasDerivAt_chaosFunction_coordinate a _ i x

/-- True orthogonal-projection Pythagoras for the actual Gaussian averaging
operator on finite chaos, proved from factorial Gaussian inner products. -/
theorem projectedChaosLp_pythagoras {K : Type*} [Fintype K] (observed : Finset I)
    (a : K → I → ℕ) (ha : Function.Injective a) (coeff : K → ℝ) :
    ‖chaosLp a coeff - projectedChaosLp observed a coeff‖ ^ 2 =
      ‖chaosLp a coeff‖ ^ 2 - ‖projectedChaosLp observed a coeff‖ ^ 2 := by
  classical
  let mask := fun k => if supportedOn observed (a k) then coeff k else 0
  have hsub : chaosLp a coeff - chaosLp a mask = chaosLp a (fun k => coeff k - mask k) := by
    simp only [chaosLp, ← Finset.sum_sub_distrib, sub_smul]
  change ‖chaosLp a coeff - chaosLp a mask‖ ^ 2 = _
  rw [hsub, chaosLp_norm_sq a ha, projectedChaosLp, chaosLp_norm_sq a ha, chaosLp_norm_sq a ha]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp [mask]
  split_ifs with h <;> simp [h]

end GeneralizedBulk.Entropy.Hermite
