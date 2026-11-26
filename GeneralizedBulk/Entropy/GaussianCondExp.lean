import GeneralizedBulk.Entropy.GaussianAveraging
import GeneralizedBulk.Gaussian.IID

/-! The computed Gaussian averaging operator is the actual conditional
expectation for the retained-coordinate observation sigma algebra. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
open GeneralizedBulk.Gaussian

variable {I : Type*} [Fintype I] [DecidableEq I]

def retainedCoordinates (observed : Finset I) (x : I → ℝ) : observed → ℝ := fun i => x i

def coordinateSigma (observed : Finset I) : MeasurableSpace (I → ℝ) :=
  MeasurableSpace.comap (retainedCoordinates observed) inferInstance

omit [Fintype I] [DecidableEq I] in
theorem measurable_retainedCoordinates (observed : Finset I) : Measurable (retainedCoordinates observed) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)

omit [Fintype I] [DecidableEq I] in
theorem coordinateSigma_le (observed : Finset I) : coordinateSigma observed ≤ (inferInstance : MeasurableSpace (I → ℝ)) :=
  (measurable_retainedCoordinates observed).comap_le

omit [DecidableEq I] in
/-- The observed coordinates have their actual independent Gaussian marginal. -/
theorem retainedCoordinates_measurePreserving (observed : Finset I) :
    MeasurePreserving (retainedCoordinates observed) (standardGaussian I) (standardGaussian observed) := by
  refine ⟨measurable_retainedCoordinates observed, ?_⟩
  simpa only [iidLaw, Measure.infinitePi_eq_pi, standardGaussian, retainedCoordinates] using
    iidLaw_map_injectiveSelection standardNormal I (fun i : observed => i.val) Subtype.val_injective

def hermiteFactor (observed : Finset I) (a : I → ℕ) (x : I → ℝ) : ℝ :=
  multiHermite observed (fun i => a i) (retainedCoordinates observed x)

omit [DecidableEq I] in
theorem hermiteFactor_measurable_observed (observed : Finset I) (a : I → ℕ) :
    StronglyMeasurable[coordinateSigma observed] (hermiteFactor observed a) := by
  have hr : Measurable[coordinateSigma observed] (retainedCoordinates observed) :=
    Measurable.of_comap_le le_rfl
  exact ((continuous_multiHermite observed (fun i => a i)).measurable.comp hr).stronglyMeasurable

theorem hermiteFactor_integrable (observed : Finset I) (a : I → ℕ) :
    Integrable (hermiteFactor observed a) (standardGaussian I) :=
  ((retainedCoordinates_measurePreserving observed).integrable_comp
    (continuous_multiHermite observed (fun i => a i)).aestronglyMeasurable).2
      (integrable_multiHermite observed (fun i => a i))

/-- The retained and discarded factors are literal disjoint Gaussian products. -/
theorem multiHermite_factorization (observed : Finset I) (a : I → ℕ) (x : I → ℝ) :
    multiHermite I a x = hermiteFactor observed a x * hermiteFactor observedᶜ a x := by
  unfold hermiteFactor multiHermite retainedCoordinates
  change (∏ i : I, (hermite (a i)).eval (x i)) =
    (∏ i : observed, (hermite (a i.val)).eval (x i.val)) *
      ∏ i : (observedᶜ : Finset I), (hermite (a i.val)).eval (x i.val)
  have ho := Finset.prod_coe_sort observed (fun i : I => (hermite (a i)).eval (x i))
  have hc := Finset.prod_coe_sort observedᶜ (fun i : I => (hermite (a i)).eval (x i))
  rw [ho, hc]
  exact (Finset.prod_mul_prod_compl observed (fun i => (hermite (a i)).eval (x i))).symm

omit [DecidableEq I] in
theorem standardGaussian_eval_iIndepFun :
    iIndepFun (fun i (x : I → ℝ) => x i) (standardGaussian I) := by
  simpa only [iidLaw, Measure.infinitePi_eq_pi, standardGaussian] using iidLaw_eval_iIndepFun standardNormal I

/-- Independence of the sigma algebras is proved from the actual product law. -/
theorem coordinateSigma_indep (observed : Finset I) :
    Indep (coordinateSigma observedᶜ) (coordinateSigma observed) (standardGaussian I) := by
  exact ProbabilityTheory.iIndepFun.indepFun_finset observedᶜ observed
    (Finset.disjoint_left.mpr (fun i hi hio => by simpa using (Finset.mem_compl.mp hi) hio)) standardGaussian_eval_iIndepFun (fun i => measurable_pi_apply i)

omit [DecidableEq I] in
theorem integral_multiHermite_mean (a : I → ℕ) :
    (∫ x, multiHermite I a x ∂standardGaussian I) = if a = (fun _ => 0) then 1 else 0 := by
  classical
  have h := integral_multiHermite_pair I a (fun _ => 0)
  simp only [multiHermite, hermite_zero, Polynomial.eval_one, Finset.prod_const_one, mul_one] at h
  by_cases ha : a = fun _ => 0
  · simp [ha, multiHermite]
  · simpa only [ha, ↓reduceIte] using h

/-- A discarded positive Hermite factor has mean zero. -/
theorem integral_hermiteFactor_complement (observed : Finset I) (a : I → ℕ) :
    (∫ x, hermiteFactor observedᶜ a x ∂standardGaussian I) = if supportedOn observed a then 1 else 0 := by
  classical
  change (∫ x, multiHermite (observedᶜ : Finset I) (fun i => a i) (retainedCoordinates observedᶜ x) ∂standardGaussian I) = _
  have hmp := retainedCoordinates_measurePreserving (I := I) observedᶜ
  have hfm : AEStronglyMeasurable (multiHermite (observedᶜ : Finset I) (fun i => a i))
      (Measure.map (retainedCoordinates observedᶜ) (standardGaussian I)) := by
    rw [hmp.map_eq]
    exact (continuous_multiHermite (observedᶜ : Finset I) (fun i => a i)).aestronglyMeasurable
  have hchange := integral_map (measurable_retainedCoordinates observedᶜ).aemeasurable hfm
  rw [hmp.map_eq] at hchange
  rw [← hchange]
  rw [integral_multiHermite_mean]
  have hs : (fun i : (observedᶜ : Finset I) => a i) = (fun _ => 0) ↔ supportedOn observed a := by
    constructor
    · intro h i hi
      have hh := congrFun h ⟨i, Finset.mem_compl.mpr hi⟩
      exact hh
    · intro h
      funext i
      exact h i.val (Finset.mem_compl.mp i.property)
  simp only [hs]

/-- The actual conditional expectation equals the computed Gaussian averaging
operator on each Hermite function. -/
theorem condExp_multiHermite (observed : Finset I) (a : I → ℕ) :
    (standardGaussian I)[multiHermite I a | coordinateSigma observed] =ᵐ[standardGaussian I]
      coordinateAverage observed (multiHermite I a) := by
  classical
  have hg := condExp_indep_eq (coordinateSigma_le observedᶜ) (coordinateSigma_le observed)
    (hermiteFactor_measurable_observed observedᶜ a) (coordinateSigma_indep observed)
  have hf : Integrable (hermiteFactor observed a * hermiteFactor observedᶜ a) (standardGaussian I) := by
    convert integrable_multiHermite I a using 1
    funext x
    exact (multiHermite_factorization observed a x).symm
  have hp := condExp_mul_of_stronglyMeasurable_left (hermiteFactor_measurable_observed observed a)
    hf (hermiteFactor_integrable observedᶜ a)
  have heq : (hermiteFactor observed a * hermiteFactor observedᶜ a) = multiHermite I a := by
    funext x
    exact (multiHermite_factorization observed a x).symm
  rw [heq] at hp
  filter_upwards [hp, hg] with x hpx hgx
  rw [hpx]
  simp only [Pi.mul_apply, hgx, integral_hermiteFactor_complement, coordinateAverage_multiHermite]
  by_cases ha : supportedOn observed a
  · simp only [ha, ↓reduceIte, mul_one]
    have hc : hermiteFactor observedᶜ a x = 1 := by
      change (∏ i : (observedᶜ : Finset I), (hermite (a i.val)).eval (x i.val)) = 1
      apply Finset.prod_eq_one
      intro i hi
      have hz : a i.val = 0 := ha i.val (Finset.mem_compl.mp i.property)
      simp only [hz, hermite_zero, Polynomial.eval_one]
    simpa only [hc, mul_one] using (multiHermite_factorization observed a x).symm
  · simp [ha]

/-- Conditional expectation and actual Gaussian averaging agree on every
finite Hermite polynomial, by linearity of the genuine conditional expectation. -/
theorem condExp_chaosFunction {K : Type*} [Fintype K] (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) :
    (standardGaussian I)[chaosFunction a coeff | coordinateSigma observed] =ᵐ[standardGaussian I]
      coordinateAverage observed (chaosFunction a coeff) := by
  classical
  have hs := condExp_finset_sum (μ := standardGaussian I)
    (fun k (_ : k ∈ (Finset.univ : Finset K)) => (integrable_multiHermite I (a k)).const_mul (coeff k))
    (coordinateSigma observed)
  have hfun : (∑ k : K, (fun x : I → ℝ => coeff k * multiHermite I (a k) x)) =
      (fun x => ∑ k : K, coeff k * multiHermite I (a k) x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [hfun] at hs
  have hk (k : K) : (standardGaussian I)[(fun x => coeff k * multiHermite I (a k) x) | coordinateSigma observed]
      =ᵐ[standardGaussian I] (fun x => coeff k * coordinateAverage observed (multiHermite I (a k)) x) := by
    have hsmul := condExp_smul (μ := standardGaussian I) (coeff k) (multiHermite I (a k)) (coordinateSigma observed)
    filter_upwards [hsmul, condExp_multiHermite observed (a k)] with x hx hc
    simpa only [Pi.smul_apply, smul_eq_mul, hc] using hx
  have hall : ∀ᵐ x ∂standardGaussian I, ∀ k : K,
      (standardGaussian I)[(fun y => coeff k * multiHermite I (a k) y) | coordinateSigma observed] x =
        coeff k * coordinateAverage observed (multiHermite I (a k)) x := ae_all_iff.mpr hk
  filter_upwards [hs, hall] with x hsum hx
  change (standardGaussian I)[(fun y => ∑ k, coeff k * multiHermite I (a k) y) | coordinateSigma observed] x = _
  rw [hsum, coordinateAverage_chaosFunction]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hkmem
  rw [hx k, coordinateAverage_multiHermite]
  split_ifs with h <;> simp [h]

/-- The observation channel as an actual bounded linear orthogonal projection
on the entire Gaussian L² space. -/
def coordinateConditionalL2 (observed : Finset I) :
    Lp ℝ 2 (standardGaussian I) →L[ℝ] Lp ℝ 2 (standardGaussian I) :=
  (lpMeas ℝ ℝ (coordinateSigma observed) 2 (standardGaussian I)).subtypeL.comp
    (condExpL2 ℝ ℝ (coordinateSigma_le observed))

theorem coordinateConditionalL2_ae (observed : Finset I) (f : Lp ℝ 2 (standardGaussian I)) :
    (coordinateConditionalL2 observed f : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
      (standardGaussian I)[(f : (I → ℝ) → ℝ) | coordinateSigma observed] := by
  have h := MemLp.condExpL2_ae_eq_condExp (𝕜 := ℝ) (coordinateSigma_le observed) (Lp.memLp f)
  simpa only [Lp.toLp_coeFn] using h

/-- The genuine conditional projection has exactly the already computed
Hermite truncation formula. -/
theorem coordinateConditionalL2_chaosLp {K : Type*} [Fintype K] (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) :
    coordinateConditionalL2 observed (chaosLp a coeff) = projectedChaosLp observed a coeff := by
  apply Lp.ext
  exact (coordinateConditionalL2_ae observed (chaosLp a coeff)).trans
    ((condExp_congr_ae (chaosLp_ae a coeff)).trans
      ((condExp_chaosFunction observed a coeff).trans (projectedChaosLp_ae observed a coeff).symm))

/-- The genuine Gaussian conditional observation operator is an L² contraction. -/
theorem coordinateConditionalL2_norm_le (observed : Finset I) (f : Lp ℝ 2 (standardGaussian I)) :
    ‖coordinateConditionalL2 observed f‖ ≤ ‖f‖ :=
  norm_condExpL2_coe_le (coordinateSigma_le observed) f

/-- Conditional expectation is self-adjoint on the actual Gaussian Hilbert space. -/
theorem coordinateConditionalL2_selfAdjoint (observed : Finset I) (f g : Lp ℝ 2 (standardGaussian I)) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (coordinateConditionalL2 observed f) g =
      @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ f (coordinateConditionalL2 observed g) :=
  inner_condExpL2_left_eq_right (coordinateSigma_le observed)

end GeneralizedBulk.Entropy.Hermite
