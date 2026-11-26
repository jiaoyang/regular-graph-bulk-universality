import GeneralizedBulk.Entropy.CoordinateJets
import GeneralizedBulk.Entropy.GaussianAveraging

/-! Vanishing transverse top derivatives force actual Gaussian-coordinate support. -/
noncomputable section
open scoped BigOperators Topology ContDiff

namespace GeneralizedBulk.Entropy.Hermite
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
variable (observed : Finset I) (a : K → I → ℕ) (ha : Function.Injective a) (coeff : K → ℝ)
variable (degree : ℕ) (hdegree : ∀ k, ∑ j, a k j = degree + 1)
variable (hzero : ∀ i ∉ observed, ∀ x, ∀ m : Fin degree → (I → ℝ),
  iteratedFDeriv ℝ (degree + 1) (chaosFunction a coeff) x (Fin.snoc m (Pi.single i 1)) = 0)

include ha hdegree hzero in
theorem coeff_eq_zero_of_unobserved_exponent (i : I) (hi : i ∉ observed)
    (k : K) (hai : 0 < a k i) : coeff k = 0 := by
  have hgdegree (k : {k : K // 0 < a k i}) :
      ∑ j, positiveLowerFamily a i k j = degree := by
    simpa only [Nat.add_sub_cancel] using positiveLowerFamily_degree a (degree + 1) hdegree i k
  have hgzero : ∀ x, ∀ m : Fin degree → (I → ℝ),
      iteratedFDeriv ℝ degree
        (chaosFunction (positiveLowerFamily a i) (positiveLowerCoeff a coeff i)) x m = 0 := by
    intro x m
    rw [← coordinateDerivative_chaosFunction a coeff i,
      iteratedFDeriv_coordinateDerivative degree _ (contDiff_chaosFunction a coeff) i x m]
    exact hzero i hi x m
  have hlp := chaosLp_eq_zero_of_iteratedFDeriv_zero (positiveLowerFamily a i)
    (positiveLowerFamily_injective a ha i) (positiveLowerCoeff a coeff i)
    degree degree hgdegree le_rfl hgzero
  have hc := chaosCoeff_eq_zero_of_chaosLp_eq_zero (positiveLowerFamily a i)
    (positiveLowerFamily_injective a ha i) (positiveLowerCoeff a coeff i) hlp ⟨k, hai⟩
  change coeff k * (a k i : ℝ) = 0 at hc
  exact (mul_eq_zero.mp hc).resolve_right (by exact_mod_cast ne_of_gt hai)

include ha hdegree hzero in
theorem coeff_eq_zero_of_not_supported (k : K) (hk : ¬supportedOn observed (a k)) : coeff k = 0 := by
  unfold supportedOn at hk
  push_neg at hk
  obtain ⟨i, hi, hai⟩ := hk
  exact coeff_eq_zero_of_unobserved_exponent observed a ha coeff degree hdegree hzero
    i hi k (Nat.pos_of_ne_zero hai)

include ha hdegree hzero in
/-- The full polynomial, including its lower Hermite terms, depends only on
the retained coordinates. This conclusion is proved from the top tensor. -/
theorem chaosFunction_eq_of_eq_on_observed (x y : I → ℝ)
    (hxy : ∀ i ∈ observed, x i = y i) : chaosFunction a coeff x = chaosFunction a coeff y := by
  classical
  unfold chaosFunction
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hs : supportedOn observed (a k)
  · congr 1
    unfold multiHermite
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hio : i ∈ observed
    · rw [hxy i hio]
    · rw [hs i hio]
      simp [hermite]
  · rw [coeff_eq_zero_of_not_supported observed a ha coeff degree hdegree hzero k hs]
    simp only [zero_mul]

include ha hdegree hzero in
theorem coordinateAverage_eq_self_of_top_tensor_zero (x : I → ℝ) :
    coordinateAverage observed (chaosFunction a coeff) x = chaosFunction a coeff x := by
  classical
  rw [coordinateAverage_chaosFunction]
  unfold chaosFunction
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hs : supportedOn observed (a k)
  · simp only [hs, ↓reduceIte]
  · simp only [hs, ↓reduceIte,
      coeff_eq_zero_of_not_supported observed a ha coeff degree hdegree hzero k hs, zero_mul]

include ha hdegree hzero in
theorem projectedChaosLp_eq_self_of_top_tensor_zero :
    projectedChaosLp observed a coeff = chaosLp a coeff := by
  classical
  unfold projectedChaosLp
  congr 1
  funext k
  by_cases hs : supportedOn observed (a k)
  · simp only [hs, ↓reduceIte]
  · simp only [hs, ↓reduceIte,
      coeff_eq_zero_of_not_supported observed a ha coeff degree hdegree hzero k hs]

end GeneralizedBulk.Entropy.Hermite
