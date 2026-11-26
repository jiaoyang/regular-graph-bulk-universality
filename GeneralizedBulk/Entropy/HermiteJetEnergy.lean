import GeneralizedBulk.Entropy.HermiteDerivatives

/-! Repeated derivative energy and injectivity for actual finite Gaussian chaoses. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {K : Type*} [Fintype K]

def positiveLowerFamily (a : K → I → ℕ) (i : I) :
    {k : K // 0 < a k i} → I → ℕ := fun k => lower (a k) i

def positiveLowerCoeff (a : K → I → ℕ) (coeff : K → ℝ) (i : I) :
    {k : K // 0 < a k i} → ℝ := fun k => coeff k * (a k i : ℝ)

omit [Fintype I] [Fintype K] in
theorem positiveLowerFamily_injective (a : K → I → ℕ) (ha : Function.Injective a) (i : I) :
    Function.Injective (positiveLowerFamily a i) := by
  intro k l h
  exact Subtype.ext (ha (lower_injective_positive i k.property l.property h))

theorem sum_lower_add_one (a : I → ℕ) (i : I) (hai : 0 < a i) :
    (∑ j, lower a i j) + 1 = ∑ j, a j := by
  have hp (j : I) : lower a i j + (if j = i then 1 else 0) = a j := by
    by_cases hji : j = i
    · subst j; simp only [lower, Function.update_self, ↓reduceIte]; omega
    · simp [lower, hji]
  have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j hj => hp j)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using hh

omit [Fintype K] in
theorem positiveLowerFamily_degree (a : K → I → ℕ) (degree : ℕ)
    (hdegree : ∀ k, ∑ j, a k j = degree) (i : I) (k : {k : K // 0 < a k i}) :
    (∑ j, positiveLowerFamily a i k j) = degree - 1 := by
  have h := sum_lower_add_one (a k) i k.property
  rw [hdegree k] at h
  exact Nat.eq_sub_of_add_eq h

/-- A derivative is again an actual finite homogeneous Gaussian chaos. Terms
whose lowering coefficient is zero are removed, restoring injective indices. -/
theorem chaosDerivativeLp_eq_positiveLower (a : K → I → ℕ) (coeff : K → ℝ) (i : I) :
    chaosDerivativeLp a coeff i = chaosLp (positiveLowerFamily a i) (positiveLowerCoeff a coeff i) := by
  classical
  unfold chaosDerivativeLp
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => 0 < a k i)
    (fun k => coeff k • derivativeLp (a k) i)]
  have hz : (∑ k : {k : K // ¬0 < a k i}, coeff k • derivativeLp (a k) i) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hai : a k i = 0 := Nat.eq_zero_of_not_pos k.property
    simp [derivativeLp, hai]
  rw [hz, add_zero]
  unfold chaosLp
  apply Finset.sum_congr rfl
  intro k hk
  simp only [positiveLowerCoeff, positiveLowerFamily, derivativeLp, smul_smul]

theorem chaosDerivativeFunction_eq_positiveLower (a : K → I → ℕ) (coeff : K → ℝ)
    (i : I) (x : I → ℝ) :
    chaosDerivativeFunction a coeff i x =
      chaosFunction (positiveLowerFamily a i) (positiveLowerCoeff a coeff i) x := by
  classical
  unfold chaosDerivativeFunction
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => 0 < a k i)
    (fun k => coeff k * (a k i : ℝ) * multiHermite I (lower (a k) i) x)]
  have hz : (∑ k : {k : K // ¬0 < a k i},
      coeff k * (a k i : ℝ) * multiHermite I (lower (a k) i) x) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hai : a k i = 0 := Nat.eq_zero_of_not_pos k.property
    simp [hai]
  rw [hz, add_zero]
  rfl

theorem hasDerivAt_positiveLower_chaos (a : K → I → ℕ) (coeff : K → ℝ)
    (i : I) (x : I → ℝ) :
    HasDerivAt (fun t : ℝ => chaosFunction a coeff (Function.update x i (x i + t)))
      (chaosFunction (positiveLowerFamily a i) (positiveLowerCoeff a coeff i) x) 0 := by
  simpa only [chaosDerivativeFunction_eq_positiveLower] using
    hasDerivAt_chaosFunction_coordinate a coeff i x

/-- The sum of squared norms of the actual iterated derivatives. Recursion
uses the explicit positive-index lowering above, rather than formal symbols. -/
def chaosJetEnergy (r : ℕ) {K : Type*} [Fintype K]
    (a : K → I → ℕ) (coeff : K → ℝ) : ℝ := by
  classical
  exact match r with
  | 0 => ‖chaosLp a coeff‖ ^ 2
  | r + 1 => ∑ i : I, chaosJetEnergy r (positiveLowerFamily a i) (positiveLowerCoeff a coeff i)
termination_by r

theorem descFactorial_peel (degree r : ℕ) :
    degree.descFactorial (r + 1) = degree * (degree - 1).descFactorial r := by
  cases degree with
  | zero => simp [Nat.zero_descFactorial_succ]
  | succ n => simpa only [Nat.add_sub_cancel] using Nat.succ_descFactorial_succ n r

/-- Exact all-order Gaussian derivative energy. In particular a degree-j
chaos is determined by its j-th derivative, with factor j!. -/
theorem chaosJetEnergy_eq (r : ℕ) {K : Type*} [Fintype K]
    (a : K → I → ℕ) (ha : Function.Injective a) (coeff : K → ℝ)
    (degree : ℕ) (hdegree : ∀ k, ∑ j, a k j = degree) :
    chaosJetEnergy r a coeff = (degree.descFactorial r : ℝ) * ‖chaosLp a coeff‖ ^ 2 := by
  induction r generalizing K degree with
  | zero => simp [chaosJetEnergy]
  | succ r ih =>
    classical
    simp only [chaosJetEnergy]
    simp_rw [ih _ (positiveLowerFamily_injective a ha _) _ (degree - 1)
      (positiveLowerFamily_degree a degree hdegree _)]
    simp_rw [← chaosDerivativeLp_eq_positiveLower]
    rw [← Finset.mul_sum, chaos_derivative_energy a ha coeff degree hdegree,
      descFactorial_peel, Nat.cast_mul]
    ring

theorem chaosJetEnergy_nonneg (r : ℕ) {K : Type*} [Fintype K]
    (a : K → I → ℕ) (coeff : K → ℝ) : 0 ≤ chaosJetEnergy r a coeff := by
  induction r generalizing K with
  | zero => simp only [chaosJetEnergy]; exact sq_nonneg _
  | succ r ih =>
    classical
    simp only [chaosJetEnergy]
    exact Finset.sum_nonneg (fun i _ => ih (positiveLowerFamily a i) (positiveLowerCoeff a coeff i))

/-- No leading-monomial hypothesis is needed for derivative injectivity:
the proved Gaussian energy identity supplies it at every finite order. -/
theorem chaosLp_eq_zero_of_jetEnergy_zero (r : ℕ) {K : Type*} [Fintype K]
    (a : K → I → ℕ) (ha : Function.Injective a) (coeff : K → ℝ)
    (degree : ℕ) (hdegree : ∀ k, ∑ j, a k j = degree)
    (hr : r ≤ degree) (hzero : chaosJetEnergy r a coeff = 0) : chaosLp a coeff = 0 := by
  rw [chaosJetEnergy_eq r a ha coeff degree hdegree] at hzero
  have hn : degree.descFactorial r ≠ 0 := by
    intro h
    exact Nat.not_lt_of_ge hr (Nat.descFactorial_eq_zero_iff_lt.mp h)
  have hnR : (degree.descFactorial r : ℝ) ≠ 0 := by exact_mod_cast hn
  have hsq := (mul_eq_zero.mp hzero).resolve_left hnR
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (chaosLp a coeff)]

theorem chaosJetEnergy_top (a : K → I → ℕ) (ha : Function.Injective a) (coeff : K → ℝ)
    (degree : ℕ) (hdegree : ∀ k, ∑ j, a k j = degree) :
    chaosJetEnergy degree a coeff = (degree.factorial : ℝ) * ‖chaosLp a coeff‖ ^ 2 := by
  simpa only [Nat.descFactorial_self] using chaosJetEnergy_eq degree a ha coeff degree hdegree

def coordinateDerivative (f : (I → ℝ) → ℝ) (i : I) (x : I → ℝ) : ℝ :=
  deriv (fun t : ℝ => f (Function.update x i (x i + t))) 0

def iteratedCoordinateDerivative (indices : List I) (f : (I → ℝ) → ℝ) : (I → ℝ) → ℝ :=
  match indices with
  | [] => f
  | i :: tail => iteratedCoordinateDerivative tail (coordinateDerivative f i)

theorem coordinateDerivative_chaosFunction (a : K → I → ℕ) (coeff : K → ℝ) (i : I) :
    coordinateDerivative (chaosFunction a coeff) i =
      chaosFunction (positiveLowerFamily a i) (positiveLowerCoeff a coeff i) := by
  funext x
  exact (hasDerivAt_positiveLower_chaos a coeff i x).deriv

/-- Literal vanishing of every iterated coordinate derivative gives zero
jet energy. Every derivative in this recursion has its actual lowering proof. -/
theorem chaosJetEnergy_eq_zero_of_derivatives_zero (r : ℕ) {K : Type*} [Fintype K]
    (a : K → I → ℕ) (coeff : K → ℝ)
    (hzero : ∀ indices : List I, indices.length = r → ∀ x,
      iteratedCoordinateDerivative indices (chaosFunction a coeff) x = 0) :
    chaosJetEnergy r a coeff = 0 := by
  induction r generalizing K with
  | zero =>
    have hf : ∀ x, chaosFunction a coeff x = 0 := by
      intro x
      exact hzero [] rfl x
    have hlp : chaosLp a coeff = 0 := by
      apply Lp.ext
      filter_upwards [chaosLp_ae a coeff, Lp.coeFn_zero ℝ 2 (standardGaussian I)] with x hx hz
      rw [hx, hf x, hz]
      rfl
    simp only [chaosJetEnergy, hlp, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  | succ r ih =>
    classical
    simp only [chaosJetEnergy]
    apply Finset.sum_eq_zero
    intro i hi
    apply ih
    intro indices hlength x
    have h := hzero (i :: indices) (by simpa only [List.length_cons, hlength]) x
    simpa only [iteratedCoordinateDerivative, coordinateDerivative_chaosFunction] using h

theorem chaosLp_eq_zero_of_derivatives_zero (r : ℕ) {K : Type*} [Fintype K]
    (a : K → I → ℕ) (ha : Function.Injective a) (coeff : K → ℝ)
    (degree : ℕ) (hdegree : ∀ k, ∑ j, a k j = degree) (hr : r ≤ degree)
    (hzero : ∀ indices : List I, indices.length = r → ∀ x,
      iteratedCoordinateDerivative indices (chaosFunction a coeff) x = 0) :
    chaosLp a coeff = 0 := by
  exact chaosLp_eq_zero_of_jetEnergy_zero r a ha coeff degree hdegree hr
    (chaosJetEnergy_eq_zero_of_derivatives_zero r a coeff hzero)

omit [DecidableEq I] in
theorem chaosLp_inner_basis (a : K → I → ℕ) (ha : Function.Injective a)
    (coeff : K → ℝ) (k : K) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (chaosLp a coeff) (multiLp I (a k)) =
      coeff k * multiFactorial I (a k) := by
  classical
  simp only [chaosLp, sum_inner, inner_smul_left, starRingEnd_apply, star_trivial, multiLp_inner]
  simp_rw [ha.eq_iff]
  simp [mul_ite]

omit [DecidableEq I] in
theorem chaosCoeff_eq_zero_of_chaosLp_eq_zero (a : K → I → ℕ) (ha : Function.Injective a)
    (coeff : K → ℝ) (hzero : chaosLp a coeff = 0) (k : K) : coeff k = 0 := by
  have hh := chaosLp_inner_basis a ha coeff k
  rw [hzero, inner_zero_left] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_right (ne_of_gt (multiFactorial_pos I (a k)))

theorem chaosFunction_eq_zero_of_chaosLp_eq_zero (a : K → I → ℕ) (ha : Function.Injective a)
    (coeff : K → ℝ) (hzero : chaosLp a coeff = 0) (x : I → ℝ) :
    chaosFunction a coeff x = 0 := by
  unfold chaosFunction
  apply Finset.sum_eq_zero
  intro k hk
  have hh := chaosLp_inner_basis a ha coeff k
  rw [hzero, inner_zero_left] at hh
  have hc : coeff k = 0 := (mul_eq_zero.mp hh.symm).resolve_right (ne_of_gt (multiFactorial_pos I (a k)))
  rw [hc, zero_mul]

end GeneralizedBulk.Entropy.Hermite
