import BourgadeHuang.CMS.ExplicitFunctions
import BourgadeHuang.Integrability
import BourgadeHuang.Particles
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Finite-particle exponential observables

For β = 2, the exponential of the integrated centered resolvent is a finite
characteristic-polynomial ratio. This module constructs that actual function,
proves its numerator derivatives, and recovers every mixed resolvent product
by differentiating at the paired diagonal. These are pathwise identities;
the stochastic limiting characterization is not asserted here.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace BourgadeHuang

/-- One paired characteristic-polynomial ratio with the centering exponential. -/
def finiteCharacteristicRatio {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (u v : ℂ) : ℂ :=
  Complex.exp ((center : ℂ) * (u - v)) *
    ∏ i, ((x i : ℂ) - u) / ((x i : ℂ) - v)

/-- The finite-particle paired exponential observable. It has an entire numerator. -/
def finiteExponentialObservable {N q : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (t s : Fin q → ℂ) : ℂ :=
  ∏ j, finiteCharacteristicRatio x center (t j) (s j)

theorem finiteCharacteristicRatio_self {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) {v : ℂ} (hv : v.im ≠ 0) :
    finiteCharacteristicRatio x center v v = 1 := by
  have hne (i : Fin N) : (x i : ℂ) - v ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hv this
  simp [finiteCharacteristicRatio, hne]

theorem finiteExponentialObservable_diagonal {N q : ℕ} (x : Fin N → ℝ)
    (center : ℝ) (s : Fin q → ℂ) (hs : ∀ j, (s j).im ≠ 0) :
    finiteExponentialObservable x center s s = 1 := by
  simp only [finiteExponentialObservable, finiteCharacteristicRatio_self x center (hs _),
    Finset.prod_const_one]

/-- Exact logarithmic derivative, proved from the finite product. -/
theorem hasDerivAt_finiteCharacteristicRatio {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) (u v : ℂ) (hu : u.im ≠ 0) (hv : v.im ≠ 0) :
    HasDerivAt (fun w => finiteCharacteristicRatio x center w v)
      (-microscopicResolvent x center u * finiteCharacteristicRatio x center u v) u := by
  have hune (i : Fin N) : (x i : ℂ) - u ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hu this
  have hvne (i : Fin N) : (x i : ℂ) - v ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hv this
  have hp := CMS.hasDerivAt_finset_prod_log Finset.univ
    (fun i : Fin N => fun w : ℂ => ((x i : ℂ) - w) / ((x i : ℂ) - v))
    (fun i => -((x i : ℂ) - u)⁻¹) u (fun i _ => by
      convert ((hasDerivAt_const u (x i : ℂ)).sub (hasDerivAt_id u)).div_const
        ((x i : ℂ) - v) using 1
      field_simp [hune i, hvne i]
      <;> ring)
  have he := (((hasDerivAt_id u).sub_const v).const_mul (center : ℂ)).cexp
  convert he.mul hp using 1
  simp only [finiteCharacteristicRatio, microscopicResolvent, id_eq]
  rw [Finset.sum_neg_distrib]
  ring

/-- In each numerator coordinate, differentiation inserts the negative resolvent. -/
theorem hasDerivAt_finiteExponentialObservable_coord {N q : ℕ}
    (x : Fin N → ℝ) (center : ℝ) (t s : Fin q → ℂ) (i : Fin q)
    (hti : (t i).im ≠ 0) (hs : ∀ j, (s j).im ≠ 0) :
    HasDerivAt (fun w => finiteExponentialObservable x center (Function.update t i w) s)
      (-microscopicResolvent x center (t i) * finiteExponentialObservable x center t s)
      (t i) := by
  classical
  have h := CMS.hasDerivAt_finset_prod_log Finset.univ
    (fun j : Fin q => fun w => finiteCharacteristicRatio x center (Function.update t i w j) (s j))
    (fun j => if j = i then -microscopicResolvent x center (t i) else 0) (t i)
    (fun j _ => by
      by_cases hji : j = i
      · subst j
        simpa using hasDerivAt_finiteCharacteristicRatio x center (t i) (s i) hti (hs i)
      · simpa [Function.update_of_ne hji, hji] using
          hasDerivAt_const (t i) (finiteCharacteristicRatio x center (t j) (s j)))
  simpa [finiteExponentialObservable, Function.update_eq_self] using h

/-- Genuine iterated partial derivative, taking each numerator coordinate once.
The recursion explicitly uses mathlib's complex derivative of the coordinate slice. -/
def mixedNumeratorDerivative : {q : ℕ} → ((Fin q → ℂ) → ℂ) → (Fin q → ℂ) → ℂ
  | 0, f, z => f z
  | q + 1, f, z => deriv (fun w =>
      mixedNumeratorDerivative (fun y : Fin q → ℂ => f (Fin.cons w y)) (Fin.tail z)) (z 0)

/-- Separated variables have the expected mixed derivative. -/
theorem mixedNumeratorDerivative_product {q : ℕ} (c : ℂ)
    (f : Fin q → ℂ → ℂ) (z : Fin q → ℂ) (df : Fin q → ℂ)
    (hf : ∀ j, HasDerivAt (f j) (df j) (z j)) :
    mixedNumeratorDerivative (fun y => c * ∏ j, f j (y j)) z = c * ∏ j, df j := by
  induction q generalizing c with
  | zero => simp [mixedNumeratorDerivative]
  | succ q ih =>
    simp only [mixedNumeratorDerivative, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have heq : (fun w => mixedNumeratorDerivative
        (fun y : Fin q → ℂ => c * (f 0 w * ∏ j, f j.succ (y j))) (Fin.tail z)) =
        (fun w => (c * f 0 w) * ∏ j : Fin q, df j.succ) := by
      funext w
      simpa only [mul_assoc] using ih (c * f 0 w) (fun j => f j.succ) (Fin.tail z)
        (fun j => df j.succ) (fun j => hf j.succ)
    rw [heq]
    rw [(((hf 0).const_mul c).mul_const (∏ j : Fin q, df j.succ)).deriv]
    ring

/-- Differentiating every numerator and then pairing variables recovers all
resolvent products, including repeated parameters and both half-planes. -/
theorem mixedNumeratorDerivative_finiteExponentialObservable_diagonal {N q : ℕ}
    (x : Fin N → ℝ) (center : ℝ) (s : Fin q → ℂ) (hs : ∀ j, (s j).im ≠ 0) :
    mixedNumeratorDerivative (fun t => finiteExponentialObservable x center t s) s =
      (-1 : ℂ) ^ q * ∏ j, microscopicResolvent x center (s j) := by
  have h := mixedNumeratorDerivative_product (1 : ℂ)
    (fun j => fun u => finiteCharacteristicRatio x center u (s j)) s
    (fun j => -microscopicResolvent x center (s j)) (fun j => by
      simpa only [finiteCharacteristicRatio_self x center (hs j), mul_one] using
        hasDerivAt_finiteCharacteristicRatio x center (s j) (s j) (hs j) (hs j))
  simpa only [one_mul, finiteExponentialObservable, Finset.prod_neg, Finset.card_univ,
    Fintype.card_fin] using h

/-- The single-pair observable is entire in its numerator variable. -/
theorem analyticAt_finiteCharacteristicRatio {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) (u v : ℂ) :
    AnalyticAt ℂ (fun w => finiteCharacteristicRatio x center w v) u := by
  unfold finiteCharacteristicRatio
  apply AnalyticAt.mul
  · exact (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).cexp'
  · apply Finset.analyticAt_prod
    intro i _
    simp only [div_eq_mul_inv]
    exact (analyticAt_const.sub analyticAt_id).mul analyticAt_const

/-- The paired numerator observable is genuinely entire, including real points
and collisions among numerator variables. -/
theorem analyticAt_finiteExponentialObservable {N q : ℕ}
    (x : Fin N → ℝ) (center : ℝ) (t s : Fin q → ℂ) :
    AnalyticAt ℂ (fun u => finiteExponentialObservable x center u s) t := by
  apply Finset.analyticAt_prod
  intro j _
  exact (analyticAt_finiteCharacteristicRatio x center (t j) (s j)).comp
    (f := fun z : Fin q → ℂ => z j) (CMS.analyticAt_coord t j)

/-- A characteristic-ratio factor is bounded uniformly over its real particle. -/
theorem norm_characteristicRatio_factor_le (a : ℝ) (u v : ℂ) (hv : v.im ≠ 0) :
    ‖((a : ℂ) - u) / ((a : ℂ) - v)‖ ≤ 1 + ‖u - v‖ / |v.im| := by
  have hvne : (a : ℂ) - v ≠ 0 := by
    intro h
    apply hv
    have hi := congrArg Complex.im h
    simpa using hi
  have he : ((a : ℂ) - u) / ((a : ℂ) - v) =
      1 - (u - v) * ((a : ℂ) - v)⁻¹ := by
    field_simp [hvne]
    <;> ring
  rw [he]
  calc
    ‖1 - (u - v) * ((a : ℂ) - v)⁻¹‖ ≤
        ‖(1 : ℂ)‖ + ‖(u - v) * ((a : ℂ) - v)⁻¹‖ := norm_sub_le _ _
    _ = 1 + ‖u - v‖ * ‖((a : ℂ) - v)⁻¹‖ := by rw [norm_one, norm_mul]
    _ ≤ 1 + ‖u - v‖ * (1 / |v.im|) := by
      gcongr
      exact norm_reciprocal_le_im a hv
    _ = 1 + ‖u - v‖ / |v.im| := by ring

/-- A deterministic bound proves genuine finite-N expectation integrability. -/
theorem norm_finiteCharacteristicRatio_le {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) (u v : ℂ) (hv : v.im ≠ 0) :
    ‖finiteCharacteristicRatio x center u v‖ ≤
      ‖Complex.exp ((center : ℂ) * (u - v))‖ *
        (1 + ‖u - v‖ / |v.im|) ^ N := by
  rw [finiteCharacteristicRatio, norm_mul, norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    (∏ i : Fin N, ‖((x i : ℂ) - u) / ((x i : ℂ) - v)‖) ≤
        ∏ _i : Fin N, (1 + ‖u - v‖ / |v.im|) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ =>
        norm_characteristicRatio_factor_le (x i) u v hv)
    _ = _ := by simp

/-- Measurability uses the actual particle coordinates. -/
theorem measurable_finiteCharacteristicRatio {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (center : ℝ) (u v : ℂ) :
    Measurable (fun ω => finiteCharacteristicRatio (x ω) center u v) := by
  unfold finiteCharacteristicRatio
  apply Measurable.mul measurable_const
  apply Finset.measurable_prod
  intro i _
  exact ((Complex.continuous_ofReal.measurable.comp (hx i)).sub_const u).div
    ((Complex.continuous_ofReal.measurable.comp (hx i)).sub_const v)

/-- Uniform finite-N boundedness makes the single-pair observable integrable. -/
theorem integrable_finiteCharacteristicRatio {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {N : ℕ}
    (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (center : ℝ) (u v : ℂ) (hv : v.im ≠ 0) :
    Integrable (fun ω => finiteCharacteristicRatio (x ω) center u v) μ := by
  apply (integrable_const
    (‖Complex.exp ((center : ℂ) * (u - v))‖ * (1 + ‖u - v‖ / |v.im|) ^ N)).mono'
    (measurable_finiteCharacteristicRatio x hx center u v).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => norm_finiteCharacteristicRatio_le (x ω) center u v hv

/-- Joint numerator observables are measurable in the particles. -/
theorem measurable_finiteExponentialObservable {Ω : Type*} [MeasurableSpace Ω]
    {N q : ℕ} (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (center : ℝ) (t s : Fin q → ℂ) :
    Measurable (fun ω => finiteExponentialObservable (x ω) center t s) := by
  apply Finset.measurable_prod
  intro j _
  exact measurable_finiteCharacteristicRatio x hx center (t j) (s j)

/-- The finite-N exponential observable has a genuine expectation for all
numerators, including real numerators and numerator collisions. -/
theorem integrable_finiteExponentialObservable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {N q : ℕ}
    (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (center : ℝ) (t s : Fin q → ℂ) (hs : ∀ j, (s j).im ≠ 0) :
    Integrable (fun ω => finiteExponentialObservable (x ω) center t s) μ := by
  apply (integrable_const (∏ j : Fin q,
    ‖Complex.exp ((center : ℂ) * (t j - s j))‖ *
      (1 + ‖t j - s j‖ / |(s j).im|) ^ N)).mono'
    (measurable_finiteExponentialObservable x hx center t s).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [finiteExponentialObservable, norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ =>
    norm_finiteCharacteristicRatio_le (x ω) center (t j) (s j) (hs j))

/-- A uniform bound on a numerator ball; the particle positions do not appear. -/
def localCharacteristicRatioBound (N : ℕ) (center : ℝ) (u v : ℂ) (R : ℝ) : ℝ :=
  Real.exp (|center| * (R + ‖u - v‖)) * (1 + (R + ‖u - v‖) / |v.im|) ^ N

theorem norm_finiteCharacteristicRatio_le_local {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) (u v w : ℂ) (hv : v.im ≠ 0) (R : ℝ) (_hR : 0 ≤ R)
    (hw : ‖w - u‖ ≤ R) :
    ‖finiteCharacteristicRatio x center w v‖ ≤
      localCharacteristicRatioBound N center u v R := by
  have hwv : ‖w - v‖ ≤ R + ‖u - v‖ := by
    calc
      ‖w - v‖ = ‖(w - u) + (u - v)‖ := by congr 1; ring
      _ ≤ ‖w - u‖ + ‖u - v‖ := norm_add_le _ _
      _ ≤ R + ‖u - v‖ := add_le_add_right hw _
  apply (norm_finiteCharacteristicRatio_le x center w v hv).trans
  unfold localCharacteristicRatioBound
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · apply (Complex.norm_exp_le_exp_norm _).trans
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hwv (abs_nonneg center))
  · apply pow_le_pow_left₀ (by positivity)
    exact add_le_add_left (div_le_div_of_nonneg_right hwv (abs_nonneg _)) _

/-- An off-real point has a ball of half its imaginary height inside the spectral domain. -/
theorem half_imaginary_ball_bound (u w : ℂ) (hu : u.im ≠ 0)
    (hw : w ∈ Metric.ball u (|u.im| / 2)) :
    |u.im| / 2 ≤ |w.im| ∧ w.im ≠ 0 := by
  have hdist : ‖w - u‖ < |u.im| / 2 := by simpa [dist_eq_norm] using hw
  have htri := abs_sub_abs_le_abs_sub u.im w.im
  have him := Complex.abs_im_le_norm (u - w)
  simp only [Complex.sub_im] at him
  rw [norm_sub_rev] at him
  have hy : 0 < |u.im| := abs_pos.mpr hu
  constructor
  · linarith
  · intro h
    simp only [h, abs_zero, sub_zero] at htri him
    linarith

/-- Differentiation passes through the actual finite-N expectation. A bounded
measurable weight may contain any fixed additional observable factors. -/
theorem hasDerivAt_integral_weighted_finiteCharacteristicRatio
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {N : ℕ} (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (center : ℝ) (u v : ℂ) (hu : u.im ≠ 0) (hv : v.im ≠ 0)
    (weight : Ω → ℂ) (hm : Measurable weight) (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ ω, ‖weight ω‖ ≤ C) :
    HasDerivAt (fun w => ∫ ω, finiteCharacteristicRatio (x ω) center w v * weight ω ∂μ)
      (∫ ω, -microscopicResolvent (x ω) center u *
        finiteCharacteristicRatio (x ω) center u v * weight ω ∂μ) u := by
  let R := |u.im| / 2
  have hR : 0 < R := by dsimp [R]; positivity
  let B := localCharacteristicRatioBound N center u v R
  have hB : 0 ≤ B := by
    dsimp [B, localCharacteristicRatioBound]
    positivity
  let A := (N : ℝ) / R + |center|
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hmeas (w : ℂ) : Measurable (fun ω =>
      finiteCharacteristicRatio (x ω) center w v * weight ω) :=
    (measurable_finiteCharacteristicRatio x hx center w v).mul hm
  have hint : Integrable (fun ω => finiteCharacteristicRatio (x ω) center u v * weight ω) μ := by
    apply (integrable_const (B * C)).mono' (hmeas u).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [norm_mul]
    exact mul_le_mul (norm_finiteCharacteristicRatio_le_local (x ω) center u v u hv R
      hR.le (by simpa using hR.le)) (hbound ω) (norm_nonneg _) hB
  have hdm : AEStronglyMeasurable (fun ω => -microscopicResolvent (x ω) center u *
      finiteCharacteristicRatio (x ω) center u v * weight ω) μ :=
    (((measurable_microscopicResolvent hx center hu).neg.mul
      (measurable_finiteCharacteristicRatio x hx center u v)).mul hm).aestronglyMeasurable
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w ω => finiteCharacteristicRatio (x ω) center w v * weight ω)
    (F' := fun w ω => -microscopicResolvent (x ω) center w *
      finiteCharacteristicRatio (x ω) center w v * weight ω)
    (bound := fun _ => A * B * C) hR
    (Filter.Eventually.of_forall (fun w => (hmeas w).aestronglyMeasurable)) hint hdm
    ?_ (integrable_const _) ?_).2
  · apply Filter.Eventually.of_forall
    intro ω w hw
    have hi := half_imaginary_ball_bound u w hu hw
    have hs : ‖microscopicResolvent (x ω) center w‖ ≤ A := by
      apply (norm_microscopicResolvent_le (x ω) center hi.2).trans
      apply add_le_add_right
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hR hi.1
    have hr : ‖finiteCharacteristicRatio (x ω) center w v‖ ≤ B :=
      norm_finiteCharacteristicRatio_le_local (x ω) center u v w hv R hR.le
        (by simpa [dist_eq_norm] using (le_of_lt hw))
    rw [norm_mul, norm_mul, norm_neg]
    exact mul_le_mul (mul_le_mul hs hr (norm_nonneg _) hA) (hbound ω)
      (norm_nonneg _) (mul_nonneg hA hB)
  · apply Filter.Eventually.of_forall
    intro ω w hw
    exact (hasDerivAt_finiteCharacteristicRatio (x ω) center w v
      (half_imaginary_ball_bound u w hu hw).2 hv).mul_const (weight ω)

/-- Every fixed product of finite-N resolvents has a deterministic bound. -/
theorem norm_resolventProduct_le {N q : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (s : Fin q → ℂ) (hs : ∀ j, (s j).im ≠ 0) :
    ‖∏ j, microscopicResolvent x center (s j)‖ ≤
      ∏ j, ((N : ℝ) / |(s j).im| + |center|) := by
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ =>
    norm_microscopicResolvent_le x center (hs j))

/-- Measurability of a finite mixed-half-plane product. -/
theorem measurable_resolventProduct {Ω : Type*} [MeasurableSpace Ω]
    {N q : ℕ} (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (center : ℝ) (s : Fin q → ℂ) (hs : ∀ j, (s j).im ≠ 0) :
    Measurable (fun ω => ∏ j, microscopicResolvent (x ω) center (s j)) := by
  apply Finset.measurable_prod
  intro j _
  exact measurable_microscopicResolvent hx center (hs j)

/-- A bounded weighted product is integrable, with no distributional moments assumed. -/
theorem integrable_weighted_resolventProduct {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {N q : ℕ}
    (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (center : ℝ) (s : Fin q → ℂ) (hs : ∀ j, (s j).im ≠ 0)
    (weight : Ω → ℂ) (hm : Measurable weight) (C : ℝ)
    (hbound : ∀ ω, ‖weight ω‖ ≤ C) :
    Integrable (fun ω => (∏ j, microscopicResolvent (x ω) center (s j)) * weight ω) μ := by
  let D := ∏ j, ((N : ℝ) / |(s j).im| + |center|)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  apply (integrable_const (D * C)).mono'
    ((measurable_resolventProduct x hx center s hs).mul hm).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [norm_mul]
  exact mul_le_mul (norm_resolventProduct_le (x ω) center s hs)
    (hbound ω) (norm_nonneg _) hD

/-- Finite-N mixed derivatives can be moved through expectation in every order.
This is the actual correlation-recovery formula, prior to any limiting argument. -/
theorem mixedNumeratorDerivative_expected_finiteExponentialObservable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {N q : ℕ} (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (center : ℝ) (s : Fin q → ℂ) (hs : ∀ j, (s j).im ≠ 0)
    (weight : Ω → ℂ) (hm : Measurable weight) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ ω, ‖weight ω‖ ≤ C) :
    mixedNumeratorDerivative
      (fun t => ∫ ω, finiteExponentialObservable (x ω) center t s * weight ω ∂μ) s =
      (-1 : ℂ) ^ q * ∫ ω, (∏ j, microscopicResolvent (x ω) center (s j)) * weight ω ∂μ := by
  induction q generalizing weight C with
  | zero => simp [mixedNumeratorDerivative, finiteExponentialObservable]
  | succ q ih =>
    let st : Fin q → ℂ := fun j => s j.succ
    have hst : ∀ j, (st j).im ≠ 0 := fun j => hs j.succ
    let P : Ω → ℂ := fun ω => ∏ j : Fin q, microscopicResolvent (x ω) center (st j)
    let D := ∏ j : Fin q, ((N : ℝ) / |(st j).im| + |center|)
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hPm : Measurable P := measurable_resolventProduct x hx center st hst
    have hPb : ∀ ω, ‖P ω‖ ≤ D := fun ω => norm_resolventProduct_le (x ω) center st hst
    let W : Ω → ℂ := fun ω => ((-1 : ℂ) ^ q * P ω) * weight ω
    have hWm : Measurable W := (measurable_const.mul hPm).mul hm
    have hWb : ∀ ω, ‖W ω‖ ≤ D * C := by
      intro ω
      simp only [W, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact mul_le_mul (hPb ω) (hbound ω) (norm_nonneg _) hD
    have heq : (fun w : ℂ => mixedNumeratorDerivative
        (fun y : Fin q → ℂ => ∫ ω,
          finiteExponentialObservable (x ω) center (Fin.cons w y) s * weight ω ∂μ)
        (Fin.tail s)) =
        (fun w => ∫ ω, finiteCharacteristicRatio (x ω) center w (s 0) * W ω ∂μ) := by
      funext w
      let V : Ω → ℂ := fun ω => finiteCharacteristicRatio (x ω) center w (s 0) * weight ω
      let B := ‖Complex.exp ((center : ℂ) * (w - s 0))‖ *
        (1 + ‖w - s 0‖ / |(s 0).im|) ^ N
      have hB : 0 ≤ B := by dsimp [B]; positivity
      have hVm : Measurable V :=
        (measurable_finiteCharacteristicRatio x hx center w (s 0)).mul hm
      have hVb : ∀ ω, ‖V ω‖ ≤ B * C := by
        intro ω
        change ‖finiteCharacteristicRatio (x ω) center w (s 0) * weight ω‖ ≤ B * C
        rw [norm_mul]
        exact mul_le_mul (norm_finiteCharacteristicRatio_le (x ω) center w (s 0) (hs 0))
          (hbound ω) (norm_nonneg _) hB
      have hi := ih st hst V hVm (B * C) (mul_nonneg hB hC) hVb
      have hfn : (fun y : Fin q → ℂ => ∫ ω,
          finiteExponentialObservable (x ω) center (Fin.cons w y) s * weight ω ∂μ) =
          (fun y => ∫ ω, finiteExponentialObservable (x ω) center y st * V ω ∂μ) := by
        funext y
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro ω
        simp only [finiteExponentialObservable, Fin.prod_univ_succ, Fin.cons_zero,
          Fin.cons_succ, st, V]
        ring
      rw [hfn]
      change mixedNumeratorDerivative
        (fun y => ∫ ω, finiteExponentialObservable (x ω) center y st * V ω ∂μ) st = _
      rw [hi, ← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      dsimp [V, W, P]
      ring
    rw [mixedNumeratorDerivative, heq]
    rw [(hasDerivAt_integral_weighted_finiteCharacteristicRatio μ x hx center
      (s 0) (s 0) (hs 0) (hs 0) W hWm (D * C) (mul_nonneg hD hC) hWb).deriv]
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω
    simp only [finiteCharacteristicRatio_self (x ω) center (hs 0), mul_one,
      Fin.prod_univ_succ, pow_succ, W, P, st]
    ring

end BourgadeHuang
