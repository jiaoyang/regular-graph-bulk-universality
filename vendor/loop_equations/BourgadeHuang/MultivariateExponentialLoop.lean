import BourgadeHuang.ExponentialLoop

/-!
# Finite-source exponential loop equations

Multilinearity of the finite loop polynomials is proved by differentiating the
finite product-of-sums identity. This lets the exact hierarchy test every finite
linear combination of resolvents, and yields its full exponential generating equation.
-/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- Expanding a power of a finite linear combination into words. -/
theorem power_sum_words (n m : ℕ) (c X : Fin m → ℂ) :
    (∑ i, c i * X i) ^ n =
      ∑ f : Fin n → Fin m, (∏ a, c (f a)) * ∏ a, X (f a) := by
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.piFinset_univ, Finset.prod_mul_distrib] using
    Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin m)))
      (fun _ i => c i * X i)

/-- The derivative of the word expansion gives the corresponding interaction
expansion, including every coincident parameter. -/
theorem derivative_power_sum_words (n m : ℕ) (c X J : Fin m → ℂ) :
    (n : ℂ) * (∑ i, J i * c i) * (∑ i, c i * X i) ^ (n - 1) =
      ∑ f : Fin n → Fin m, (∏ a, c (f a)) *
        ∑ a, J (f a) * excludedProduct (fun b => X (f b)) a := by
  have heq : (fun z : ℂ => (∑ i, c i * (X i + z * J i)) ^ n) =
      (fun z : ℂ => ∑ f : Fin n → Fin m, (∏ a, c (f a)) * ∏ a, (X (f a) + z * J (f a))) := by
    funext z
    exact power_sum_words n m c (fun i => X i + z * J i)
  have hleft : HasDerivAt (fun z : ℂ => (∑ i, c i * (X i + z * J i)) ^ n)
      ((n : ℂ) * (∑ i, c i * X i) ^ (n - 1) * ∑ i, c i * J i) 0 := by
    have hh := (HasDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
      ((hasDerivAt_const 0 (X i)).add ((hasDerivAt_id 0).mul_const (J i))).const_mul (c i))).pow n
    simpa only [id_eq, zero_mul, add_zero, zero_add, one_mul] using hh
  have hright : HasDerivAt
      (fun z : ℂ => ∑ f : Fin n → Fin m, (∏ a, c (f a)) * ∏ a, (X (f a) + z * J (f a)))
      (∑ f : Fin n → Fin m, (∏ a, c (f a)) *
        ∑ a, J (f a) * excludedProduct (fun b => X (f b)) a) 0 := by
    apply HasDerivAt.sum
    intro f _
    have hh := (HasDerivAt.finset_prod (fun a (_ : a ∈ (Finset.univ : Finset (Fin n))) =>
      (hasDerivAt_const 0 (X (f a))).add ((hasDerivAt_id 0).mul_const (J (f a))))).const_mul
        (∏ a, c (f a))
    simpa only [id_eq, zero_mul, add_zero, zero_add, one_mul, smul_eq_mul, excludedProduct,
      mul_comm (J (f _))] using hh
  rw [← heq] at hright
  convert hleft.unique hright using 1
  simp only [mul_comm (J _) (c _)]
  ring

/-- The exact finite word expansion of a loop with a linear-combination source. -/
theorem weighted_loop_words (n m : ℕ) (H : ℂ) (c X J : Fin m → ℂ) :
    (∑ f : Fin n → Fin m, (∏ a, c (f a)) *
      (H * (∏ a, X (f a)) + ∑ a, J (f a) * excludedProduct (fun b => X (f b)) a)) =
      H * (∑ i, c i * X i) ^ n +
        (n : ℂ) * (∑ i, c i * J i) * (∑ i, c i * X i) ^ (n - 1) := by
  simp only [mul_add, Finset.sum_add_distrib]
  have hhead : (∑ f : Fin n → Fin m, (∏ a, c (f a)) * (H * ∏ a, X (f a))) =
      H * ∑ f : Fin n → Fin m, (∏ a, c (f a)) * ∏ a, X (f a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    ring
  rw [hhead, ← power_sum_words, ← derivative_power_sum_words]
  congr 2
  simp only [mul_comm (J _) (c _)]

/-- Polynomial growth times the exponential norm of a linear-growth observable
is integrable under the actual exponential-square anchor bound. -/
theorem integrable_growth_norm_mul_exp_norm
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    (F X : AnchoredCountingState → ℂ) (hF : Continuous F) (hX : Continuous X)
    {d : ℕ} (hFg : AnchoredGrowth F d) (hXg : AnchoredGrowth X 1) :
    Integrable (fun s => ‖F s‖ * Real.exp ‖X s‖) ν := by
  obtain ⟨C, hC, hb⟩ := hFg
  obtain ⟨D, hD, hd⟩ := hXg
  have hi := integrable_anchor_polynomial_exp ν ha he (mul_nonneg hC (Real.exp_nonneg D)) d D
  apply hi.mono' (hF.norm.mul (Real.continuous_exp.comp hX.norm)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro s
  change ‖‖F s‖ * Real.exp ‖X s‖‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))]
  calc
    _ ≤ (C * (1 + ‖s.val.2‖) ^ d) * Real.exp (D * (1 + ‖s.val.2‖)) :=
      mul_le_mul (hb s) (Real.exp_le_exp.mpr (by simpa only [pow_one] using hd s))
        (Real.exp_nonneg _) (by positivity)
    _ = C * Real.exp D * (1 + ‖s.val.2‖) ^ d * Real.exp (D * ‖s.val.2‖) := by
      rw [mul_add, mul_one, Real.exp_add]
      ring

/-- Every finite linear combination of resolvents satisfies all polynomial
integration-by-parts identities, by the original mixed-parameter hierarchy. -/
theorem exactHierarchy_linearCombination_monomial
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {m : ℕ} {w : ℂ} {v : Fin m → ℂ} (hw : w.im ≠ 0) (hv : ∀ i, (v i).im ≠ 0)
    (c : Fin m → ℂ) (n : ℕ) :
    let X := fun s : AnchoredCountingState => ∑ i, c i * anchoredNevanlinna s (v i)
    let J := fun s : AnchoredCountingState => ∑ i, c i * ((2 / β.value) * anchoredInteraction s w (v i))
    Integrable (fun s => anchoredLoopHead β s w * X s ^ n + (n : ℂ) * J s * X s ^ (n - 1)) ν ∧
      (∫ s, anchoredLoopHead β s w * X s ^ n + (n : ℂ) * J s * X s ^ (n - 1) ∂ν) = 0 := by
  let Q (f : Fin n → Fin m) (s : AnchoredCountingState) :=
    (∏ a, c (f a)) * anchoredLoopIntegrand β s w (fun a => v (f a))
  have hQ (f : Fin n → Fin m) : Integrable (Q f) ν ∧ (∫ s, Q f s ∂ν) = 0 := by
    obtain ⟨hi, hz⟩ := hh n w hw (fun a => v (f a)) (fun a => hv (f a))
    exact ⟨hi.const_mul _, by rw [integral_const_mul, hz, mul_zero]⟩
  have heq (s : AnchoredCountingState) : (∑ f : Fin n → Fin m, Q f s) =
      anchoredLoopHead β s w * (∑ i, c i * anchoredNevanlinna s (v i)) ^ n +
        (n : ℂ) * (∑ i, c i * ((2 / β.value) * anchoredInteraction s w (v i))) *
          (∑ i, c i * anchoredNevanlinna s (v i)) ^ (n - 1) := by
    have hpoint := weighted_loop_words n m (anchoredLoopHead β s w) c
      (fun i => anchoredNevanlinna s (v i)) (fun i => (2 / β.value) * anchoredInteraction s w (v i))
    convert hpoint using 1
    apply Finset.sum_congr rfl
    intro f _
    dsimp [Q, anchoredLoopIntegrand, anchoredLoopHead]
    rw [Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    ring
  constructor
  · simpa only [heq] using integrable_finset_sum Finset.univ (fun f _ => (hQ f).1)
  · calc
      _ = ∫ s, ∑ f : Fin n → Fin m, Q f s ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall (fun s => (heq s).symm))
      _ = 0 := by
        rw [integral_finset_sum _ (fun f _ => (hQ f).1)]
        simp only [(hQ _).2, Finset.sum_const_zero]


/-- The full finite-source exponential generating equation. Repetitions among
the spectral parameters and mixed upper/lower half-planes are unrestricted. -/
theorem multivariate_exponential_tilted_loop_identity
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    {m : ℕ} {w : ℂ} {v : Fin m → ℂ} (hw : w.im ≠ 0) (hv : ∀ i, (v i).im ≠ 0)
    (c : Fin m → ℂ) :
    let X := fun s : AnchoredCountingState => ∑ i, c i * anchoredNevanlinna s (v i)
    let J := fun s : AnchoredCountingState => ∑ i, c i * ((2 / β.value) * anchoredInteraction s w (v i))
    Integrable (fun s => (anchoredLoopHead β s w + J s) * Complex.exp (X s)) ν ∧
      (∫ s, (anchoredLoopHead β s w + J s) * Complex.exp (X s) ∂ν) = 0 := by
  let H := fun s : AnchoredCountingState => anchoredLoopHead β s w
  let X := fun s : AnchoredCountingState => ∑ i, c i * anchoredNevanlinna s (v i)
  let J := fun s : AnchoredCountingState => ∑ i, c i * ((2 / β.value) * anchoredInteraction s w (v i))
  have hH : Continuous H := continuous_anchoredLoopHead β hw
  have hX : Continuous X := continuous_finset_sum _ (fun i _ =>
    continuous_const.mul (continuous_anchoredNevanlinna (hv i)))
  have hJ : Continuous J := continuous_finset_sum _ (fun i _ =>
    continuous_const.mul (continuous_const.mul (continuous_anchoredInteraction hw (hv i))))
  have hXg : AnchoredGrowth X 1 := AnchoredGrowth.finset_sum _ _ (fun i _ =>
    AnchoredGrowth.const_mul _ (anchoredGrowth_nevanlinna (hv i)))
  have hJg : AnchoredGrowth J 1 := AnchoredGrowth.finset_sum _ _ (fun i _ =>
    AnchoredGrowth.const_mul _ (AnchoredGrowth.const_mul _ (anchoredGrowth_interaction hw (hv i))))
  have hdom := (integrable_growth_norm_mul_exp_norm ν ha he H X hH hX (anchoredGrowth_loopHead β hw) hXg).add
    (integrable_growth_norm_mul_exp_norm ν ha he J X hJ hX hJg hXg)
  have hres := integral_exponential_identity_of_monomials ν H X J 1 hH.aestronglyMeasurable
    hX.aestronglyMeasurable hJ.aestronglyMeasurable
    (fun n => exactHierarchy_linearCombination_monomial ν β hh hw hv c n)
    (by simpa only [norm_one, one_mul, add_mul] using hdom)
  simpa only [one_mul] using hres

end BourgadeHuang
