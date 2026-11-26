import GeneralizedBulk.Gaussian.Marks

/-! # Infinite iid actual Gaussian mark vectors and their centered quadratic entries -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace GeneralizedBulk.Gaussian

def rawQuadratic (p : ℝ) (i j : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  y i * y j - covarianceMatrix p i j

@[simp] theorem rawQuadratic_mark (p : ℝ) (i j : Fin 4) (x : Fin 4 → ℝ) :
    rawQuadratic p i j (mark p x) = centeredQuadratic p i j x := rfl

theorem measurable_rawQuadratic (p : ℝ) (i j : Fin 4) : Measurable (rawQuadratic p i j) :=
  ((measurable_pi_apply i).mul (measurable_pi_apply j)).sub_const _

theorem integrable_rawQuadratic_pow (p : ℝ) (i j : Fin 4) (n : ℕ) :
    Integrable (fun y => rawQuadratic p i j y ^ n) (markLaw p) := by
  unfold markLaw
  apply (integrable_map_measure ((measurable_rawQuadratic p i j).pow_const n).aestronglyMeasurable
    (measurable_mark p).aemeasurable).2
  simpa only [Function.comp_def, rawQuadratic_mark] using integrable_centeredQuadratic_pow p i j n

theorem rawQuadratic_memLp_two (p : ℝ) (i j : Fin 4) :
    MemLp (rawQuadratic p i j) 2 (markLaw p) := by
  exact (memLp_two_iff_integrable_sq
    (measurable_rawQuadratic p i j).aestronglyMeasurable).2 (integrable_rawQuadratic_pow p i j 2)

theorem rawQuadratic_memLp_nat (p : ℝ) (i j : Fin 4) (n : ℕ) :
    MemLp (rawQuadratic p i j) (n : ℝ≥0∞) (markLaw p) := by
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero] using
      (memLp_zero_iff_aestronglyMeasurable (μ := markLaw p)).mpr
        (measurable_rawQuadratic p i j).aestronglyMeasurable
  · apply (integrable_norm_rpow_iff (p := (n : ℝ≥0∞))
      (measurable_rawQuadratic p i j).aestronglyMeasurable
      (by exact_mod_cast hn) (by simp)).mp
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, norm_pow] using
      (integrable_rawQuadratic_pow p i j n).norm

theorem rawQuadratic_mean_zero (p : ℝ) (hp : |p| < 1) (i j : Fin 4) :
    (∫ y, rawQuadratic p i j y ∂markLaw p) = 0 := by
  rw [markLaw, integral_map (measurable_mark p).aemeasurable
    (measurable_rawQuadratic p i j).aestronglyMeasurable]
  exact centeredQuadratic_mean_zero p hp i j

theorem integrable_rawQuadratic_product (p : ℝ) (i j a b : Fin 4) :
    Integrable (fun y => rawQuadratic p i j y * rawQuadratic p a b y) (markLaw p) := by
  unfold markLaw
  apply (integrable_map_measure
    ((measurable_rawQuadratic p i j).mul (measurable_rawQuadratic p a b)).aestronglyMeasurable
    (measurable_mark p).aemeasurable).2
  simpa only [Function.comp_def, rawQuadratic_mark] using integrable_centeredQuadratic_product p i j a b

theorem rawQuadratic_covariance (p : ℝ) (hp : |p| < 1) (i j a b : Fin 4) :
    (∫ y, rawQuadratic p i j y * rawQuadratic p a b y ∂markLaw p) =
      covarianceMatrix p i a * covarianceMatrix p j b +
      covarianceMatrix p i b * covarianceMatrix p j a := by
  rw [markLaw, integral_map (measurable_mark p).aemeasurable
    ((measurable_rawQuadratic p i j).mul (measurable_rawQuadratic p a b)).aestronglyMeasurable]
  exact centeredQuadratic_covariance p hp i j a b

private theorem covarianceMatrix_ofReal (p : ℝ) (i j : Fin 4) :
    ((covarianceMatrix p i j : ℝ) : ℂ) = covarianceMatrix (p : ℂ) i j := by
  rw [covarianceMatrix_eq, covarianceMatrix_eq]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

def markQuadraticFamily (p : ℝ) {I : Type*} (n : I) (i j : Fin 4)
    (ω : I → (Fin 4 → ℝ)) : ℝ := rawQuadratic p i j (ω n)

theorem measurable_markQuadraticFamily (p : ℝ) {I : Type*} (n : I) (i j : Fin 4) :
    Measurable (markQuadraticFamily p n i j) :=
  (measurable_rawQuadratic p i j).comp (measurable_pi_apply n)

theorem markQuadraticFamily_memLp_two (p : ℝ) {I : Type*} (n : I) (i j : Fin 4) :
    MemLp (markQuadraticFamily p n i j) 2 (iidLaw (markLaw p) I) :=
  (rawQuadratic_memLp_two p i j).comp_measurePreserving
    (iidLaw_eval_measurePreserving (markLaw p) I n)

theorem markQuadraticFamily_memLp_nat (p : ℝ) {I : Type*} (n : I) (i j : Fin 4) (q : ℕ) :
    MemLp (markQuadraticFamily p n i j) (q : ℝ≥0∞) (iidLaw (markLaw p) I) :=
  (rawQuadratic_memLp_nat p i j q).comp_measurePreserving
    (iidLaw_eval_measurePreserving (markLaw p) I n)

theorem integrable_markQuadraticFamily_pow (p : ℝ) {I : Type*} (n : I) (i j : Fin 4) (q : ℕ) :
    Integrable (fun ω => markQuadraticFamily p n i j ω ^ q) (iidLaw (markLaw p) I) := by
  exact ((iidLaw_eval_measurePreserving (markLaw p) I n).integrable_comp
    (integrable_rawQuadratic_pow p i j q).aestronglyMeasurable).2
      (integrable_rawQuadratic_pow p i j q)

theorem markQuadraticFamily_mean_zero (p : ℝ) (hp : |p| < 1)
    {I : Type*} (n : I) (i j : Fin 4) :
    (∫ ω, markQuadraticFamily p n i j ω ∂iidLaw (markLaw p) I) = 0 := by
  rw [show (fun ω => markQuadraticFamily p n i j ω) =
    (fun ω => rawQuadratic p i j (ω n)) from rfl,
    integral_iid_eval (markLaw p) I n _
      (measurable_rawQuadratic p i j).aestronglyMeasurable]
  exact rawQuadratic_mean_zero p hp i j

theorem markQuadraticFamily_iIndepFun (p : ℝ) (I : Type*) (i j : Fin 4) :
    iIndepFun (fun n : I => markQuadraticFamily p n i j) (iidLaw (markLaw p) I) :=
  (iidLaw_eval_iIndepFun (markLaw p) I).comp (fun _ => rawQuadratic p i j)
    (fun _ => measurable_rawQuadratic p i j)

theorem markQuadraticFamily_off_covariance (p : ℝ) (hp : |p| < 1)
    {I : Type*} {n m : I} (hnm : n ≠ m) (i j a b : Fin 4) :
    (∫ ω, markQuadraticFamily p n i j ω * markQuadraticFamily p m a b ω
      ∂iidLaw (markLaw p) I) = 0 := by
  have hind := ((iidLaw_eval_iIndepFun (markLaw p) I).indepFun hnm).comp
    (measurable_rawQuadratic p i j) (measurable_rawQuadratic p a b)
  have hi : Integrable (markQuadraticFamily p n i j) (iidLaw (markLaw p) I) := by
    simpa using integrable_markQuadraticFamily_pow p n i j 1
  have hj : Integrable (markQuadraticFamily p m a b) (iidLaw (markLaw p) I) := by
    simpa using integrable_markQuadraticFamily_pow p m a b 1
  have hmul : (∫ ω, markQuadraticFamily p n i j ω * markQuadraticFamily p m a b ω
      ∂iidLaw (markLaw p) I) =
      (∫ ω, markQuadraticFamily p n i j ω ∂iidLaw (markLaw p) I) *
      (∫ ω, markQuadraticFamily p m a b ω ∂iidLaw (markLaw p) I) := by
    simpa only [markQuadraticFamily, Function.comp_def, Pi.mul_apply] using
      hind.integral_mul_of_integrable hi hj
  rw [hmul]
  simp only [markQuadraticFamily_mean_zero p hp, zero_mul]

theorem markQuadraticFamily_diagonal_covariance (p : ℝ) (hp : |p| < 1)
    {I : Type*} (n : I) (i j a b : Fin 4) :
    (∫ ω, markQuadraticFamily p n i j ω * markQuadraticFamily p n a b ω
      ∂iidLaw (markLaw p) I) =
      covarianceMatrix p i a * covarianceMatrix p j b +
      covarianceMatrix p i b * covarianceMatrix p j a := by
  change (∫ ω, (fun x => rawQuadratic p i j x * rawQuadratic p a b x) (ω n)
    ∂iidLaw (markLaw p) I) = _
  rw [integral_iid_eval (markLaw p) I n _
    (integrable_rawQuadratic_product p i j a b).aestronglyMeasurable]
  exact rawQuadratic_covariance p hp i j a b

def quadraticMomentBound (p : ℝ) (i j : Fin 4) (q : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (2 * q + 1), ∫ y, |rawQuadratic p i j y| ^ k ∂markLaw p

theorem quadraticMomentBound_nonneg (p : ℝ) (i j : Fin 4) (q : ℕ) :
    0 ≤ quadraticMomentBound p i j q := by
  apply Finset.sum_nonneg
  intro k hk
  exact integral_nonneg (fun y => pow_nonneg (abs_nonneg _) _)

theorem markQuadraticFamily_moment_bound (p : ℝ) {I : Type*} (n : I)
    (i j : Fin 4) (q k : ℕ) (hk : k ≤ 2 * q) :
    |∫ ω, markQuadraticFamily p n i j ω ^ k ∂iidLaw (markLaw p) I| ≤
      quadraticMomentBound p i j q := by
  calc
    _ ≤ ∫ ω, |markQuadraticFamily p n i j ω| ^ k ∂iidLaw (markLaw p) I := by
      simpa only [Real.norm_eq_abs, abs_pow] using
        norm_integral_le_integral_norm (fun ω => markQuadraticFamily p n i j ω ^ k)
    _ = ∫ y, |rawQuadratic p i j y| ^ k ∂markLaw p := by
      exact integral_iid_eval (markLaw p) I n _
        ((measurable_rawQuadratic p i j).abs.pow_const k).aestronglyMeasurable
    _ ≤ _ := by
      unfold quadraticMomentBound
      apply Finset.single_le_sum (f := fun a : ℕ => ∫ y, |rawQuadratic p i j y| ^ a ∂markLaw p)
        (a := k) (s := Finset.range (2 * q + 1))
      · intro a ha
        exact integral_nonneg (fun y => pow_nonneg (abs_nonneg _) _)
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)

def markQuadraticLp (p : ℝ) {I : Type*} (n : I) (i j : Fin 4) :
    Lp ℂ 2 (iidLaw (markLaw p) I) :=
  ((markQuadraticFamily_memLp_two p n i j).ofReal (K := ℂ)).toLp
    (fun ω => (markQuadraticFamily p n i j ω : ℂ))

theorem markQuadraticLp_ae (p : ℝ) {I : Type*} (n : I) (i j : Fin 4) :
    (markQuadraticLp p n i j : (I → (Fin 4 → ℝ)) → ℂ) =ᵐ[iidLaw (markLaw p) I]
      (fun ω => (markQuadraticFamily p n i j ω : ℂ)) :=
  MemLp.coeFn_toLp _

theorem markQuadraticLp_mean_zero (p : ℝ) (hp : |p| < 1)
    {I : Type*} (n : I) (i j : Fin 4) :
    (∫ ω, markQuadraticLp p n i j ω ∂iidLaw (markLaw p) I) = 0 := by
  rw [integral_congr_ae (markQuadraticLp_ae p n i j), integral_complex_ofReal]
  simp [markQuadraticFamily_mean_zero p hp]

theorem markQuadraticLp_off_covariance (p : ℝ) (hp : |p| < 1)
    {I : Type*} {n m : I} (hnm : n ≠ m) (i j a b : Fin 4) :
    (∫ ω, markQuadraticLp p n i j ω * markQuadraticLp p m a b ω
      ∂iidLaw (markLaw p) I) = 0 := by
  have heq : (fun ω => markQuadraticLp p n i j ω * markQuadraticLp p m a b ω) =ᵐ[iidLaw (markLaw p) I]
      (fun ω => ((markQuadraticFamily p n i j ω * markQuadraticFamily p m a b ω : ℝ) : ℂ)) := by
    filter_upwards [markQuadraticLp_ae p n i j, markQuadraticLp_ae p m a b] with ω hi hj
    simp only [hi, hj, Complex.ofReal_mul]
  rw [integral_congr_ae heq, integral_complex_ofReal, markQuadraticFamily_off_covariance p hp hnm]
  rfl

theorem markQuadraticLp_diagonal_covariance (p : ℝ) (hp : |p| < 1)
    {I : Type*} (n : I) (i j a b : Fin 4) :
    (∫ ω, markQuadraticLp p n i j ω * markQuadraticLp p n a b ω
      ∂iidLaw (markLaw p) I) =
      covarianceMatrix (p : ℂ) i a * covarianceMatrix (p : ℂ) j b +
      covarianceMatrix (p : ℂ) i b * covarianceMatrix (p : ℂ) j a := by
  have heq : (fun ω => markQuadraticLp p n i j ω * markQuadraticLp p n a b ω) =ᵐ[iidLaw (markLaw p) I]
      (fun ω => ((markQuadraticFamily p n i j ω * markQuadraticFamily p n a b ω : ℝ) : ℂ)) := by
    filter_upwards [markQuadraticLp_ae p n i j, markQuadraticLp_ae p n a b] with ω hi hj
    simp only [hi, hj, Complex.ofReal_mul]
  rw [integral_congr_ae heq, integral_complex_ofReal, markQuadraticFamily_diagonal_covariance p hp]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, covarianceMatrix_ofReal]

end GeneralizedBulk.Gaussian
