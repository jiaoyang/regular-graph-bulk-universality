import BourgadeHuang.Counting
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Factorial statistics and counting moments

The factorial statistic sums over injective particle-label maps, not distinct
particle locations. The estimates therefore remain valid when particle locations repeat.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace BourgadeHuang

/-- Expanding a power of the interval count sums over all ordered particle labels. -/
theorem particleCount_pow_eq_sum_tuples {N q : ℕ} (x : Fin N → ℝ) (a b : ℝ) :
    particleCount x a b ^ q =
      ∑ t : Fin q → Fin N, ∏ j, if x (t j) ∈ Set.Icc a b then (1 : ℝ) else 0 := by
  simpa [particleCount] using
    (Fintype.prod_sum (fun (_ : Fin q) (i : Fin N) =>
      if x i ∈ Set.Icc a b then (1 : ℝ) else 0))

/-- The compact-box bound used to pass from count moments to factorial statistics.
Only distinct labels enter the statistic; no simplicity assumption is made. -/
theorem abs_factorialStatistic_le_count_pow {N q : ℕ} (x : Fin N → ℝ)
    (φ : (Fin q → ℝ) → ℝ) (a b C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y, |φ y| ≤ C)
    (hsupport : ∀ y, (¬ ∀ j, y j ∈ Set.Icc a b) → φ y = 0) :
    |factorialStatistic x φ| ≤ C * particleCount x a b ^ q := by
  classical
  rw [particleCount_pow_eq_sum_tuples, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro t _
  by_cases hbox : ∀ j, x (t j) ∈ Set.Icc a b
  · simp only [hbox, if_true, Finset.prod_const_one, mul_one]
    split_ifs
    · exact hbound _
    · simpa using hC
  · have hφ := hsupport (fun j => x (t j)) hbox
    obtain ⟨j, hj⟩ := not_forall.mp hbox
    have hprod : (∏ j, if x (t j) ∈ Set.Icc a b then (1 : ℝ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
    simp only [hφ, ite_self, abs_zero, hprod, mul_zero, le_refl]

theorem measurable_factorialStatistic {Ω : Type*} [MeasurableSpace Ω] {N q : ℕ}
    (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (φ : (Fin q → ℝ) → ℝ) (hφ : Measurable φ) :
    Measurable (fun ω => factorialStatistic (x ω) φ) := by
  classical
  apply Finset.measurable_sum
  intro t _
  by_cases ht : Function.Injective t
  · simp only [ht, if_true]
    exact hφ.comp (measurable_pi_lambda _ fun j => hx (t j))
  · simp only [ht, if_false]
    exact measurable_const

/-- Every fixed finite-particle factorial statistic is genuinely integrable. -/
theorem integrable_factorialStatistic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {N q : ℕ}
    (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (φ : (Fin q → ℝ) → ℝ) (hφ : Measurable φ)
    (a b C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, |φ y| ≤ C)
    (hsupport : ∀ y, (¬ ∀ j, y j ∈ Set.Icc a b) → φ y = 0) :
    Integrable (fun ω => factorialStatistic (x ω) φ) μ := by
  apply ((integrable_particleCount_pow μ x hx a b q).const_mul C).mono'
    (measurable_factorialStatistic x hx φ hφ).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using
      abs_factorialStatistic_le_count_pow (x ω) φ a b C hC hbound hsupport

/-- A `q`th factorial statistic is controlled in square mean by the `2q`th count moment. -/
theorem integral_factorialStatistic_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {N q : ℕ}
    (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (φ : (Fin q → ℝ) → ℝ) (hφ : Measurable φ)
    (a b C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, |φ y| ≤ C)
    (hsupport : ∀ y, (¬ ∀ j, y j ∈ Set.Icc a b) → φ y = 0) :
    Integrable (fun ω => factorialStatistic (x ω) φ ^ 2) μ ∧
      (∫ ω, factorialStatistic (x ω) φ ^ 2 ∂μ) ≤
        C ^ 2 * ∫ ω, particleCount (x ω) a b ^ (q * 2) ∂μ := by
  have hpoint (ω) : factorialStatistic (x ω) φ ^ 2 ≤
      C ^ 2 * particleCount (x ω) a b ^ (q * 2) := by
    have h := pow_le_pow_left₀ (abs_nonneg _) 
      (abs_factorialStatistic_le_count_pow (x ω) φ a b C hC hbound hsupport) 2
    simpa only [sq_abs, mul_pow, ← pow_mul] using h
  have hi := ((integrable_particleCount_pow μ x hx a b (q * 2)).const_mul (C ^ 2)).mono'
    ((measurable_factorialStatistic x hx φ hφ).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (factorialStatistic (x ω) φ))]
      exact hpoint ω)
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hi ((integrable_particleCount_pow μ x hx a b (q * 2)).const_mul _) hpoint

/-- A uniform second moment gives uniform integrability, with all integrability
hypotheses explicit. This is the truncation step used for factorial correlations. -/
theorem uniformIntegrable_of_uniform_second_moment {Ω ι : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : ι → Ω → ℝ) (hfm : ∀ i, Measurable (f i))
    (hfi : ∀ i, Integrable (f i) μ)
    (hfs : ∀ i, Integrable (fun ω => f i ω ^ 2) μ)
    (M : ℝ) (hM : ∀ i, (∫ ω, f i ω ^ 2 ∂μ) ≤ M) :
    UniformIntegrable f 1 μ := by
  apply uniformIntegrable_of (by norm_num) (by norm_num)
    (fun i => (hfm i).aestronglyMeasurable)
  intro ε hε
  let R : ℝ≥0 := ⟨(max M 0 + 1) / ε, by positivity⟩
  have hR : 0 < (R : ℝ) := by dsimp [R]; positivity
  refine ⟨R, fun i => ?_⟩
  have hs : MeasurableSet {ω | R ≤ ‖f i ω‖₊} :=
    measurableSet_le measurable_const (hfm i).nnnorm
  have ht := (hfi i).indicator hs
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm ht]
  apply ENNReal.ofReal_le_ofReal
  have hpoint (ω) : ‖{ω | R ≤ ‖f i ω‖₊}.indicator (f i) ω‖ ≤ f i ω ^ 2 / R := by
    rw [Set.indicator_apply]
    split_ifs with h
    · have h' : (R : ℝ) ≤ |f i ω| := by exact_mod_cast h
      rw [Real.norm_eq_abs, le_div_iff₀ hR]
      nlinarith [sq_abs (f i ω), abs_nonneg (f i ω)]
    · simp only [norm_zero]
      positivity
  calc
    (∫ ω, ‖{ω | R ≤ ‖f i ω‖₊}.indicator (f i) ω‖ ∂μ) ≤
        ∫ ω, f i ω ^ 2 / R ∂μ := integral_mono ht.norm ((hfs i).div_const _) hpoint
    _ = (∫ ω, f i ω ^ 2 ∂μ) / R := integral_div _ _
    _ ≤ M / R := div_le_div_of_nonneg_right (hM i) hR.le
    _ ≤ ε := by
      apply (div_le_iff₀ hR).mpr
      dsimp [R]
      rw [mul_div_cancel₀ _ (ne_of_gt hε)]
      linarith [le_max_left M 0]

/-- Uniform count moments of order `2q` imply uniform integrability of the `q`th
factorial statistics. This includes particles with repeated locations. -/
theorem uniformIntegrable_factorialStatistic_of_count_moment {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {q : ℕ}
    (x : (N : ℕ) → Ω → Fin N → ℝ)
    (hx : ∀ N i, Measurable (fun ω => x N ω i))
    (φ : (Fin q → ℝ) → ℝ) (hφ : Measurable φ)
    (a b C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, |φ y| ≤ C)
    (hsupport : ∀ y, (¬ ∀ j, y j ∈ Set.Icc a b) → φ y = 0)
    (M : ℝ) (hM : ∀ N, (∫ ω, particleCount (x N ω) a b ^ (q * 2) ∂μ) ≤ M) :
    UniformIntegrable (fun N ω => factorialStatistic (x N ω) φ) 1 μ := by
  apply uniformIntegrable_of_uniform_second_moment μ _
    (fun N => measurable_factorialStatistic (x N) (hx N) φ hφ)
    (fun N => integrable_factorialStatistic μ (x N) (hx N) φ hφ a b C hC hbound hsupport)
    (fun N => (integral_factorialStatistic_sq_le μ (x N) (hx N) φ hφ
      a b C hC hbound hsupport).1) (C ^ 2 * M)
  intro N
  exact (integral_factorialStatistic_sq_le μ (x N) (hx N) φ hφ
    a b C hC hbound hsupport).2.trans
    (mul_le_mul_of_nonneg_left (hM N) (sq_nonneg C))

/-- A continuous compactly supported test admits the uniform box and magnitude
bounds needed above, including in dimension zero. -/
theorem compact_test_box_bound {q : ℕ} (φ : (Fin q → ℝ) → ℝ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ (∀ y, |φ y| ≤ C) ∧
      (∀ y, (¬ ∀ j, y j ∈ Set.Icc (-R) R) → φ y = 0) := by
  classical
  obtain ⟨R, hR, hs⟩ := hc.isBounded.exists_pos_norm_le
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hφ
  refine ⟨R, max C 0, hR, le_max_right _ _, ?_, ?_⟩
  · intro y
    exact (show |φ y| ≤ C by simpa only [Real.norm_eq_abs] using hC y).trans (le_max_left C 0)
  · intro y hy
    by_contra hne
    apply hy
    intro j
    have hy' : y ∈ tsupport φ := subset_tsupport φ (Function.mem_support.mpr hne)
    have hn : |y j| ≤ R := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y j).trans (hs y hy')
    exact abs_le.mp hn

end BourgadeHuang
