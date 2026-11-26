import BourgadeHuang.Factorial
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Removing bounded truncations from vague law convergence

Vague convergence is tested only against bounded continuous observables. The
following estimates rigorously remove that restriction for continuous observables
with uniform second moments. The linear statistic is continuous by the exact
initial topology used in `LocalCountingMeasure`.

The module also proves the first two finite-label inclusion-exclusion identities
and the continuity of the corresponding tensor observable.
-/
noncomputable section
open scoped BigOperators Topology CompactlySupported BoundedContinuousFunction
open MeasureTheory Filter

namespace BourgadeHuang

def clipReal (R x : ℝ) : ℝ := max (-R) (min R x)

theorem continuous_clipReal (R : ℝ) : Continuous (clipReal R) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem abs_clipReal_le (R x : ℝ) (hR : 0 ≤ R) : |clipReal R x| ≤ R := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem abs_sub_clipReal_le_sq_div (R x : ℝ) (hR : 0 < R) :
    |x - clipReal R x| ≤ x ^ 2 / R := by
  rw [le_div_iff₀ hR]
  by_cases hl : x ≤ -R
  · have hxR : x ≤ R := by linarith
    simp only [clipReal, min_eq_right hxR, max_eq_left hl]
    rw [abs_of_nonpos (by linarith : x - -R ≤ 0)]
    nlinarith [sq_nonneg (x + R)]
  · by_cases hh : R ≤ x
    · simp only [clipReal, min_eq_left hh, max_eq_right (by linarith : -R ≤ R)]
      rw [abs_of_nonneg (sub_nonneg.mpr hh)]
      nlinarith [sq_nonneg (x - R)]
    · simp only [clipReal, min_eq_right (le_of_not_ge hh),
        max_eq_right (le_of_not_ge hl), sub_self, abs_zero, zero_mul]
      positivity

def clippedObservable {α : Type*} [TopologicalSpace α] (F : α → ℝ)
    (hF : Continuous F) (R : ℝ) (hR : 0 ≤ R) : α →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => clipReal R (F x), (continuous_clipReal R).comp hF⟩ (2 * R)
    (fun x y => by
      change dist (clipReal R (F x)) (clipReal R (F y)) ≤ 2 * R
      calc
        dist (clipReal R (F x)) (clipReal R (F y)) ≤
            dist (clipReal R (F x)) 0 + dist 0 (clipReal R (F y)) := dist_triangle _ _ _
        _ ≤ R + R := by
          simpa only [Real.dist_eq, sub_zero, zero_sub, abs_neg] using
            add_le_add (abs_clipReal_le R (F x) hR) (abs_clipReal_le R (F y) hR)
        _ = 2 * R := by ring)

theorem integrable_clipReal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (R : ℝ) (hR : 0 ≤ R) : Integrable (fun ω => clipReal R (f ω)) μ := by
  apply (integrable_const R).mono'
    ((continuous_clipReal R).measurable.comp hf).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using abs_clipReal_le R (f ω) hR

theorem abs_integral_sub_clipReal_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : Integrable f μ) (hfs : Integrable (fun ω => f ω ^ 2) μ)
    (R : ℝ) (hR : 0 < R) :
    |(∫ ω, f ω ∂μ) - ∫ ω, clipReal R (f ω) ∂μ| ≤
      (∫ ω, f ω ^ 2 ∂μ) / R := by
  rw [← integral_sub hf (integrable_clipReal μ f hfm R hR.le)]
  calc
    |∫ ω, f ω - clipReal R (f ω) ∂μ| ≤
        ∫ ω, |f ω - clipReal R (f ω)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, f ω ^ 2 / R ∂μ := integral_mono
      ((hf.sub (integrable_clipReal μ f hfm R hR.le)).abs)
      (hfs.div_const R) (fun ω => abs_sub_clipReal_le_sq_div R (f ω) hR)
    _ = (∫ ω, f ω ^ 2 ∂μ) / R := integral_div _ _

/-- Compactly supported linear statistics are continuous for the specified vague topology. -/
theorem continuous_linearStatistic (f : ℝ →C_c ℝ) :
    Continuous (fun ξ : LocalCountingMeasure => ∫ x, f x ∂ξ.measure) := by
  exact continuous_iInf_dom (i := f) continuous_induced_dom

/-- Vague law convergence extends to a continuous unbounded observable when
its second moments are uniformly bounded and the target has a finite second moment. -/
theorem vagueLawConverges_integral_of_second_moments {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : ℕ → Ω → LocalCountingMeasure) (hξ : ∀ N, Measurable (ξ N))
    (ν : Measure LocalCountingMeasure) [IsFiniteMeasure ν]
    (hw : VagueLawConverges μ ξ ν)
    (F : LocalCountingMeasure → ℝ) (hF : Continuous F)
    (hfi : ∀ N, Integrable (fun ω => F (ξ N ω)) μ)
    (hfs : ∀ N, Integrable (fun ω => F (ξ N ω) ^ 2) μ)
    (M : ℝ) (hM : ∀ N, (∫ ω, F (ξ N ω) ^ 2 ∂μ) ≤ M)
    (hνi : Integrable F ν) (hνs : Integrable (fun c => F c ^ 2) ν) :
    Tendsto (fun N => ∫ ω, F (ξ N ω) ∂μ) atTop (𝓝 (∫ c, F c ∂ν)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let B := max M 0 + max (∫ c, F c ^ 2 ∂ν) 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let R := 4 * B / ε
  have hR : 0 < R := by dsimp [R]; positivity
  have hεR : (ε / 4) * R = B := by dsimp [R]; field_simp; ring
  have hsource : M / R < ε / 4 := by
    rw [div_lt_iff₀ hR, hεR]
    dsimp [B]
    linarith [le_max_left M 0, le_max_right (∫ c, F c ^ 2 ∂ν) 0]
  have htarget : (∫ c, F c ^ 2 ∂ν) / R < ε / 4 := by
    rw [div_lt_iff₀ hR, hεR]
    dsimp [B]
    linarith [le_max_right M 0, le_max_left (∫ c, F c ^ 2 ∂ν) 0]
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp
    (hw (clippedObservable F hF R hR.le)) (ε / 2) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have hs := (abs_integral_sub_clipReal_le μ (fun ω => F (ξ N ω))
    (hF.measurable.comp (hξ N)) (hfi N) (hfs N) R hR).trans
    (div_le_div_of_nonneg_right (hM N) hR.le)
  have ht := abs_integral_sub_clipReal_le ν F hF.measurable hνi hνs R hR
  have hc := hN₀ N hN
  change dist (∫ ω, clipReal R (F (ξ N ω)) ∂μ)
    (∫ c, clipReal R (F c) ∂ν) < ε / 2 at hc
  have htri := dist_triangle4 (∫ ω, F (ξ N ω) ∂μ)
    (∫ ω, clipReal R (F (ξ N ω)) ∂μ)
    (∫ c, clipReal R (F c) ∂ν) (∫ c, F c ∂ν)
  rw [Real.dist_eq] at hc ⊢
  simp only [Real.dist_eq] at htri
  rw [abs_sub_comm (∫ c, clipReal R (F c) ∂ν)] at htri
  linarith

/-- A compactly supported linear observable is bounded by the interval count. -/
theorem abs_linearStatistic_le_count (f : ℝ →C_c ℝ) (a b C : ℝ)
    (hbound : ∀ x, |f x| ≤ C) (hsupport : Function.support f ⊆ Set.Icc a b)
    (ξ : LocalCountingMeasure) :
    |∫ x, f x ∂ξ.measure| ≤ C * (ξ.measure (Set.Icc a b)).toReal := by
  have hfinite : ξ.measure (Set.Icc a b) < ⊤ := isCompact_Icc.measure_lt_top
  letI : IsFiniteMeasure (ξ.measure.restrict (Set.Icc a b)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite⟩
  have hrestrict : (∫ x, f x ∂ξ.measure) = ∫ x in Set.Icc a b, f x ∂ξ.measure := by
    rw [← integral_indicator measurableSet_Icc]
    congr 1
    exact (Set.indicator_eq_self.mpr hsupport).symm
  rw [hrestrict]
  have h := norm_integral_le_of_norm_le_const
    (μ := ξ.measure.restrict (Set.Icc a b))
    (f := fun x => f x) (C := C) (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hbound x)
  simpa only [Real.norm_eq_abs, measureReal_def, Measure.restrict_apply_univ] using h

/-- Explicit box data for a real compactly supported test. -/
theorem linear_test_box_bound (f : ℝ →C_c ℝ) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ (∀ x, |f x| ≤ C) ∧
      Function.support f ⊆ Set.Icc (-R) R := by
  obtain ⟨R, hR, hs⟩ := f.hasCompactSupport.isBounded.exists_pos_norm_le
  obtain ⟨C, hC⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  refine ⟨R, max C 0, hR, le_max_right _ _, ?_, ?_⟩
  · intro x
    exact (show |f x| ≤ C by simpa only [Real.norm_eq_abs] using hC x).trans
      (le_max_left C 0)
  · intro x hx
    exact abs_le.mp (by
      simpa only [Real.norm_eq_abs] using hs x (subset_tsupport f hx))

/-- First-order correlation convergence follows from vague law convergence and
uniform interval-count moments. No extra continuity or transfer assumption is used. -/
theorem vagueLawConverges_linearStatistic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : ℕ → Ω → LocalCountingMeasure)
    (hξ : ∀ N, Measurable (ξ N)) (target : TargetProcess)
    (hw : VagueLawConverges μ ξ target.law) (hc : UniformCountMoments μ ξ)
    (f : ℝ →C_c ℝ) :
    Tendsto (fun N => ∫ ω, (∫ x, f x ∂(ξ N ω).measure) ∂μ)
      atTop (𝓝 (∫ c, (∫ x, f x ∂c.measure) ∂target.law)) := by
  letI : IsProbabilityMeasure target.law := target.probability
  obtain ⟨R, C, _, hC, hb, hs⟩ := linear_test_box_bound f
  let F : LocalCountingMeasure → ℝ := fun c => ∫ x, f x ∂c.measure
  have hF : Continuous F := continuous_linearStatistic f
  let count : LocalCountingMeasure → ℝ := fun c => (c.measure (Set.Icc (-R) R)).toReal
  have hbound (c) : |F c| ≤ C * count c := abs_linearStatistic_le_count f (-R) R C hb hs c
  have hboundSq (c) : F c ^ 2 ≤ C ^ 2 * count c ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (hbound c) 2
    simpa only [sq_abs, mul_pow] using h
  have hi (N) : Integrable (fun ω => F (ξ N ω)) μ := by
    have hcount : Integrable (fun ω => count (ξ N ω)) μ := by
      simpa only [pow_one] using (hc (-R) R 1).1 N
    apply (hcount.const_mul C).mono' (hF.measurable.comp (hξ N)).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound (ξ N ω)
  have hsq (N) : Integrable (fun ω => F (ξ N ω) ^ 2) μ := by
    apply (((hc (-R) R 2).1 N).const_mul (C ^ 2)).mono'
      ((hF.measurable.comp (hξ N)).pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs, Function.comp_apply, abs_pow, sq_abs]
      exact hboundSq _
  obtain ⟨M, hM⟩ := (hc (-R) R 2).2
  have hm (N) : (∫ ω, F (ξ N ω) ^ 2 ∂μ) ≤ C ^ 2 * M := by
    calc
      (∫ ω, F (ξ N ω) ^ 2 ∂μ) ≤ ∫ ω, C ^ 2 * count (ξ N ω) ^ 2 ∂μ :=
        integral_mono (hsq N) (((hc (-R) R 2).1 N).const_mul (C ^ 2)) (fun ω => hboundSq _)
      _ = C ^ 2 * ∫ ω, count (ξ N ω) ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ C ^ 2 * M := mul_le_mul_of_nonneg_left (hM N) (sq_nonneg C)
  have hνi : Integrable F target.law := by
    have hcount : Integrable count target.law := by
      simpa only [pow_one] using target.count_moments_integrable (-R) R 1
    apply (hcount.const_mul C).mono' hF.measurable.aestronglyMeasurable
    exact Eventually.of_forall fun c => by simpa only [Real.norm_eq_abs] using hbound c
  have hνsq : Integrable (fun c => F c ^ 2) target.law := by
    apply ((target.count_moments_integrable (-R) R 2).const_mul (C ^ 2)).mono'
      (hF.measurable.pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (F c))]; exact hboundSq c
  exact vagueLawConverges_integral_of_second_moments μ ξ hξ target.law hw F hF
    hi hsq (C ^ 2 * M) hm hνi hνsq

/-- For finite configurations the vague linear observable is exactly the particle sum. -/
theorem linearStatistic_finite_dirac {N : ℕ} (x : Fin N → ℝ) (f : ℝ →C_c ℝ) :
    (∫ y, f y ∂(∑ i, Measure.dirac (x i))) = ∑ i, f (x i) := by
  rw [integral_finset_sum_measure]
  · simp only [integral_dirac]
  · intro i _
    exact integrable_dirac

theorem factorialStatistic_one {N : ℕ} (x : Fin N → ℝ) (φ : (Fin 1 → ℝ) → ℝ) :
    factorialStatistic x φ = ∑ i, φ (fun _ => x i) := by
  classical
  unfold factorialStatistic
  simp only [Function.injective_of_subsingleton, if_true]
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin N))
  intro t
  congr 1
  funext j
  exact congrArg (fun l => x (t l)) (Subsingleton.elim j default)

theorem target_factorialExpectation_one (target : TargetProcess)
    (φ : (Fin 1 → ℝ) → ℝ) :
    target.factorialExpectation 1 φ =
      ∫ c, (∫ y, φ (fun _ => y) ∂c.measure) ∂target.law := by
  classical
  unfold TargetProcess.factorialExpectation
  simp only [Function.injective_of_subsingleton, if_true]
  congr 1
  funext c
  have h := (measurePreserving_piUnique (fun _ : Fin 1 => c.measure)).integral_comp'
    (fun y => φ (fun _ => y))
  convert h using 1
  congr 1
  funext y
  congr 1
  funext j
  exact congrArg y (Subsingleton.elim j default)

/-- The first nontrivial inclusion-exclusion identity removes coincident labels,
not coincident positions. It holds even when `x i = x j` for distinct labels. -/
theorem factorialStatistic_two_tensor {N : ℕ} (x : Fin N → ℝ) (f g : ℝ → ℝ) :
    factorialStatistic x (fun y : Fin 2 → ℝ => f (y 0) * g (y 1)) =
      (∑ i, f (x i)) * (∑ j, g (x j)) - ∑ i, f (x i) * g (x i) := by
  classical
  have hinj (t : Fin 2 → Fin N) : Function.Injective t ↔ t 0 ≠ t 1 := by
    constructor
    · intro h he
      have hh := h he
      exact (by decide : (0 : Fin 2) ≠ 1) hh
    · intro h i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  unfold factorialStatistic
  calc
    (∑ t : Fin 2 → Fin N, if Function.Injective t then f (x (t 0)) * g (x (t 1)) else 0) =
        ∑ ij : Fin N × Fin N, if ij.1 ≠ ij.2 then f (x ij.1) * g (x ij.2) else 0 := by
      apply Fintype.sum_equiv (finTwoArrowEquiv (Fin N))
      intro t
      simp only [hinj]
      rfl
    _ = ∑ i, ∑ j, if i ≠ j then f (x i) * g (x j) else 0 := Fintype.sum_prod_type _
    _ = (∑ i, f (x i)) * (∑ j, g (x j)) - ∑ i, f (x i) * g (x i) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      have hdiag : (∑ j : Fin N, if i = j then f (x i) * g (x j) else 0) =
          f (x i) * g (x i) := by simp
      rw [← hdiag, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i = j <;> simp [h]

/-- A continuous factorial observable for order-two tensor tests. -/
def pairFactorialObservable (f g : ℝ →C_c ℝ) (ξ : LocalCountingMeasure) : ℝ :=
  (∫ x, f x ∂ξ.measure) * (∫ x, g x ∂ξ.measure) - ∫ x, f x * g x ∂ξ.measure

theorem continuous_pairFactorialObservable (f g : ℝ →C_c ℝ) :
    Continuous (pairFactorialObservable f g) := by
  exact ((continuous_linearStatistic f).mul (continuous_linearStatistic g)).sub
    (continuous_linearStatistic (f * g))

theorem pairFactorialObservable_finite {N : ℕ} (x : Fin N → ℝ)
    (f g : ℝ →C_c ℝ) (ξ : LocalCountingMeasure)
    (hξ : ξ.measure = ∑ i, Measure.dirac (x i)) :
    pairFactorialObservable f g ξ =
      factorialStatistic x (fun y : Fin 2 → ℝ => f (y 0) * g (y 1)) := by
  rw [factorialStatistic_two_tensor]
  unfold pairFactorialObservable
  rw [hξ, linearStatistic_finite_dirac, linearStatistic_finite_dirac]
  congr 1
  exact linearStatistic_finite_dirac x (f * g)

end BourgadeHuang
