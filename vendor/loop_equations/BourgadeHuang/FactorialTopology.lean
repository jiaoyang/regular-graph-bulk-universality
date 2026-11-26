import BourgadeHuang.FactorialAlgebra
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Tensor approximation for compactly supported factorial tests

Stone–Weierstrass supplies the approximation by separated coordinate functions.
A common one-dimensional cutoff turns every factor into a compactly supported
factor without losing uniform approximation or a common support box.
-/
noncomputable section
open scoped BigOperators Topology CompactlySupported
open MeasureTheory Filter

namespace BourgadeHuang

/-- A separated-coordinate continuous test. -/
def continuousTensor {q : ℕ} (f : Fin q → C(ℝ, ℝ)) : C((Fin q → ℝ), ℝ) :=
  ⟨fun x => ∏ j, f j (x j), continuous_finset_prod _ fun j _ =>
    (f j).continuous.comp (continuous_apply j)⟩

@[simp] theorem continuousTensor_apply {q : ℕ} (f : Fin q → C(ℝ, ℝ))
    (x : Fin q → ℝ) : continuousTensor f x = ∏ j, f j (x j) := rfl

/-- Finite real linear combinations of separated-coordinate functions. -/
def continuousTensorSpan (q : ℕ) : Submodule ℝ C((Fin q → ℝ), ℝ) :=
  Submodule.span ℝ (Set.range (@continuousTensor q))

theorem continuousTensor_mem_span {q : ℕ} (f : Fin q → C(ℝ, ℝ)) :
    continuousTensor f ∈ continuousTensorSpan q := Submodule.subset_span ⟨f, rfl⟩

theorem continuousTensor_one (q : ℕ) : continuousTensor (fun _ : Fin q => 1) = 1 := by
  ext x
  simp

theorem continuousTensor_mul {q : ℕ} (f g : Fin q → C(ℝ, ℝ)) :
    continuousTensor f * continuousTensor g = continuousTensor (fun j => f j * g j) := by
  ext x
  simp only [ContinuousMap.mul_apply, continuousTensor_apply, Finset.prod_mul_distrib]

theorem continuousTensorSpan_mul_mem {q : ℕ} {f g : C((Fin q → ℝ), ℝ)}
    (hf : f ∈ continuousTensorSpan q) (hg : g ∈ continuousTensorSpan q) :
    f * g ∈ continuousTensorSpan q := by
  induction hf, hg using Submodule.span_induction₂ with
  | mem_mem f g hf hg =>
    obtain ⟨fs, rfl⟩ := hf
    obtain ⟨gs, rfl⟩ := hg
    rw [continuousTensor_mul]
    exact continuousTensor_mem_span _
  | zero_left => simp
  | zero_right => simp
  | add_left f g h hf hg hh ihf ihg =>
    rw [add_mul]
    exact (continuousTensorSpan q).add_mem ihf ihg
  | add_right f g h hf hg hh ihf ihg =>
    rw [mul_add]
    exact (continuousTensorSpan q).add_mem ihf ihg
  | smul_left r f g hf hg ih =>
    rw [smul_mul_assoc]
    exact (continuousTensorSpan q).smul_mem r ih
  | smul_right r f g hf hg ih =>
    rw [mul_smul_comm]
    exact (continuousTensorSpan q).smul_mem r ih

/-- The tensor span is an algebra, so Stone–Weierstrass applies directly. -/
def continuousTensorAlgebra (q : ℕ) : Subalgebra ℝ C((Fin q → ℝ), ℝ) where
  carrier := continuousTensorSpan q
  add_mem' := (continuousTensorSpan q).add_mem
  zero_mem' := (continuousTensorSpan q).zero_mem
  mul_mem' := continuousTensorSpan_mul_mem
  one_mem' := by rw [← continuousTensor_one q]; exact continuousTensor_mem_span _
  algebraMap_mem' r := by
    have hone : (1 : C((Fin q → ℝ), ℝ)) ∈ continuousTensorSpan q := by
      rw [← continuousTensor_one q]; exact continuousTensor_mem_span _
    have h := (continuousTensorSpan q).smul_mem r hone
    simpa only [Algebra.algebraMap_eq_smul_one] using h

theorem continuousTensorAlgebra_separatesPoints (q : ℕ) :
    (continuousTensorAlgebra q).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
    by_contra! h
    exact hxy (funext h)
  let f : Fin q → C(ℝ, ℝ) := fun i => if i = j then ContinuousMap.id ℝ else 1
  have heval (z : Fin q → ℝ) : continuousTensor f z = z j := by
    simp only [continuousTensor_apply, f]
    simp only [apply_ite, ContinuousMap.coe_id, ContinuousMap.coe_one]
    simp only [ite_apply, id_eq, Pi.one_apply, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  refine ⟨continuousTensor f, ⟨continuousTensor f, continuousTensor_mem_span f, rfl⟩, ?_⟩
  simpa only [heval] using hj

/-- Tensor sums approximate every continuous function uniformly on any compact set. -/
theorem exists_continuousTensorSpan_approx {q : ℕ} (φ : C((Fin q → ℝ), ℝ))
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ ∈ continuousTensorSpan q, ∀ x ∈ K, |ψ x - φ x| < ε := by
  simpa only [Real.norm_eq_abs] using
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (continuousTensorAlgebra_separatesPoints q) φ hK hε

/-- Separated-coordinate tests whose factors have compact support. -/
def compactTensorSpan (q : ℕ) : Submodule ℝ C((Fin q → ℝ), ℝ) :=
  Submodule.span ℝ (Set.range (fun f : Fin q → ℝ →C_c ℝ =>
    continuousTensor (fun j => (f j).toContinuousMap)))

/-- Multiplication by a product cutoff turns a tensor sum into a compact tensor sum. -/
theorem cutoff_mul_mem_compactTensorSpan {q : ℕ} (χ : ℝ →C_c ℝ)
    {ψ : C((Fin q → ℝ), ℝ)} (hψ : ψ ∈ continuousTensorSpan q) :
    continuousTensor (fun _ => χ.toContinuousMap) * ψ ∈ compactTensorSpan q := by
  induction hψ using Submodule.span_induction with
  | mem ψ hψ =>
    obtain ⟨f, rfl⟩ := hψ
    let g : Fin q → ℝ →C_c ℝ := fun j =>
      ⟨χ.toContinuousMap * f j, χ.hasCompactSupport.mul_right⟩
    apply Submodule.subset_span
    refine ⟨g, ?_⟩
    ext x
    simp only [ContinuousMap.mul_apply, continuousTensor_apply, g,
      CompactlySupportedContinuousMap.coe_mk, Finset.prod_mul_distrib]
  | zero => simp
  | add f g hf hg ihf ihg =>
    rw [mul_add]
    exact (compactTensorSpan q).add_mem ihf ihg
  | smul r f hf ih =>
    rw [mul_smul_comm]
    exact (compactTensorSpan q).smul_mem r ih

/-- An explicit cutoff equal to one on `[-R,R]` and zero outside `[-R-1,R+1]`. -/
def intervalCutoff (R : ℝ) : C(ℝ, ℝ) :=
  ⟨fun x => max 0 (min 1 (R + 1 - |x|)),
    continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))⟩

theorem intervalCutoff_mem_Icc (R x : ℝ) : intervalCutoff R x ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem intervalCutoff_eq_one {R x : ℝ} (hx : x ∈ Set.Icc (-R) R) :
    intervalCutoff R x = 1 := by
  have ha : |x| ≤ R := abs_le.mpr hx
  simp only [intervalCutoff, ContinuousMap.coe_mk]
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem intervalCutoff_eq_zero {R x : ℝ} (hx : x ∉ Set.Icc (-(R + 1)) (R + 1)) :
    intervalCutoff R x = 0 := by
  have ha : R + 1 < |x| := lt_of_not_ge (fun h => hx (abs_le.mp h))
  simp only [intervalCutoff, ContinuousMap.coe_mk]
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]

theorem intervalCutoff_hasCompactSupport (R : ℝ) : HasCompactSupport (intervalCutoff R) := by
  exact HasCompactSupport.intro' isCompact_Icc isClosed_Icc
    (fun _ hx => intervalCutoff_eq_zero hx)

/-- A compactly supported cutoff, bundled for use in tensor tests. -/
def compactIntervalCutoff (R : ℝ) : ℝ →C_c ℝ :=
  ⟨intervalCutoff R, intervalCutoff_hasCompactSupport R⟩

theorem prod_intervalCutoff_mem_Icc {q : ℕ} (R : ℝ) (x : Fin q → ℝ) :
    (∏ j, intervalCutoff R (x j)) ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨Finset.prod_nonneg (fun j _ => (intervalCutoff_mem_Icc R (x j)).1),
    Finset.prod_le_one (fun j _ => (intervalCutoff_mem_Icc R (x j)).1)
      (fun j _ => (intervalCutoff_mem_Icc R (x j)).2)⟩

/-- Cutoff multiplication preserves a test supported in the inner box. -/
theorem prod_intervalCutoff_mul {q : ℕ} (R : ℝ) (φ : (Fin q → ℝ) → ℝ)
    (hs : ∀ x, (¬ ∀ j, x j ∈ Set.Icc (-R) R) → φ x = 0) (x : Fin q → ℝ) :
    (∏ j, intervalCutoff R (x j)) * φ x = φ x := by
  by_cases hx : ∀ j, x j ∈ Set.Icc (-R) R
  · simp only [fun j => intervalCutoff_eq_one (hx j), Finset.prod_const_one, one_mul]
  · rw [hs x hx, mul_zero]

theorem prod_intervalCutoff_eq_zero {q : ℕ} (R : ℝ) (x : Fin q → ℝ)
    (hx : ¬ ∀ j, x j ∈ Set.Icc (-(R + 1)) (R + 1)) :
    (∏ j, intervalCutoff R (x j)) = 0 := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp hx
  exact Finset.prod_eq_zero (Finset.mem_univ j) (intervalCutoff_eq_zero hj)

/-- Every continuous compactly supported multivariate test can be uniformly
approximated by finite sums of products of one-dimensional compactly supported
tests. All approximants vanish outside one fixed box. -/
theorem exists_compactTensorSpan_uniform_approx {q : ℕ}
    (φ : C((Fin q → ℝ), ℝ)) (hs : HasCompactSupport φ) :
    ∃ R : ℝ, 0 < R ∧
      (∀ x, (¬ ∀ j, x j ∈ Set.Icc (-R) R) → φ x = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ ψ ∈ compactTensorSpan q,
        (∀ x, |ψ x - φ x| ≤ ε) ∧
        (∀ x, (¬ ∀ j, x j ∈ Set.Icc (-R) R) → ψ x = 0) := by
  classical
  obtain ⟨R, C, hR, hC, hb, hφ⟩ := compact_test_box_bound φ φ.continuous hs
  have hinner : Set.Icc (-R) R ⊆ Set.Icc (-(R + 1)) (R + 1) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hφ' (x) (hx : ¬ ∀ j, x j ∈ Set.Icc (-(R + 1)) (R + 1)) : φ x = 0 :=
    hφ x (fun h => hx (fun j => hinner (h j)))
  refine ⟨R + 1, by linarith, hφ', ?_⟩
  intro ε hε
  let K := Set.pi Set.univ (fun _ : Fin q => Set.Icc (-(R + 1)) (R + 1))
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨ψ, hψ, ha⟩ := exists_continuousTensorSpan_approx φ hK hε
  let cutoff := continuousTensor (fun _ : Fin q => (compactIntervalCutoff R).toContinuousMap)
  refine ⟨cutoff * ψ, cutoff_mul_mem_compactTensorSpan _ hψ, ?_, ?_⟩
  · intro x
    have hcut : cutoff x * φ x = φ x := prod_intervalCutoff_mul R φ hφ x
    have hbcut : |cutoff x| ≤ 1 := by
      change |∏ j, intervalCutoff R (x j)| ≤ 1
      rw [abs_of_nonneg (prod_intervalCutoff_mem_Icc R x).1]
      exact (prod_intervalCutoff_mem_Icc R x).2
    by_cases hx : ∀ j, x j ∈ Set.Icc (-(R + 1)) (R + 1)
    · have hxK : x ∈ K := by simpa only [K, Set.mem_pi, Set.mem_univ, true_implies]
      calc
        |(cutoff * ψ) x - φ x| = |cutoff x * (ψ x - φ x)| := by
          congr 1
          simp only [ContinuousMap.mul_apply, mul_sub, hcut]
        _ = |cutoff x| * |ψ x - φ x| := abs_mul _ _
        _ ≤ 1 * |ψ x - φ x| := mul_le_mul_of_nonneg_right hbcut (abs_nonneg _)
        _ ≤ ε := by simpa only [one_mul] using (ha x hxK).le
    · have hz : cutoff x = 0 := prod_intervalCutoff_eq_zero R x hx
      simp only [ContinuousMap.mul_apply, hz, zero_mul, hφ' x hx, sub_self, abs_zero]
      exact hε.le
  · intro x hx
    have hz : cutoff x = 0 := prod_intervalCutoff_eq_zero R x hx
    simp only [ContinuousMap.mul_apply, hz, zero_mul]

/-- The location-distinct factorial integral used in the target process. -/
def factorialIntegral {q : ℕ} (φ : (Fin q → ℝ) → ℝ) (ξ : LocalCountingMeasure) : ℝ :=
  ∫ y : Fin q → ℝ, if Function.Injective y then φ y else 0
    ∂Measure.pi (fun _ : Fin q => ξ.measure)

theorem continuousTensor_hasCompactSupport {q : ℕ} (f : Fin q → ℝ →C_c ℝ) :
    HasCompactSupport (continuousTensor (fun j => (f j).toContinuousMap)) := by
  obtain ⟨R, C, hR, hC, hb, hs⟩ := tensor_test_box_bound f
  let K := Set.pi Set.univ (fun _ : Fin q => Set.Icc (-R) R)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  apply HasCompactSupport.intro' hK hK.isClosed
  intro x hx
  exact tensor_test_support f _ hs x (by simpa only [K, Set.mem_pi, Set.mem_univ,
    true_implies] using hx)

theorem LocalCountingMeasure.integrable_factorial_of_compactSupport
    (ξ : LocalCountingMeasure) (hsimple : ∀ x, ξ.measure {x} ≤ 1)
    {q : ℕ} (φ : C((Fin q → ℝ), ℝ)) (hs : HasCompactSupport φ) :
    Integrable (fun y : Fin q → ℝ => if Function.Injective y then φ y else 0)
      (Measure.pi (fun _ : Fin q => ξ.measure)) := by
  obtain ⟨R, C, hR, hC, hb, hφ⟩ := compact_test_box_bound φ φ.continuous hs
  exact ξ.integrable_injective_pi hsimple isCompact_Icc φ hφ

theorem factorialIntegral_add {q : ℕ} (φ ψ : C((Fin q → ℝ), ℝ))
    (hφ : HasCompactSupport φ) (hψ : HasCompactSupport ψ)
    (ξ : LocalCountingMeasure) (hξ : ∀ x, ξ.measure {x} ≤ 1) :
    factorialIntegral (φ + ψ) ξ = factorialIntegral φ ξ + factorialIntegral ψ ξ := by
  classical
  unfold factorialIntegral
  have heq : (fun y : Fin q → ℝ => if Function.Injective y then (φ + ψ) y else 0) =
      fun y => (if Function.Injective y then φ y else 0) +
        (if Function.Injective y then ψ y else 0) := by
    funext y
    split_ifs <;> simp
  rw [heq, integral_add (ξ.integrable_factorial_of_compactSupport hξ φ hφ)
    (ξ.integrable_factorial_of_compactSupport hξ ψ hψ)]

theorem factorialIntegral_smul {q : ℕ} (r : ℝ) (φ : C((Fin q → ℝ), ℝ))
    (ξ : LocalCountingMeasure) :
    factorialIntegral (r • φ) ξ = r * factorialIntegral φ ξ := by
  classical
  unfold factorialIntegral
  have heq : (fun y : Fin q → ℝ => if Function.Injective y then (r • φ) y else 0) =
      fun y => r * (if Function.Injective y then φ y else 0) := by
    funext y
    split_ifs <;> simp
  rw [heq, integral_const_mul]

/-- A representation by a continuous observable includes equality both for
finite labeled configurations and for simple target counting measures. -/
def HasContinuousFactorialObservable {q : ℕ} (φ : C((Fin q → ℝ), ℝ)) : Prop :=
  ∃ F : LocalCountingMeasure → ℝ, Continuous F ∧
    (∀ (N : ℕ) (x : Fin N → ℝ) (ξ : LocalCountingMeasure),
      ξ.measure = ∑ i, Measure.dirac (x i) → F ξ = factorialStatistic x φ) ∧
    (∀ ξ : LocalCountingMeasure, (∀ x, ξ.measure {x} ≤ 1) →
      F ξ = factorialIntegral φ ξ)

/-- Every finite tensor sum has a genuine continuous factorial observable. -/
theorem compactTensorSpan_continuous_observable {q : ℕ}
    {φ : C((Fin q → ℝ), ℝ)} (hφ : φ ∈ compactTensorSpan q) :
    HasCompactSupport φ ∧ HasContinuousFactorialObservable φ := by
  classical
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨f, rfl⟩ := hφ
    refine ⟨continuousTensor_hasCompactSupport f, tensorFactorialObservable f,
      continuous_tensorFactorialObservable f, ?_, ?_⟩
    · intro N x ξ hξ
      exact tensorFactorialObservable_finite x f ξ hξ
    · intro ξ hξ
      exact tensorFactorialObservable_eq_factorial_integral f ξ hξ
  | zero =>
    refine ⟨HasCompactSupport.zero, (fun _ => 0), continuous_const, ?_, ?_⟩
    · intro N x ξ hξ
      exact (factorialStatistic_zero x).symm
    · intro ξ hξ
      simp [factorialIntegral]
  | add φ ψ hφ hψ ihφ ihψ =>
    obtain ⟨hsφ, F, hF, hFs, hFt⟩ := ihφ
    obtain ⟨hsψ, G, hG, hGs, hGt⟩ := ihψ
    refine ⟨hsφ.add hsψ, (fun ξ => F ξ + G ξ), hF.add hG, ?_, ?_⟩
    · intro N x ξ hξ
      change F ξ + G ξ = _
      rw [hFs N x ξ hξ, hGs N x ξ hξ]
      exact (factorialStatistic_add x φ ψ).symm
    · intro ξ hξ
      change F ξ + G ξ = _
      rw [hFt ξ hξ, hGt ξ hξ, factorialIntegral_add φ ψ hsφ hsψ ξ hξ]
  | smul r φ hφ ih =>
    obtain ⟨hsφ, F, hF, hFs, hFt⟩ := ih
    refine ⟨hsφ.smul_left, (fun ξ => r * F ξ), continuous_const.mul hF, ?_, ?_⟩
    · intro N x ξ hξ
      change r * F ξ = _
      rw [hFs N x ξ hξ]
      exact (factorialStatistic_smul x r φ).symm
    · intro ξ hξ
      change r * F ξ = _
      rw [hFt ξ hξ, factorialIntegral_smul]

/-- On a target process, tensor-span factorial integrals are measurably represented
by continuous functions. -/
theorem TargetProcess.aestronglyMeasurable_factorialIntegral_of_mem_span
    (target : TargetProcess) {q : ℕ} {φ : C((Fin q → ℝ), ℝ)}
    (hφ : φ ∈ compactTensorSpan q) :
    AEStronglyMeasurable (factorialIntegral φ) target.law := by
  obtain ⟨_, F, hF, _, hFt⟩ := compactTensorSpan_continuous_observable hφ
  apply hF.measurable.aestronglyMeasurable.congr
  filter_upwards [target.simple] with ξ hξ
  exact hFt ξ hξ

/-- Tensor approximation proves measurability of every compactly supported
factorial integral; no measurability assumption on the measure-valued map is needed. -/
theorem TargetProcess.aestronglyMeasurable_factorialIntegral
    (target : TargetProcess) {q : ℕ} (φ : C((Fin q → ℝ), ℝ))
    (hs : HasCompactSupport φ) :
    AEStronglyMeasurable (factorialIntegral φ) target.law := by
  obtain ⟨R, hR, hsφ, happrox⟩ := exists_compactTensorSpan_uniform_approx φ hs
  have hpos (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  choose ψ hψ ha hsψ using fun n : ℕ => happrox (1 / ((n : ℝ) + 1)) (hpos n)
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => target.aestronglyMeasurable_factorialIntegral_of_mem_span (hψ n))
  filter_upwards [target.simple] with ξ hξ
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (g := fun n : ℕ => (1 / ((n : ℝ) + 1)) *
    (ξ.measure (Set.Icc (-R) R)).toReal ^ q) (fun _ => norm_nonneg _) ?_ ?_
  · intro n
    exact ξ.abs_sub_factorial_integral_le_count_pow hξ (ψ n) φ (-R) R
      (1 / ((n : ℝ) + 1)) (hpos n).le (ha n) (hsψ n) hsφ
  · simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const
      ((ξ.measure (Set.Icc (-R) R)).toReal ^ q)

/-- Every continuous compactly supported factorial integral is integrable under
the target process's count-moment hypotheses. -/
theorem TargetProcess.integrable_factorialIntegral
    (target : TargetProcess) {q : ℕ} (φ : C((Fin q → ℝ), ℝ))
    (hs : HasCompactSupport φ) : Integrable (factorialIntegral φ) target.law := by
  obtain ⟨R, C, hR, hC, hb, hsφ⟩ := compact_test_box_bound φ φ.continuous hs
  exact target.integrable_factorial_integral_of_aestronglyMeasurable φ
    (target.aestronglyMeasurable_factorialIntegral φ hs) (-R) R C hC hb hsφ

/-- Compact test functions have integrable finite-particle factorial statistics. -/
theorem integrable_factorialStatistic_of_compactSupport {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {N q : ℕ}
    (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (φ : C((Fin q → ℝ), ℝ)) (hs : HasCompactSupport φ) :
    Integrable (fun ω => factorialStatistic (x ω) φ) μ := by
  obtain ⟨R, C, hR, hC, hb, hsφ⟩ := compact_test_box_bound φ φ.continuous hs
  exact integrable_factorialStatistic μ x hx φ φ.continuous.measurable (-R) R C hC hb hsφ

theorem TargetProcess.factorialExpectation_add
    (target : TargetProcess) {q : ℕ} (φ ψ : C((Fin q → ℝ), ℝ))
    (hφ : HasCompactSupport φ) (hψ : HasCompactSupport ψ) :
    target.factorialExpectation q (φ + ψ : C((Fin q → ℝ), ℝ)) =
      target.factorialExpectation q φ + target.factorialExpectation q ψ := by
  change (∫ ξ, factorialIntegral (φ + ψ) ξ ∂target.law) =
    (∫ ξ, factorialIntegral φ ξ ∂target.law) + ∫ ξ, factorialIntegral ψ ξ ∂target.law
  rw [← integral_add (target.integrable_factorialIntegral φ hφ)
    (target.integrable_factorialIntegral ψ hψ)]
  apply integral_congr_ae
  filter_upwards [target.simple] with ξ hξ
  exact factorialIntegral_add φ ψ hφ hψ ξ hξ

theorem TargetProcess.factorialExpectation_smul
    (target : TargetProcess) {q : ℕ} (r : ℝ) (φ : C((Fin q → ℝ), ℝ)) :
    target.factorialExpectation q (r • φ : C((Fin q → ℝ), ℝ)) = r * target.factorialExpectation q φ := by
  change (∫ ξ, factorialIntegral (r • φ) ξ ∂target.law) =
    r * ∫ ξ, factorialIntegral φ ξ ∂target.law
  simp_rw [factorialIntegral_smul, integral_const_mul]

/-- The source factorial expectations obey the same compact-box approximation
bound as the target expectations. -/
theorem abs_sub_integral_factorialStatistic_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {N q : ℕ}
    (x : Ω → Fin N → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (φ ψ : C((Fin q → ℝ), ℝ))
    (hφc : HasCompactSupport φ) (hψc : HasCompactSupport ψ)
    (a b C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, |φ y - ψ y| ≤ C)
    (hφ : ∀ y, (¬ ∀ j, y j ∈ Set.Icc a b) → φ y = 0)
    (hψ : ∀ y, (¬ ∀ j, y j ∈ Set.Icc a b) → ψ y = 0) :
    |(∫ ω, factorialStatistic (x ω) φ ∂μ) -
      (∫ ω, factorialStatistic (x ω) ψ ∂μ)| ≤
      C * ∫ ω, particleCount (x ω) a b ^ q ∂μ := by
  have hfi := integrable_factorialStatistic_of_compactSupport μ x hx φ hφc
  have hgi := integrable_factorialStatistic_of_compactSupport μ x hx ψ hψc
  rw [← integral_sub hfi hgi, ← integral_const_mul]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono (hfi.sub hgi).abs ((integrable_particleCount_pow μ x hx a b q).const_mul C)
  intro ω
  change |factorialStatistic (x ω) φ - factorialStatistic (x ω) ψ| ≤
    C * particleCount (x ω) a b ^ q
  rw [← factorialStatistic_sub]
  apply abs_factorialStatistic_le_count_pow (x ω) (fun y => φ y - ψ y) a b C hC hbound
  intro y hy
  simp [hφ y hy, hψ y hy]

end BourgadeHuang
