import GaussianWave.Foundation

/-!
# Fourth-moment tails and preservation of covariance

The finite vector uses `squareMass x = ∑ i, x i ^ 2`, the squared
Euclidean norm, rather than the sup norm on a Lean function space.
The varying-measure tail condition below is stated explicitly because
`MeasureTheory.UniformIntegrable` uses a single fixed base measure.

The clipped-square argument is adapted from the earlier project's
`GeneralizedBulk/Gaussian/UniformIntegrability.lean`; this module has
no dependency on that project and imports no external theorem as an axiom.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace GaussianWave

/-- The square of the Euclidean norm in finite coordinates. -/
def squareMass {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

lemma squareMass_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ squareMass x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma continuous_squareMass {ι : Type*} [Fintype ι] :
    Continuous (squareMass : (ι → ℝ) → ℝ) :=
  continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2)

/-- Deterministic Cauchy--Schwarz, with the exact dimension factor. -/
theorem squareMass_sq_le {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    squareMass x ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, x i ^ 4 := by
  calc
    squareMass x ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, (x i ^ 2) ^ 2 := by
      simpa only [squareMass, Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => x i ^ 2))
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring


lemma integrable_sq_of_fourth {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (f : E → ℝ) (hf : Measurable f)
    (h4 : Integrable (fun x => f x ^ 4) μ) : Integrable (fun x => f x ^ 2) μ := by
  apply ((integrable_const (1 : ℝ)).add h4).mono' (hf.pow_const 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change f x ^ 2 ≤ 1 + f x ^ 4
  nlinarith [sq_nonneg (f x ^ 2 - 1)]

/-- Uniform scalar fourth bounds give the finite vector fourth bound `C m²`. -/
theorem integral_squareMass_sq_le {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ))
    (h4 : ∀ i, Integrable (fun x => x i ^ 4) μ) (C : ℝ)
    (hC : ∀ i, (∫ x, x i ^ 4 ∂μ) ≤ C) :
    Integrable (fun x => squareMass x ^ 2) μ ∧
      (∫ x, squareMass x ^ 2 ∂μ) ≤ C * (Fintype.card ι : ℝ) ^ 2 := by
  have hs : Integrable (fun x => ∑ i, x i ^ 4) μ :=
    integrable_finset_sum _ (fun i _ => h4 i)
  have hm : Integrable (fun x => squareMass x ^ 2) μ := by
    apply (hs.const_mul (Fintype.card ι : ℝ)).mono'
      (continuous_squareMass.pow 2).measurable.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact squareMass_sq_le x
  refine ⟨hm, ?_⟩
  calc
    _ ≤ ∫ x, (Fintype.card ι : ℝ) * ∑ i, x i ^ 4 ∂μ :=
      integral_mono hm (hs.const_mul _) (squareMass_sq_le)
    _ = (Fintype.card ι : ℝ) * ∑ i, ∫ x, x i ^ 4 ∂μ := by
      rw [integral_const_mul, integral_finset_sum _ (fun i _ => h4 i)]
    _ ≤ (Fintype.card ι : ℝ) * ∑ _i : ι, C := by
      gcongr with i
      exact hC i
    _ = _ := by simp; ring

/-- The ordinary function-space sup norm is bounded by the physical Euclidean norm. -/
lemma pi_norm_sq_le_squareMass {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ‖x‖ ^ 2 ≤ squareMass x := by
  classical
  have hi (i : ι) : x i ^ 2 ≤ squareMass x :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have hnorm : ‖x‖ ≤ Real.sqrt (squareMass x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (hi i)
  nlinarith [Real.sq_sqrt (squareMass_nonneg x), norm_nonneg x,
    Real.sqrt_nonneg (squareMass x)]

lemma pi_norm_fourth_le_squareMass_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ‖x‖ ^ 4 ≤ squareMass x ^ 2 := by
  have h := pow_le_pow_left₀ (sq_nonneg ‖x‖) (pi_norm_sq_le_squareMass x) 2
  nlinarith [h]

/-- Bridge to the sup-norm fourth-moment interface used for linear projections. -/
theorem integral_pi_norm_fourth_le {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ))
    (h4 : ∀ i, Integrable (fun x => x i ^ 4) μ) (C : ℝ)
    (hC : ∀ i, (∫ x, x i ^ 4 ∂μ) ≤ C) :
    Integrable (fun x => ‖x‖ ^ 4) μ ∧
      (∫ x, ‖x‖ ^ 4 ∂μ) ≤ C * (Fintype.card ι : ℝ) ^ 2 := by
  obtain ⟨hi, hb⟩ := integral_squareMass_sq_le μ h4 C hC
  have hn : Integrable (fun x => ‖x‖ ^ 4) μ := by
    apply hi.mono' (continuous_norm.pow 4).measurable.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pi_norm_fourth_le_squareMass_sq x
  exact ⟨hn, (integral_mono hn hi pi_norm_fourth_le_squareMass_sq).trans hb⟩

/-- A nonnegative mass with bounded square has an explicit tail bound. -/
theorem integral_mass_tail_le {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (g : E → ℝ) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (h2 : Integrable (fun x => g x ^ 2) μ)
    (L : ℝ) (hL : 0 < L) :
    (∫ x in {x | L < g x}, g x ∂μ) ≤ (∫ x, g x ^ 2 ∂μ) / L := by
  have hi : Integrable g μ := by
    apply ((integrable_const (1 : ℝ)).add h2).mono' hg.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    change g x ≤ 1 + g x ^ 2
    nlinarith [sq_nonneg (g x - 1)]
  have hset : MeasurableSet {x | L < g x} := measurableSet_lt measurable_const hg
  rw [← integral_indicator hset]
  calc
    _ ≤ ∫ x, g x ^ 2 / L ∂μ := by
      apply integral_mono (hi.indicator hset) (h2.div_const L)
      intro x
      by_cases hx : L < g x
      · rw [Set.indicator_of_mem (show x ∈ {x | L < g x} from hx)]
        apply (le_div_iff₀ hL).mpr
        nlinarith [mul_nonneg (hg0 x) (sub_nonneg.mpr hx.le)]
      · rw [Set.indicator_of_not_mem (show x ∉ {x | L < g x} from hx)]
        positivity
    _ = _ := integral_div L _

/-- The empirical finite vector tail estimate in physical Euclidean coordinates. -/
theorem integral_squareMass_tail_le {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (h4 : ∀ i, Integrable (fun x => x i ^ 4) μ) (C : ℝ)
    (hC : ∀ i, (∫ x, x i ^ 4 ∂μ) ≤ C) (R : ℝ) (hR : 0 < R) :
    (∫ x in {x | R ^ 2 < squareMass x}, squareMass x ∂μ) ≤
      C * (Fintype.card ι : ℝ) ^ 2 / R ^ 2 := by
  obtain ⟨hi, hb⟩ := integral_squareMass_sq_le μ h4 C hC
  exact (integral_mass_tail_le μ squareMass continuous_squareMass.measurable
    squareMass_nonneg hi (R ^ 2) (sq_pos_of_pos hR)).trans
      (div_le_div_of_nonneg_right hb (sq_nonneg R))

/-- Square uniform integrability for laws whose measures may vary with the index. -/
def UniformSquareTails {E : Type*} [MeasurableSpace E]
    (μ : ℕ → Measure E) (g : E → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
    ∀ n, (∫ x in {x | R ^ 2 < g x}, g x ∂μ n) < ε

/-- A single scalar fourth bound supplies a uniform square-tail modulus. -/
theorem uniformSquareTails_of_scalar_fourth {ι : Type*} [Fintype ι]
    (μ : ℕ → Measure (ι → ℝ)) [∀ n, IsFiniteMeasure (μ n)]
    (h4 : ∀ n i, Integrable (fun x => x i ^ 4) (μ n))
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ n i, (∫ x, x i ^ 4 ∂μ n) ≤ C) :
    UniformSquareTails μ squareMass := by
  intro ε hε
  let D := C * (Fintype.card ι : ℝ) ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let R := D / ε + 1
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, fun n => ?_⟩
  apply (integral_squareMass_tail_le (μ n) (h4 n) C (hC n) R hR).trans_lt
  change D / R ^ 2 < ε
  apply (div_lt_iff₀ (sq_pos_of_pos hR)).mpr
  have hRD : ε * R = D + ε := by dsimp [R]; field_simp
  have hR1 : 1 ≤ R := by dsimp [R]; linarith [div_nonneg hD hε.le]
  nlinarith [mul_nonneg hε.le (mul_nonneg hR.le (sub_nonneg.mpr hR1))]

def clippedSquare {E : Type*} [TopologicalSpace E] (f : E → ℝ) (hf : Continuous f)
    (R : ℝ) (hR : 0 ≤ R) : BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (f x ^ 2) R)
    ((hf.pow 2).min continuous_const) R (fun x => by
      change |min (f x ^ 2) R| ≤ R
      rw [abs_of_nonneg (le_min (sq_nonneg _) hR)]
      exact min_le_right _ _)

lemma square_clip_error (a R : ℝ) (hR : 0 < R) :
    0 ≤ a ^ 2 - min (a ^ 2) R ∧ a ^ 2 - min (a ^ 2) R ≤ a ^ 4 / R := by
  constructor
  · exact sub_nonneg.mpr (min_le_left _ _)
  · by_cases ha : a ^ 2 ≤ R
    · rw [min_eq_left ha, sub_self]
      exact div_nonneg (by positivity) hR.le
    · rw [min_eq_right (le_of_not_ge ha)]
      apply (le_div_iff₀ hR).mpr
      nlinarith [sq_nonneg (a ^ 2 - R)]

lemma integral_square_clip_error
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (f : E → ℝ) (hf : Continuous f)
    (h4 : Integrable (fun x => f x ^ 4) μ) (R : ℝ) (hR : 0 < R) :
    |(∫ x, f x ^ 2 ∂μ) - ∫ x, clippedSquare f hf R hR.le x ∂μ| ≤
      (∫ x, f x ^ 4 ∂μ) / R := by
  have h2 := integrable_sq_of_fourth μ f hf.measurable h4
  have hc := (clippedSquare f hf R hR.le).integrable μ
  rw [← integral_sub h2 hc]
  have hn : 0 ≤ ∫ x, f x ^ 2 - clippedSquare f hf R hR.le x ∂μ :=
    integral_nonneg (fun x => (square_clip_error (f x) R hR).1)
  rw [abs_of_nonneg hn]
  calc
    _ ≤ ∫ x, f x ^ 4 / R ∂μ := integral_mono (h2.sub hc) (h4.div_const R)
      (fun x => (square_clip_error (f x) R hR).2)
    _ = _ := integral_div R _

/-- Uniform fourth moments preserve second moments under genuine weak convergence.
The fourth moment of the limit is an explicit hypothesis, supplied by a
qualitative Gaussian limit without prescribing its covariance. -/
theorem weak_integral_sq_of_fourth
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hweak : WeakLawConverges μ ν) (f : E → ℝ) (hf : Continuous f)
    (h4 : ∀ n, Integrable (fun x => f x ^ 4) (μ n))
    (h4ν : Integrable (fun x => f x ^ 4) ν) (M : ℝ)
    (hM : ∀ n, (∫ x, f x ^ 4 ∂μ n) ≤ M) :
    Tendsto (fun n => ∫ x, f x ^ 2 ∂μ n) atTop (𝓝 (∫ x, f x ^ 2 ∂ν)) := by
  have hM0 : 0 ≤ M :=
    (integral_nonneg (fun x => by positivity : ∀ x, 0 ≤ f x ^ 4)).trans (hM 0)
  let L := ∫ x, f x ^ 4 ∂ν
  have hL0 : 0 ≤ L := integral_nonneg (fun x => by positivity)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let R := 4 * (M + L + 1) / ε
  have hR : 0 < R := div_pos (mul_pos (by norm_num) (by linarith)) hε
  have htail : M / R + L / R < ε / 2 := by
    rw [← add_div, div_lt_iff₀ hR]
    have he : ε * R = 4 * (M + L + 1) := by dsimp [R]; field_simp
    nlinarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hweak (clippedSquare f hf R hR.le))
    (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hclip := hN n hn
  rw [Real.dist_eq] at hclip ⊢
  have hfirst := integral_square_clip_error (μ n) f hf (h4 n) R hR
  have hlast := integral_square_clip_error ν f hf h4ν R hR
  have hfirst' : |(∫ x, f x ^ 2 ∂μ n) - ∫ x, clippedSquare f hf R hR.le x ∂μ n| ≤ M / R :=
    hfirst.trans (div_le_div_of_nonneg_right (hM n) hR.le)
  have ht1 := abs_sub_le (∫ x, f x ^ 2 ∂μ n) (∫ x, clippedSquare f hf R hR.le x ∂μ n)
    (∫ x, f x ^ 2 ∂ν)
  have ht2 := abs_sub_le (∫ x, clippedSquare f hf R hR.le x ∂μ n)
    (∫ x, clippedSquare f hf R hR.le x ∂ν) (∫ x, f x ^ 2 ∂ν)
  rw [abs_sub_comm (∫ x, clippedSquare f hf R hR.le x ∂ν) (∫ x, f x ^ 2 ∂ν)] at ht2
  change |(∫ x, f x ^ 2 ∂ν) - ∫ x, clippedSquare f hf R hR.le x ∂ν| ≤ L / R at hlast
  nlinarith

end GaussianWave
