import BourgadeHuang.CountingLawSubsequence

/-!
# Moment bounds and uniform integrability for weak limits

Nonnegative continuous moments of a weak limit are obtained by monotone bounded
truncation. Uniform second moments then remove the bounded-test restriction.
The target integrability is proved, rather than imposed as a separate hypothesis.
-/
noncomputable section
open scoped Topology ENNReal BoundedContinuousFunction
open MeasureTheory Filter
namespace BourgadeHuang

/-- Weak law convergence tested against all bounded continuous real functions. -/
def WeakLawConverges {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure Ω) (x : ℕ → Ω → X) (ν : Measure X) : Prop :=
  ∀ F : X →ᵇ ℝ, Tendsto (fun N => ∫ ω, F (x N ω) ∂μ) atTop (𝓝 (∫ c, F c ∂ν))

/-- The law of a measurable random variable as a bundled probability measure. -/
def probabilityLaw {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (x : Ω → X) (hx : Measurable x) : ProbabilityMeasure X :=
  ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω) hx.aemeasurable

theorem integral_probabilityLaw {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → X) (hx : Measurable x) (F : X →ᵇ ℝ) :
    (∫ c, F c ∂(probabilityLaw μ x hx : Measure X)) = ∫ ω, F (x ω) ∂μ :=
  integral_map hx.aemeasurable F.continuous.aestronglyMeasurable

theorem weakLawConverges_iff_tendsto_probabilityLaw
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → X) (hx : ∀ N, Measurable (x N))
    (ν : ProbabilityMeasure X) :
    WeakLawConverges μ x (ν : Measure X) ↔
      Tendsto (fun N => probabilityLaw μ (x N) (hx N)) atTop (𝓝 ν) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  simp only [integral_probabilityLaw]
  rfl

theorem clipReal_eq_min_of_nonneg {R x : ℝ} (hR : 0 ≤ R) (hx : 0 ≤ x) :
    clipReal R x = min R x := by
  unfold clipReal
  exact max_eq_right ((neg_nonpos.mpr hR).trans (le_min hR hx))

/-- Nonnegative continuous observables inherit eventual uniform expectation bounds
under weak convergence, including genuine integrability of the limit observable. -/
theorem WeakLawConverges.integrable_nonneg_and_integral_le
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure X} [IsFiniteMeasure ν]
    {x : ℕ → Ω → X} (hw : WeakLawConverges μ x ν) (hx : ∀ N, Measurable (x N))
    (F : X → ℝ) (hF : Continuous F) (hpos : ∀ c, 0 ≤ F c)
    (hi : ∀ N, Integrable (fun ω => F (x N ω)) μ)
    (C : ℝ) (hC : ∀ᶠ N in atTop, (∫ ω, F (x N ω) ∂μ) ≤ C) :
    Integrable F ν ∧ (∫ c, F c ∂ν) ≤ C := by
  have hC0 : 0 ≤ C := by
    obtain ⟨N, hN⟩ := hC.exists
    exact (integral_nonneg (fun ω => hpos (x N ω))).trans hN
  have hn (n : ℕ) : (∫ c, clipReal n (F c) ∂ν) ≤ C := by
    apply le_of_tendsto (hw (clippedObservable F hF n (Nat.cast_nonneg _)))
    filter_upwards [hC] with N hN
    apply le_trans _ hN
    apply integral_mono (integrable_clipReal μ _ (hF.measurable.comp (hx N)) n (Nat.cast_nonneg _)) (hi N)
    intro ω
    change clipReal n (F (x N ω)) ≤ F (x N ω)
    rw [clipReal_eq_min_of_nonneg (Nat.cast_nonneg _) (hpos _)]
    exact min_le_right _ _
  have hclippos (n : ℕ) (c : X) : 0 ≤ clipReal n (F c) := by
    rw [clipReal_eq_min_of_nonneg (Nat.cast_nonneg _) (hpos c)]
    exact le_min (Nat.cast_nonneg _) (hpos c)
  have hlim : Tendsto (fun n : ℕ => ∫⁻ c, ENNReal.ofReal (clipReal n (F c)) ∂ν) atTop
      (𝓝 (∫⁻ c, ENNReal.ofReal (F c) ∂ν)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
      (fun n => ((continuous_clipReal n).comp hF).measurable.ennreal_ofReal.aemeasurable)
    · apply Filter.Eventually.of_forall
      intro c n m hnm
      apply ENNReal.ofReal_le_ofReal
      change clipReal n (F c) ≤ clipReal m (F c)
      simp only [clipReal_eq_min_of_nonneg (Nat.cast_nonneg _) (hpos c)]
      exact min_le_min (by exact_mod_cast hnm) le_rfl
    · apply Filter.Eventually.of_forall
      intro c
      obtain ⟨N, hN⟩ := exists_nat_ge (F c)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      change ENNReal.ofReal (F c) = ENNReal.ofReal (clipReal n (F c))
      rw [clipReal_eq_min_of_nonneg (Nat.cast_nonneg _) (hpos c),
        min_eq_right (hN.trans (by exact_mod_cast hn))]
  have hb : (∫⁻ c, ENNReal.ofReal (F c) ∂ν) ≤ ENNReal.ofReal C := by
    apply le_of_tendsto hlim
    exact Filter.Eventually.of_forall fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (integrable_clipReal ν F hF.measurable n (Nat.cast_nonneg _))
        (Filter.Eventually.of_forall (hclippos n))]
      exact ENNReal.ofReal_le_ofReal (hn n)
  have hν : Integrable F ν := by
    refine ⟨hF.measurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpos)]
    exact hb.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hν, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hC0).mp
  rwa [ofReal_integral_eq_lintegral_ofReal hν (Filter.Eventually.of_forall hpos)]

/-- Finite second moments imply finite first moments, with an explicit domination. -/
theorem integrable_of_integrable_sq {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsFiniteMeasure ν] {F : X → ℝ}
    (hF : AEStronglyMeasurable F ν) (hs : Integrable (fun c => F c ^ 2) ν) :
    Integrable F ν := by
  apply ((integrable_const 1).add hs).mono' hF
  apply Filter.Eventually.of_forall
  intro c
  rw [Real.norm_eq_abs]
  change |F c| ≤ 1 + F c ^ 2
  nlinarith [sq_nonneg (|F c| - 1), sq_abs (F c), abs_nonneg (F c)]

/-- Weak convergence plus uniform second moments gives convergence of the actual
unbounded expectation. Target integrability is derived by bounded truncation. -/
theorem WeakLawConverges.integral_of_second_moments
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure X} [IsFiniteMeasure ν]
    {x : ℕ → Ω → X} (hw : WeakLawConverges μ x ν) (hx : ∀ N, Measurable (x N))
    (F : X → ℝ) (hF : Continuous F)
    (hs : ∀ N, Integrable (fun ω => F (x N ω) ^ 2) μ)
    (M : ℝ) (hM : ∀ N, (∫ ω, F (x N ω) ^ 2 ∂μ) ≤ M) :
    Integrable F ν ∧ Tendsto (fun N => ∫ ω, F (x N ω) ∂μ) atTop (𝓝 (∫ c, F c ∂ν)) := by
  obtain ⟨hνs, hνM⟩ := hw.integrable_nonneg_and_integral_le hx
    (fun c => F c ^ 2) (hF.pow 2) (fun _ => sq_nonneg _) hs M (Filter.Eventually.of_forall hM)
  have hνi := integrable_of_integrable_sq hF.measurable.aestronglyMeasurable hνs
  have hfi (N : ℕ) := integrable_of_integrable_sq
    (hF.measurable.comp (hx N)).aestronglyMeasurable (hs N)
  refine ⟨hνi, ?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let B := max M 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let R := 4 * B / ε
  have hR : 0 < R := by dsimp [R]; positivity
  have hεR : (ε / 4) * R = B := by dsimp [R]; field_simp; ring
  have hMR : M / R < ε / 4 := by
    rw [div_lt_iff₀ hR, hεR]
    dsimp [B]
    linarith [le_max_left M 0]
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp
    (hw (clippedObservable F hF R hR.le)) (ε / 2) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have hsource := (abs_integral_sub_clipReal_le μ (fun ω => F (x N ω))
    (hF.measurable.comp (hx N)) (hfi N) (hs N) R hR).trans
    (div_le_div_of_nonneg_right (hM N) hR.le)
  have htarget := (abs_integral_sub_clipReal_le ν F hF.measurable hνi hνs R hR).trans
    (div_le_div_of_nonneg_right hνM hR.le)
  have hclip := hN₀ N hN
  change dist (∫ ω, clipReal R (F (x N ω)) ∂μ)
    (∫ c, clipReal R (F c) ∂ν) < ε / 2 at hclip
  have htri := dist_triangle4 (∫ ω, F (x N ω) ∂μ)
    (∫ ω, clipReal R (F (x N ω)) ∂μ)
    (∫ c, clipReal R (F c) ∂ν) (∫ c, F c ∂ν)
  rw [Real.dist_eq] at hclip ⊢
  simp only [Real.dist_eq] at htri
  rw [abs_sub_comm (∫ c, clipReal R (F c) ∂ν)] at htri
  linarith

/-- The same uniform-integrability argument transfers complex observables by
applying the real theorem to their two coordinates. -/
theorem WeakLawConverges.integral_complex_of_second_moments
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure X} [IsFiniteMeasure ν]
    {x : ℕ → Ω → X} (hw : WeakLawConverges μ x ν) (hx : ∀ N, Measurable (x N))
    (F : X → ℂ) (hF : Continuous F)
    (hs : ∀ N, Integrable (fun ω => ‖F (x N ω)‖ ^ 2) μ)
    (M : ℝ) (hM : ∀ N, (∫ ω, ‖F (x N ω)‖ ^ 2 ∂μ) ≤ M) :
    Integrable F ν ∧ Tendsto (fun N => ∫ ω, F (x N ω) ∂μ) atTop (𝓝 (∫ c, F c ∂ν)) := by
  obtain ⟨hνnorm, _⟩ := hw.integral_of_second_moments hx (fun c => ‖F c‖) hF.norm hs M hM
  have hνi := (integrable_norm_iff hF.measurable.aestronglyMeasurable).mp hνnorm
  have hfi (N : ℕ) : Integrable (fun ω => F (x N ω)) μ :=
    (integrable_norm_iff (hF.measurable.comp (hx N)).aestronglyMeasurable).mp
      (integrable_of_integrable_sq (hF.measurable.comp (hx N)).norm.aestronglyMeasurable (hs N))
  have hcoord (g : ℂ → ℝ) (hg : Continuous g) (hb : ∀ z, |g z| ≤ ‖z‖) :
      Tendsto (fun N => ∫ ω, g (F (x N ω)) ∂μ) atTop (𝓝 (∫ c, g (F c) ∂ν)) := by
    have hpoint (c : X) : g (F c) ^ 2 ≤ ‖F c‖ ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb (F c)) 2
    have hsi (N : ℕ) : Integrable (fun ω => g (F (x N ω)) ^ 2) μ := by
      apply (hs N).mono' (((hg.comp hF).measurable.comp (hx N)).pow_const 2).aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro ω
      change ‖g (F (x N ω)) ^ 2‖ ≤ ‖F (x N ω)‖ ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (g (F (x N ω))))]
      exact hpoint (x N ω)
    exact (hw.integral_of_second_moments hx (fun c => g (F c)) (hg.comp hF) hsi M
      (fun N => (integral_mono (hsi N) (hs N) (fun ω => hpoint (x N ω))).trans (hM N))).2
  have hr := hcoord Complex.re Complex.continuous_re Complex.abs_re_le_norm
  have hi := hcoord Complex.im Complex.continuous_im Complex.abs_im_le_norm
  have hrc := Complex.continuous_ofReal.tendsto _ |>.comp hr
  have hic := Complex.continuous_ofReal.tendsto _ |>.comp hi
  refine ⟨hνi, ?_⟩
  have hh := hrc.add (hic.mul (tendsto_const_nhds (x := Complex.I)))
  have he (N : ℕ) : ((∫ ω, (F (x N ω)).re ∂μ : ℝ) : ℂ) +
      (∫ ω, (F (x N ω)).im ∂μ : ℝ) * Complex.I = ∫ ω, F (x N ω) ∂μ :=
    integral_re_add_im (hfi N)
  have heν : ((∫ c, (F c).re ∂ν : ℝ) : ℂ) +
      (∫ c, (F c).im ∂ν : ℝ) * Complex.I = ∫ c, F c ∂ν := integral_re_add_im hνi
  simpa only [Function.comp_apply, he, heν] using hh

/-- Continuous complex observables with polynomial growth pass through weak
limits when the controlling variable has a uniform moment of twice the degree.
Only source moment integrability is assumed; target integrability is derived. -/
theorem WeakLawConverges.integral_complex_of_polynomial_growth
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure X} [IsFiniteMeasure ν]
    {x : ℕ → Ω → X} (hw : WeakLawConverges μ x ν) (hx : ∀ N, Measurable (x N))
    (F : X → ℂ) (hF : Continuous F) (A : X → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ)
    (hb : ∀ s, ‖F s‖ ≤ C * (1 + |A s|) ^ p)
    (hs : ∀ N, Integrable (fun ω => |A (x N ω)| ^ (2 * p)) μ)
    (M : ℝ) (hM : ∀ N, (∫ ω, |A (x N ω)| ^ (2 * p) ∂μ) ≤ M) :
    Integrable F ν ∧
      Tendsto (fun N => ∫ ω, F (x N ω) ∂μ) atTop (𝓝 (∫ s, F s ∂ν)) := by
  let D : ℝ := C ^ 2 * 2 ^ (2 * p - 1)
  have hD : 0 ≤ D := mul_nonneg (pow_nonneg hC 2) (by positivity)
  have hpoint (s : X) : ‖F s‖ ^ 2 ≤ D * (1 + |A s| ^ (2 * p)) := by
    calc
      ‖F s‖ ^ 2 ≤ (C * (1 + |A s|) ^ p) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hb s) 2
      _ = C ^ 2 * (1 + |A s|) ^ (2 * p) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm p 2]
      _ ≤ C ^ 2 * (2 ^ (2 * p - 1) * (1 + |A s| ^ (2 * p))) :=
        mul_le_mul_of_nonneg_left (by simpa only [one_pow] using
          (add_pow_le (zero_le_one : (0 : ℝ) ≤ 1) (abs_nonneg (A s)) (2 * p))) (sq_nonneg C)
      _ = D * (1 + |A s| ^ (2 * p)) := by dsimp [D]; ring
  have hi (N : ℕ) : Integrable (fun ω => ‖F (x N ω)‖ ^ 2) μ := by
    apply (((integrable_const 1).add (hs N)).const_mul D).mono'
      ((hF.measurable.comp (hx N)).norm.pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint _
  apply hw.integral_complex_of_second_moments hx F hF hi (D * (1 + M))
  intro N
  calc
    (∫ ω, ‖F (x N ω)‖ ^ 2 ∂μ) ≤ ∫ ω, D * (1 + |A (x N ω)| ^ (2 * p)) ∂μ :=
      integral_mono (hi N) (((integrable_const 1).add (hs N)).const_mul D)
        (fun ω => hpoint _)
    _ = D * (1 + ∫ ω, |A (x N ω)| ^ (2 * p) ∂μ) := by
      rw [integral_const_mul, integral_add (integrable_const 1) (hs N)]
      simp
    _ ≤ D * (1 + M) := mul_le_mul_of_nonneg_left (add_le_add_left (hM N) 1) hD

/-- Every fixed norm moment transfers as soon as twice that moment is uniformly
bounded. This applies on an arbitrary Borel state space. -/
theorem WeakLawConverges.integral_norm_pow
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure X} [IsFiniteMeasure ν]
    {x : ℕ → Ω → X} (hw : WeakLawConverges μ x ν) (hx : ∀ N, Measurable (x N))
    (F : X → ℂ) (hF : Continuous F) (q : ℕ)
    (hs : ∀ N, Integrable (fun ω => ‖F (x N ω)‖ ^ (2 * q)) μ)
    (M : ℝ) (hM : ∀ N, (∫ ω, ‖F (x N ω)‖ ^ (2 * q) ∂μ) ≤ M) :
    Integrable (fun c => ‖F c‖ ^ q) ν ∧
      Tendsto (fun N => ∫ ω, ‖F (x N ω)‖ ^ q ∂μ) atTop (𝓝 (∫ c, ‖F c‖ ^ q ∂ν)) := by
  have he (a : ℝ) : (a ^ q) ^ 2 = a ^ (2 * q) := by rw [← pow_mul, Nat.mul_comm]
  apply hw.integral_of_second_moments hx (fun c => ‖F c‖ ^ q) (hF.norm.pow q)
    (fun N => by simpa only [he] using hs N) M
  intro N
  simpa only [he] using hM N

/-- A weak limit remains in a closed set that contains every source state. -/
theorem WeakLawConverges.ae_mem_closed
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x : ℕ → Ω → X} (hx : ∀ N, Measurable (x N)) (ν : ProbabilityMeasure X)
    (hw : WeakLawConverges μ x (ν : Measure X))
    {A : Set X} (hA : IsClosed A) (hsource : ∀ N ω, x N ω ∈ A) : ∀ᵐ c ∂(ν : Measure X), c ∈ A := by
  have hlim := (weakLawConverges_iff_tendsto_probabilityLaw μ x hx ν).mp hw
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hA
  have hmass (N : ℕ) : (probabilityLaw μ (x N) (hx N) : Measure X) A = 1 := by
    change Measure.map (x N) μ A = 1
    have hpre : x N ⁻¹' A = Set.univ := Set.eq_univ_of_forall (hsource N)
    rw [Measure.map_apply (hx N) hA.measurableSet, hpre, measure_univ]
  simp_rw [hmass, limsup_const] at hport
  apply ae_iff.mpr
  change (ν : Measure X) Aᶜ = 0
  rw [measure_compl hA.measurableSet (measure_ne_top _ _), measure_univ]
  exact tsub_eq_zero_of_le hport

/-- Weak laws lift through a topological and measurable embedding when the target
law is supported on the embedded image. -/
theorem WeakLawConverges.lift_embedding
    {Ω X Y : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {x : ℕ → Ω → X}
    (hx : ∀ N, Measurable (x N)) {f : X → Y}
    (he : Topology.IsEmbedding f) (hf : MeasurableEmbedding f) (ν : ProbabilityMeasure Y)
    (hν : (ν : Measure Y) (Set.range f)ᶜ = 0)
    (hw : WeakLawConverges μ (fun N => f ∘ x N) (ν : Measure Y)) :
    WeakLawConverges μ x (embeddingPullbackLaw hf ν hν : Measure X) := by
  have hm := fun N => hf.measurable.comp (hx N)
  have hconv := (weakLawConverges_iff_tendsto_probabilityLaw μ (fun N => f ∘ x N) hm ν).mp hw
  have heq (N : ℕ) : (probabilityLaw μ (x N) (hx N)).map hf.measurable.aemeasurable =
      probabilityLaw μ (f ∘ x N) (hm N) := by
    apply Subtype.ext
    exact Measure.map_map hf.measurable (hx N)
  have hmap : Tendsto (fun N => (probabilityLaw μ (x N) (hx N)).map hf.measurable.aemeasurable)
      atTop (𝓝 ν) := by simpa only [heq] using hconv
  exact (weakLawConverges_iff_tendsto_probabilityLaw μ x hx _).mpr
    (tendsto_embeddingPullbackLaw he hf (fun N => probabilityLaw μ (x N) (hx N)) ν hν hmap)

end BourgadeHuang
