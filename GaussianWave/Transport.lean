import GaussianWave.MomentTail

/-!
# Genuine transport couplings and their Euclidean quadratic cost

A coupling here is a measure on the product with the two required marginals.
The cost is the integral of the physical squared Euclidean distance, and
`wassersteinTwoSquared` is its infimum over all such measures.
The normalized-product construction below is a constructive finite-component
coupling, including components with zero mass.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace GaussianWave

/-- A genuine measure coupling. No convergence or optimality is included. -/
structure Coupling {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) where
  measure : Measure (E × F)
  fst_eq : Measure.map Prod.fst measure = μ
  snd_eq : Measure.map Prod.snd measure = ν

namespace Coupling
variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
variable {μ : Measure E} {ν : Measure F}

instance isProbability (γ : Coupling μ ν) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure γ.measure := by
  constructor
  have h := congrArg (fun m : Measure E => m Set.univ) γ.fst_eq
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ, measure_univ] using h

def independent (μ : Measure E) (ν : Measure F)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : Coupling μ ν where
  measure := μ.prod ν
  fst_eq := by simp
  snd_eq := by simp

theorem integral_fst (γ : Coupling μ ν) {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → G) (hf : AEStronglyMeasurable f μ) :
    (∫ z, f z.1 ∂γ.measure) = ∫ x, f x ∂μ := by
  have hf' : AEStronglyMeasurable f (Measure.map Prod.fst γ.measure) := by
    simpa only [γ.fst_eq] using hf
  simpa only [γ.fst_eq] using (integral_map measurable_fst.aemeasurable hf').symm

theorem integral_snd (γ : Coupling μ ν) {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : F → G) (hf : AEStronglyMeasurable f ν) :
    (∫ z, f z.2 ∂γ.measure) = ∫ x, f x ∂ν := by
  have hf' : AEStronglyMeasurable f (Measure.map Prod.snd γ.measure) := by
    simpa only [γ.snd_eq] using hf
  simpa only [γ.snd_eq] using (integral_map measurable_snd.aemeasurable hf').symm

theorem integrable_fst (γ : Coupling μ ν) {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → G) (hf : Integrable f μ) : Integrable (fun z => f z.1) γ.measure := by
  rw [← γ.fst_eq] at hf
  exact (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).mp hf

theorem integrable_snd (γ : Coupling μ ν) {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : F → G) (hf : Integrable f ν) : Integrable (fun z => f z.2) γ.measure := by
  rw [← γ.snd_eq] at hf
  exact (integrable_map_measure hf.aestronglyMeasurable measurable_snd.aemeasurable).mp hf

end Coupling

/-- Independent coupling of equal-mass finite submeasures, retaining their
original mass rather than normalizing the resulting coupling to one. -/
def normalizedProduct {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (α : Measure E) (β : Measure F) : Measure (E × F) :=
  (α Set.univ)⁻¹ • α.prod β

theorem normalizedProduct_fst {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (α : Measure E) (β : Measure F) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (hmass : α Set.univ = β Set.univ) :
    Measure.map Prod.fst (normalizedProduct α β) = α := by
  by_cases hzero : α Set.univ = 0
  · have hα : α = 0 := Measure.measure_univ_eq_zero.mp hzero
    simp [normalizedProduct, hα]
  · rw [normalizedProduct, Measure.map_smul, Measure.map_fst_prod, smul_smul,
      ← hmass, ENNReal.inv_mul_cancel hzero (measure_ne_top α Set.univ), one_smul]

theorem normalizedProduct_snd {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (α : Measure E) (β : Measure F) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (hmass : α Set.univ = β Set.univ) :
    Measure.map Prod.snd (normalizedProduct α β) = β := by
  by_cases hzero : α Set.univ = 0
  · have hα : α = 0 := Measure.measure_univ_eq_zero.mp hzero
    have hβ : β = 0 := Measure.measure_univ_eq_zero.mp (hmass.symm.trans hzero)
    simp [normalizedProduct, hα, hβ]
  · rw [normalizedProduct, Measure.map_smul, Measure.map_snd_prod, smul_smul,
      ENNReal.inv_mul_cancel hzero (measure_ne_top α Set.univ), one_smul]

theorem map_finset_sum_measure {E F ι : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (f : E → F) (hf : Measurable f) (s : Finset ι) (m : ι → Measure E) :
    Measure.map f (∑ i ∈ s, m i) = ∑ i ∈ s, Measure.map f (m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, Measure.map_add _ _ hf, ih]

/-- Assemble equal-mass components into a coupling by explicit products.
A residual component can be included as one additional index. -/
def couplingOfComponents {E F ι : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Fintype ι] (μ : Measure E) (ν : Measure F)
    (α : ι → Measure E) (β : ι → Measure F)
    [∀ i, IsFiniteMeasure (α i)] [∀ i, IsFiniteMeasure (β i)]
    (hmass : ∀ i, α i Set.univ = β i Set.univ)
    (hleft : ∑ i, α i = μ) (hright : ∑ i, β i = ν) : Coupling μ ν where
  measure := ∑ i, normalizedProduct (α i) (β i)
  fst_eq := by
    rw [map_finset_sum_measure _ measurable_fst]
    simp_rw [normalizedProduct_fst _ _ (hmass _)]
    exact hleft
  snd_eq := by
    rw [map_finset_sum_measure _ measurable_snd]
    simp_rw [normalizedProduct_snd _ _ (hmass _)]
    exact hright

/-- Physical squared Euclidean distance, independent of the function-space
sup norm used by Lean's ordinary `ι → ℝ` norm. -/
def squareTransportCost {ι : Type*} [Fintype ι] (z : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  squareMass (z.1 - z.2)

theorem squareTransportCost_nonneg {ι : Type*} [Fintype ι]
    (z : (ι → ℝ) × (ι → ℝ)) : 0 ≤ squareTransportCost z := squareMass_nonneg _

theorem continuous_squareTransportCost {ι : Type*} [Fintype ι] :
    Continuous (squareTransportCost : ((ι → ℝ) × (ι → ℝ)) → ℝ) :=
  continuous_squareMass.comp (continuous_fst.sub continuous_snd)

/-- Extended nonnegative quadratic cost of an actual coupling. -/
def quadraticCouplingCost {ι : Type*} [Fintype ι]
    {μ ν : Measure (ι → ℝ)} (γ : Coupling μ ν) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (squareTransportCost z) ∂γ.measure

/-- Genuine squared Wasserstein infimum over all measure couplings. -/
def wassersteinTwoSquared {ι : Type*} [Fintype ι]
    (μ ν : Measure (ι → ℝ)) : ℝ≥0∞ :=
  ⨅ γ : Coupling μ ν, quadraticCouplingCost γ

theorem wassersteinTwoSquared_le_cost {ι : Type*} [Fintype ι]
    {μ ν : Measure (ι → ℝ)} (γ : Coupling μ ν) :
    wassersteinTwoSquared μ ν ≤ quadraticCouplingCost γ := iInf_le _ γ

end GaussianWave

namespace GaussianWave

lemma squareTransportCost_le {ι : Type*} [Fintype ι]
    (z : (ι → ℝ) × (ι → ℝ)) :
    squareTransportCost z ≤ 2 * squareMass z.1 + 2 * squareMass z.2 := by
  calc
    _ ≤ ∑ i, (2 * z.1 i ^ 2 + 2 * z.2 i ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      change (z.1 i - z.2 i) ^ 2 ≤ _
      nlinarith [sq_nonneg (z.1 i + z.2 i)]
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, squareMass]

lemma squareTransportCost_sq_le {ι : Type*} [Fintype ι]
    (z : (ι → ℝ) × (ι → ℝ)) :
    squareTransportCost z ^ 2 ≤ 8 * (squareMass z.1 ^ 2 + squareMass z.2 ^ 2) := by
  have h := pow_le_pow_left₀ (squareTransportCost_nonneg z) (squareTransportCost_le z) 2
  nlinarith [sq_nonneg (squareMass z.1 - squareMass z.2)]

lemma integrable_of_integrable_square {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (g : E → ℝ)
    (hg : AEStronglyMeasurable g μ) (h2 : Integrable (fun x => g x ^ 2) μ) :
    Integrable g μ := by
  apply ((integrable_const (1 : ℝ)).add h2).mono' hg
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  change |g x| ≤ 1 + g x ^ 2
  nlinarith [sq_nonneg (|g x| - 1), sq_abs (g x)]

namespace Coupling
variable {ι : Type*} [Fintype ι] {μ ν : Measure (ι → ℝ)}

theorem integrable_squareCost_sq (γ : Coupling μ ν)
    (hμ : Integrable (fun x => squareMass x ^ 2) μ)
    (hν : Integrable (fun x => squareMass x ^ 2) ν) :
    Integrable (fun z => squareTransportCost z ^ 2) γ.measure := by
  have hl := γ.integrable_fst _ hμ
  have hr := γ.integrable_snd _ hν
  apply ((hl.add hr).const_mul 8).mono'
    (continuous_squareTransportCost.pow 2).measurable.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact squareTransportCost_sq_le z

theorem integral_squareCost_sq_le (γ : Coupling μ ν)
    (hμ : Integrable (fun x => squareMass x ^ 2) μ)
    (hν : Integrable (fun x => squareMass x ^ 2) ν) :
    (∫ z, squareTransportCost z ^ 2 ∂γ.measure) ≤
      8 * ((∫ x, squareMass x ^ 2 ∂μ) + ∫ x, squareMass x ^ 2 ∂ν) := by
  have hl := γ.integrable_fst _ hμ
  have hr := γ.integrable_snd _ hν
  calc
    _ ≤ ∫ z, 8 * (squareMass z.1 ^ 2 + squareMass z.2 ^ 2) ∂γ.measure :=
      integral_mono (γ.integrable_squareCost_sq hμ hν) ((hl.add hr).const_mul _)
        squareTransportCost_sq_le
    _ = _ := by
      rw [integral_const_mul, integral_add hl hr,
        γ.integral_fst _ hμ.aestronglyMeasurable,
        γ.integral_snd _ hν.aestronglyMeasurable]

theorem integrable_squareCost (γ : Coupling μ ν) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => squareMass x ^ 2) μ)
    (hν : Integrable (fun x => squareMass x ^ 2) ν) :
    Integrable squareTransportCost γ.measure :=
  integrable_of_integrable_square γ.measure squareTransportCost
    continuous_squareTransportCost.measurable.aestronglyMeasurable
    (γ.integrable_squareCost_sq hμ hν)

end Coupling

/-- A varying-measure moment argument: one separates a small value, a large
fourth-moment tail, and the probability of exceeding the small value. -/
theorem integral_nonnegative_le_threshold {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (g : E → ℝ)
    (hg : Measurable g) (_hg0 : ∀ x, 0 ≤ g x)
    (h2 : Integrable (fun x => g x ^ 2) μ)
    (δ T : ℝ) (hδ : 0 ≤ δ) (hT : 0 < T) :
    (∫ x, g x ∂μ) ≤ δ + (∫ x, g x ^ 2 ∂μ) / T +
      T * μ.real {x | δ < g x} := by
  have hi := integrable_of_integrable_square μ g hg.aestronglyMeasurable h2
  have hs : MeasurableSet {x | δ < g x} := measurableSet_lt measurable_const hg
  have hp (x : E) : g x ≤ δ + g x ^ 2 / T +
      Set.indicator {x | δ < g x} (fun _ => T) x := by
    by_cases hx : δ < g x
    · rw [Set.indicator_of_mem (show x ∈ {x | δ < g x} from hx)]
      have he : g x ≤ g x ^ 2 / T + T := by
        calc
          g x ≤ (g x ^ 2 + T ^ 2) / T :=
            (le_div_iff₀ hT).mpr (by nlinarith [sq_nonneg (g x - T)])
          _ = g x ^ 2 / T + T := by field_simp; ring
      linarith
    · rw [Set.indicator_of_not_mem (show x ∉ {x | δ < g x} from hx)]
      linarith [div_nonneg (sq_nonneg (g x)) hT.le, le_of_not_gt hx]
  have hind : Integrable (Set.indicator {x | δ < g x} (fun _ => T)) μ :=
    (integrable_const T).indicator hs
  calc
    _ ≤ ∫ x, δ + g x ^ 2 / T + Set.indicator {x | δ < g x} (fun _ => T) x ∂μ :=
      integral_mono hi (((integrable_const δ).add (h2.div_const T)).add hind) hp
    _ = _ := by
      have he1 := integral_add ((integrable_const δ).add (h2.div_const T)) hind
      have he2 := integral_add (integrable_const δ) (h2.div_const T)
      simp only [Pi.add_apply] at he1 he2
      rw [he1, he2, integral_const,
        integral_div, integral_indicator hs, setIntegral_const]
      simp only [measureReal_univ_eq_one, one_smul, smul_eq_mul]
      ring

end GaussianWave

namespace GaussianWave

/-- Explicit near-diagonal coupling information. This property must be proved
by constructing couplings, for example from finite continuity partitions; it
is not included in the definition of weak convergence. -/
def CouplingsNearDiagonal {ι : Type*} [Fintype ι]
    {μ : ℕ → Measure (ι → ℝ)} {ν : Measure (ι → ℝ)}
    (γ : ∀ n, Coupling (μ n) ν) : Prop :=
  ∀ δ : ℝ, 0 < δ → Tendsto
    (fun n => (γ n).measure.real {z | δ < squareTransportCost z}) atTop (𝓝 0)

/-- Uniform fourth moments upgrade near-diagonal-in-probability couplings to
vanishing physical quadratic transport cost, for genuinely varying measures. -/
theorem integral_squareCost_tendsto_zero {ι : Type*} [Fintype ι]
    {μ : ℕ → Measure (ι → ℝ)} {ν : Measure (ι → ℝ)}
    [∀ n, IsProbabilityMeasure (μ n)]
    (γ : ∀ n, Coupling (μ n) ν)
    (hnear : CouplingsNearDiagonal γ)
    (hμ : ∀ n, Integrable (fun x => squareMass x ^ 2) (μ n))
    (hν : Integrable (fun x => squareMass x ^ 2) ν)
    (M : ℝ) (hM : ∀ n, (∫ x, squareMass x ^ 2 ∂μ n) ≤ M) :
    Tendsto (fun n => ∫ z, squareTransportCost z ∂(γ n).measure) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (integral_nonneg (fun x => sq_nonneg _)).trans (hM 0)
  let D := 8 * (M + ∫ x, squareMass x ^ 2 ∂ν)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbound (n : ℕ) : (∫ z, squareTransportCost z ^ 2 ∂(γ n).measure) ≤ D := by
    exact ((γ n).integral_squareCost_sq_le (hμ n) hν).trans (by dsimp [D]; linarith [hM n])
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε / 3
  let T := 3 * (D + 1) / ε
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have htail : D / T < ε / 3 := by
    apply (div_lt_iff₀ hT).mpr
    have he : ε * T = 3 * (D + 1) := by dsimp [T]; field_simp
    nlinarith
  have hmass := (tendsto_order.mp (hnear δ hδ)).2 (ε / (3 * T)) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmass
  refine ⟨N, fun n hn => ?_⟩
  have hb := integral_nonnegative_le_threshold (γ n).measure squareTransportCost
    continuous_squareTransportCost.measurable squareTransportCost_nonneg
    ((γ n).integrable_squareCost_sq (hμ n) hν) δ T hδ.le hT
  have ht : T * (γ n).measure.real {z | δ < squareTransportCost z} < ε / 3 := by
    have h := hN n hn
    have hp := mul_lt_mul_of_pos_left h hT
    have he : T * (ε / (3 * T)) = ε / 3 := by field_simp; ring
    rwa [he] at hp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (integral_nonneg (fun z => squareTransportCost_nonneg z))]
  have hbd := div_le_div_of_nonneg_right (hbound n) hT.le
  dsimp [δ] at hb
  linarith

/-- The preceding constructive couplings bound the actual infimum transport
cost. This theorem does not assume that the infimum is attained. -/
theorem wassersteinTwoSquared_tendsto_zero_of_near_couplings
    {ι : Type*} [Fintype ι]
    {μ : ℕ → Measure (ι → ℝ)} {ν : Measure (ι → ℝ)}
    [∀ n, IsProbabilityMeasure (μ n)]
    (γ : ∀ n, Coupling (μ n) ν) (hnear : CouplingsNearDiagonal γ)
    (hμ : ∀ n, Integrable (fun x => squareMass x ^ 2) (μ n))
    (hν : Integrable (fun x => squareMass x ^ 2) ν)
    (M : ℝ) (hM : ∀ n, (∫ x, squareMass x ^ 2 ∂μ n) ≤ M) :
    Tendsto (fun n => wassersteinTwoSquared (μ n) ν) atTop (𝓝 0) := by
  have hint := integral_squareCost_tendsto_zero γ hnear hμ hν M hM
  have hcost : Tendsto (fun n => quadraticCouplingCost (γ n)) atTop (𝓝 0) := by
    have heq (n : ℕ) : quadraticCouplingCost (γ n) =
        ENNReal.ofReal (∫ z, squareTransportCost z ∂(γ n).measure) := by
      exact (ofReal_integral_eq_lintegral_ofReal ((γ n).integrable_squareCost (hμ n) hν)
        (Eventually.of_forall squareTransportCost_nonneg)).symm
    simp_rw [heq]
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hint
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcost
    (fun _ => bot_le) (fun n => wassersteinTwoSquared_le_cost (γ n))

end GaussianWave

namespace GaussianWave

/-- Approximate couplings at arbitrary fixed accuracy. Every existential
witness is still a measure with the required marginals. -/
def ArbitrarilyNearCouplings {ι : Type*} [Fintype ι]
    (μ : ℕ → Measure (ι → ℝ)) (ν : Measure (ι → ℝ)) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
    ∃ γ : Coupling (μ n) ν,
      γ.measure.real {z | δ < squareTransportCost z} < η

/-- Fixed-accuracy couplings and fourth moments produce fixed-accuracy
quadratic-cost couplings. No representation theorem is used. -/
theorem eventually_exists_small_quadratic_coupling
    {ι : Type*} [Fintype ι]
    {μ : ℕ → Measure (ι → ℝ)} {ν : Measure (ι → ℝ)}
    [∀ n, IsProbabilityMeasure (μ n)]
    (hnear : ArbitrarilyNearCouplings μ ν)
    (hμ : ∀ n, Integrable (fun x => squareMass x ^ 2) (μ n))
    (hν : Integrable (fun x => squareMass x ^ 2) ν)
    (M : ℝ) (hM : ∀ n, (∫ x, squareMass x ^ 2 ∂μ n) ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ γ : Coupling (μ n) ν,
      (∫ z, squareTransportCost z ∂γ.measure) < ε := by
  have hM0 : 0 ≤ M := (integral_nonneg (fun x => sq_nonneg _)).trans (hM 0)
  let D := 8 * (M + ∫ x, squareMass x ^ 2 ∂ν)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let δ := ε / 3
  let T := 3 * (D + 1) / ε
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have htail : D / T < ε / 3 := by
    apply (div_lt_iff₀ hT).mpr
    have he : ε * T = 3 * (D + 1) := by dsimp [T]; field_simp
    nlinarith
  filter_upwards [hnear δ hδ (ε / (3 * T)) (by positivity)] with n hn
  obtain ⟨γ, hγ⟩ := hn
  refine ⟨γ, ?_⟩
  have hb := integral_nonnegative_le_threshold γ.measure squareTransportCost
    continuous_squareTransportCost.measurable squareTransportCost_nonneg
    (γ.integrable_squareCost_sq (hμ n) hν) δ T hδ.le hT
  have hbound : (∫ z, squareTransportCost z ^ 2 ∂γ.measure) ≤ D :=
    (γ.integral_squareCost_sq_le (hμ n) hν).trans (by dsimp [D]; linarith [hM n])
  have ht : T * γ.measure.real {z | δ < squareTransportCost z} < ε / 3 := by
    have hp := mul_lt_mul_of_pos_left hγ hT
    have he : T * (ε / (3 * T)) = ε / 3 := by field_simp; ring
    rwa [he] at hp
  have hbd := div_le_div_of_nonneg_right hbound hT.le
  dsimp [δ] at hb
  linarith

/-- Genuine squared Wasserstein convergence follows from fixed-accuracy
couplings and fourth moments; no optimal coupling is assumed to exist. -/
theorem wassersteinTwoSquared_tendsto_zero_of_arbitrarily_near_couplings
    {ι : Type*} [Fintype ι]
    {μ : ℕ → Measure (ι → ℝ)} {ν : Measure (ι → ℝ)}
    [∀ n, IsProbabilityMeasure (μ n)]
    (hnear : ArbitrarilyNearCouplings μ ν)
    (hμ : ∀ n, Integrable (fun x => squareMass x ^ 2) (μ n))
    (hν : Integrable (fun x => squareMass x ^ 2) ν)
    (M : ℝ) (hM : ∀ n, (∫ x, squareMass x ^ 2 ∂μ n) ≤ M) :
    Tendsto (fun n => wassersteinTwoSquared (μ n) ν) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨r, hr0, hrpos, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hr : 0 < r := ENNReal.ofReal_pos.mp hrpos
  filter_upwards [eventually_exists_small_quadratic_coupling hnear hμ hν M hM r hr]
    with n hn
  obtain ⟨γ, hγ⟩ := hn
  apply (wassersteinTwoSquared_le_cost γ).trans
  have heq : quadraticCouplingCost γ =
      ENNReal.ofReal (∫ z, squareTransportCost z ∂γ.measure) :=
    (ofReal_integral_eq_lintegral_ofReal (γ.integrable_squareCost (hμ n) hν)
      (Eventually.of_forall squareTransportCost_nonneg)).symm
  rw [heq]
  exact (ENNReal.ofReal_le_ofReal hγ.le).trans hrε.le

/-- The actual extended Wasserstein distance is the square root of the
infimum quadratic cost. -/
def wassersteinTwo {ι : Type*} [Fintype ι]
    (μ ν : Measure (ι → ℝ)) : ℝ≥0∞ :=
  wassersteinTwoSquared μ ν ^ (1 / 2 : ℝ)

theorem wassersteinTwo_tendsto_zero_of_squared
    {ι : Type*} [Fintype ι] {μ : ℕ → Measure (ι → ℝ)} {ν : Measure (ι → ℝ)}
    (h : Tendsto (fun n => wassersteinTwoSquared (μ n) ν) atTop (𝓝 0)) :
    Tendsto (fun n => wassersteinTwo (μ n) ν) atTop (𝓝 0) := by
  have ht := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞)
  have hh := ht.comp h
  simpa only [wassersteinTwo, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hh

end GaussianWave

namespace GaussianWave

/-- Small diameter for the usual finite-function metric implies small physical
Euclidean squared distance with the explicit dimension factor. -/
theorem squareTransportCost_le_card_mul_dist_sq {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    squareTransportCost (x, y) ≤ (Fintype.card ι : ℝ) * dist x y ^ 2 := by
  calc
    _ ≤ ∑ _i : ι, dist x y ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have h := norm_le_pi_norm (x - y) i
      have h' : |x i - y i| ≤ dist x y := by
        simpa only [Real.norm_eq_abs, Pi.sub_apply, dist_eq_norm] using h
      change (x i - y i) ^ 2 ≤ dist x y ^ 2
      nlinarith [abs_nonneg (x i - y i), (show 0 ≤ dist x y from dist_nonneg), sq_abs (x i - y i)]
    _ = _ := by simp

/-- Finite fourth marginals give a finite actual squared Wasserstein cost. -/
theorem wassersteinTwoSquared_ne_top {ι : Type*} [Fintype ι]
    (μ ν : Measure (ι → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x => squareMass x ^ 2) μ)
    (hν : Integrable (fun x => squareMass x ^ 2) ν) :
    wassersteinTwoSquared μ ν ≠ ⊤ := by
  let γ := Coupling.independent μ ν
  have heq : quadraticCouplingCost γ =
      ENNReal.ofReal (∫ z, squareTransportCost z ∂γ.measure) :=
    (ofReal_integral_eq_lintegral_ofReal (γ.integrable_squareCost hμ hν)
      (Eventually.of_forall squareTransportCost_nonneg)).symm
  exact ne_top_of_le_ne_top (by rw [heq]; exact ENNReal.ofReal_ne_top)
    (wassersteinTwoSquared_le_cost γ)

/-- Convergence of the infimum transport cost supplies an actual sequence of
couplings with cost tending to zero; there is no assumed optimizer. -/
theorem exists_couplings_cost_tendsto_zero_of_wasserstein
    {ι : Type*} [Fintype ι]
    (μ : ℕ → Measure (ι → ℝ)) (ν : Measure (ι → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hμ : ∀ n, Integrable (fun x => squareMass x ^ 2) (μ n))
    (hν : Integrable (fun x => squareMass x ^ 2) ν)
    (hw : Tendsto (fun n => wassersteinTwoSquared (μ n) ν) atTop (𝓝 0)) :
    ∃ γ : ∀ n, Coupling (μ n) ν,
      Tendsto (fun n => quadraticCouplingCost (γ n)) atTop (𝓝 0) := by
  have heps (n : ℕ) : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    apply ENNReal.ofReal_pos.mpr
    positivity
  have hex (n : ℕ) : ∃ γ : Coupling (μ n) ν,
      quadraticCouplingCost γ < wassersteinTwoSquared (μ n) ν +
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    apply iInf_lt_iff.mp
    exact ENNReal.lt_add_right (wassersteinTwoSquared_ne_top (μ n) ν (hμ n) hν)
      (ne_of_gt (heps n))
  choose γ hγ using hex
  refine ⟨γ, ?_⟩
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hu := hw.add (by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hinv)
  have hu' : Tendsto (fun n => wassersteinTwoSquared (μ n) ν +
      ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by simpa using hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu'
    (fun _ => bot_le) (fun n => (hγ n).le)

end GaussianWave

namespace GaussianWave

/-- Fixed-accuracy near-diagonal couplings for two varying laws. -/
def ArbitrarilyNearCouplingsTwo {ι : Type*} [Fintype ι]
    (μ ν : ℕ → Measure (ι → ℝ)) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
    ∃ γ : Coupling (μ n) (ν n),
      γ.measure.real {z | δ < squareTransportCost z} < η

theorem eventually_exists_small_quadratic_coupling_two
    {ι : Type*} [Fintype ι] {μ ν : ℕ → Measure (ι → ℝ)}
    [∀ n, IsProbabilityMeasure (μ n)]
    (hnear : ArbitrarilyNearCouplingsTwo μ ν)
    (hμ : ∀ n, Integrable (fun x => squareMass x ^ 2) (μ n))
    (hν : ∀ n, Integrable (fun x => squareMass x ^ 2) (ν n))
    (M L : ℝ)
    (hM : ∀ n, (∫ x, squareMass x ^ 2 ∂μ n) ≤ M)
    (hL : ∀ n, (∫ x, squareMass x ^ 2 ∂ν n) ≤ L)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ γ : Coupling (μ n) (ν n),
      (∫ z, squareTransportCost z ∂γ.measure) < ε := by
  have hM0 : 0 ≤ M := (integral_nonneg (fun x => sq_nonneg _)).trans (hM 0)
  have hL0 : 0 ≤ L := (integral_nonneg (fun x => sq_nonneg _)).trans (hL 0)
  let D := 8 * (M + L)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let δ := ε / 3
  let T := 3 * (D + 1) / ε
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have htail : D / T < ε / 3 := by
    apply (div_lt_iff₀ hT).mpr
    have he : ε * T = 3 * (D + 1) := by dsimp [T]; field_simp
    nlinarith
  filter_upwards [hnear δ hδ (ε / (3 * T)) (by positivity)] with n hn
  obtain ⟨γ, hγ⟩ := hn
  refine ⟨γ, ?_⟩
  have hb := integral_nonnegative_le_threshold γ.measure squareTransportCost
    continuous_squareTransportCost.measurable squareTransportCost_nonneg
    (γ.integrable_squareCost_sq (hμ n) (hν n)) δ T hδ.le hT
  have hbound : (∫ z, squareTransportCost z ^ 2 ∂γ.measure) ≤ D :=
    (γ.integral_squareCost_sq_le (hμ n) (hν n)).trans (by dsimp [D]; linarith [hM n, hL n])
  have ht : T * γ.measure.real {z | δ < squareTransportCost z} < ε / 3 := by
    have hp := mul_lt_mul_of_pos_left hγ hT
    have he : T * (ε / (3 * T)) = ε / 3 := by field_simp; ring
    rwa [he] at hp
  have hbd := div_le_div_of_nonneg_right hbound hT.le
  dsimp [δ] at hb
  linarith

theorem wassersteinTwoSquared_tendsto_zero_of_arbitrarily_near_couplings_two
    {ι : Type*} [Fintype ι] {μ ν : ℕ → Measure (ι → ℝ)}
    [∀ n, IsProbabilityMeasure (μ n)]
    (hnear : ArbitrarilyNearCouplingsTwo μ ν)
    (hμ : ∀ n, Integrable (fun x => squareMass x ^ 2) (μ n))
    (hν : ∀ n, Integrable (fun x => squareMass x ^ 2) (ν n))
    (M L : ℝ)
    (hM : ∀ n, (∫ x, squareMass x ^ 2 ∂μ n) ≤ M)
    (hL : ∀ n, (∫ x, squareMass x ^ 2 ∂ν n) ≤ L) :
    Tendsto (fun n => wassersteinTwoSquared (μ n) (ν n)) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨r, _, hrpos, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hr : 0 < r := ENNReal.ofReal_pos.mp hrpos
  filter_upwards [eventually_exists_small_quadratic_coupling_two hnear hμ hν M L hM hL r hr]
    with n hn
  obtain ⟨γ, hγ⟩ := hn
  apply (wassersteinTwoSquared_le_cost γ).trans
  have heq : quadraticCouplingCost γ =
      ENNReal.ofReal (∫ z, squareTransportCost z ∂γ.measure) :=
    (ofReal_integral_eq_lintegral_ofReal (γ.integrable_squareCost (hμ n) (hν n))
      (Eventually.of_forall squareTransportCost_nonneg)).symm
  rw [heq]
  exact (ENNReal.ofReal_le_ofReal hγ.le).trans hrε.le

theorem wassersteinTwo_tendsto_zero_of_squared_two
    {ι : Type*} [Fintype ι] {μ ν : ℕ → Measure (ι → ℝ)}
    (h : Tendsto (fun n => wassersteinTwoSquared (μ n) (ν n)) atTop (𝓝 0)) :
    Tendsto (fun n => wassersteinTwo (μ n) (ν n)) atTop (𝓝 0) := by
  have ht := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞)
  have hh := ht.comp h
  simpa only [wassersteinTwo, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hh

end GaussianWave

namespace GaussianWave

/-- Approximate minimizers produce a genuine coupling sequence for two
varying marginals. The minimizing couplings need not exist. -/
theorem exists_couplings_cost_tendsto_zero_of_wasserstein_two
    {ι : Type*} [Fintype ι]
    (μ ν : ℕ → Measure (ι → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (hμ : ∀ n, Integrable (fun x => squareMass x ^ 2) (μ n))
    (hν : ∀ n, Integrable (fun x => squareMass x ^ 2) (ν n))
    (hw : Tendsto (fun n => wassersteinTwoSquared (μ n) (ν n)) atTop (𝓝 0)) :
    ∃ γ : ∀ n, Coupling (μ n) (ν n),
      Tendsto (fun n => quadraticCouplingCost (γ n)) atTop (𝓝 0) := by
  have heps (n : ℕ) : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    apply ENNReal.ofReal_pos.mpr
    positivity
  have hex (n : ℕ) : ∃ γ : Coupling (μ n) (ν n),
      quadraticCouplingCost γ < wassersteinTwoSquared (μ n) (ν n) +
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    apply iInf_lt_iff.mp
    exact ENNReal.lt_add_right (wassersteinTwoSquared_ne_top (μ n) (ν n) (hμ n) (hν n))
      (ne_of_gt (heps n))
  choose γ hγ using hex
  refine ⟨γ, ?_⟩
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hu := hw.add (by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hinv)
  have hu' : Tendsto (fun n => wassersteinTwoSquared (μ n) (ν n) +
      ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by simpa using hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu'
    (fun _ => bot_le) (fun n => (hγ n).le)

end GaussianWave
