import GeneralizedBulk.Gaussian.MarkFamily
import GeneralizedBulk.Gaussian.Presentation
import GeneralizedBulk.Analysis.SummableRandom

/-! A measurable common event for all analytic Gaussian mark corrections. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators NNReal ENNReal

namespace GeneralizedBulk.Gaussian

def quadraticSize (p : ℝ) (y : Fin 4 → ℝ) : ℝ :=
  ∑ ij : Fin 4 × Fin 4, |rawQuadratic p ij.1 ij.2 y|

theorem quadraticSize_nonneg (p : ℝ) (y : Fin 4 → ℝ) : 0 ≤ quadraticSize p y :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem measurable_quadraticSize (p : ℝ) : Measurable (quadraticSize p) :=
  Finset.measurable_sum _ (fun ij _ => (measurable_rawQuadratic p ij.1 ij.2).abs)

theorem integrable_quadraticSize (p : ℝ) : Integrable (quadraticSize p) (markLaw p) := by
  apply integrable_finset_sum
  intro ij _
  simpa only [pow_one] using (integrable_rawQuadratic_pow p ij.1 ij.2 1).norm

theorem abs_rawQuadratic_le_size (p : ℝ) (y : Fin 4 → ℝ) (i j : Fin 4) :
    |rawQuadratic p i j y| ≤ quadraticSize p y := by
  change |rawQuadratic p i j y| ≤ ∑ ij : Fin 4 × Fin 4, |rawQuadratic p ij.1 ij.2 y|
  exact Finset.single_le_sum (fun (ij : Fin 4 × Fin 4) _ => abs_nonneg (rawQuadratic p ij.1 ij.2 y))
    (Finset.mem_univ (i, j))

def weightedEvent {ι S : Type*} (X : S → PresentedState ι) (p : ℝ) :
    Set (S × (ι → (Fin 4 → ℝ))) :=
  {z | Summable (fun i => nevanlinnaWeight ((X z.1).location i) * quadraticSize p (z.2 i))}

theorem measurableSet_weightedEvent
    {ι S : Type*} [Countable ι] [MeasurableSpace S]
    (X : S → PresentedState ι) (hX : Measurable X) (p : ℝ) :
    MeasurableSet (weightedEvent X p) := by
  let F : ι → (S × (ι → (Fin 4 → ℝ))) → ℝ := fun i z =>
    nevanlinnaWeight ((X z.1).location i) * quadraticSize p (z.2 i)
  have hpos (i : ι) (z : S × (ι → (Fin 4 → ℝ))) : 0 ≤ F i z :=
    mul_nonneg (nevanlinnaWeight_nonneg _) (quadraticSize_nonneg _ _)
  have hm (i : ι) : Measurable (F i) :=
    ((continuous_nevanlinnaWeight.measurable.comp
      ((PresentedState.measurable_location i).comp hX)).comp measurable_fst).mul
      ((measurable_quadraticSize p).comp ((measurable_pi_apply i).comp measurable_snd))
  have hnn : Measurable (fun z => ∑' i, ENNReal.ofReal (F i z)) :=
    Measurable.ennreal_tsum (fun i => (hm i).ennreal_ofReal)
  have hcriterion (z : S × (ι → (Fin 4 → ℝ))) :
      (∑' i, ENNReal.ofReal (F i z)) < ∞ ↔ Summable (fun i => F i z) := by
    have hh := ENNReal.tsum_coe_ne_top_iff_summable_coe
      (f := fun i => Real.toNNReal (F i z))
    simpa only [lt_top_iff_ne_top, ENNReal.ofReal, Real.coe_toNNReal _ (hpos _ _)] using hh
  convert measurableSet_lt hnn measurable_const using 1
  ext z
  exact (hcriterion z).symm

theorem ae_weightedEvent
    {ι S : Type*} [Countable ι] [MeasurableSpace S]
    (P : Measure S) [SFinite P] (X : S → PresentedState ι) (hX : Measurable X) (p : ℝ) :
    ∀ᵐ z ∂P.prod (iidLaw (markLaw p) ι), z ∈ weightedEvent X p := by
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_weightedEvent X hX p)).2
  apply Filter.Eventually.of_forall
  intro x
  let F : ι → (ι → (Fin 4 → ℝ)) → ℂ := fun i ω => (quadraticSize p (ω i) : ℂ)
  have hi (i : ι) : Integrable (F i) (iidLaw (markLaw p) ι) := by
    have hreal : Integrable (fun ω : ι → (Fin 4 → ℝ) => quadraticSize p (ω i))
        (iidLaw (markLaw p) ι) :=
      ((iidLaw_eval_measurePreserving (markLaw p) ι i).integrable_comp
        (measurable_quadraticSize p).aestronglyMeasurable).2 (integrable_quadraticSize p)
    exact hreal.ofReal
  have heq (i : ι) : (∫ ω, ‖F i ω‖ ∂iidLaw (markLaw p) ι) =
      ∫ y, quadraticSize p y ∂markLaw p := by
    simp only [F, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (quadraticSize_nonneg _ _)]
    exact integral_iid_eval (markLaw p) ι i _ (measurable_quadraticSize p).aestronglyMeasurable
  have hs := GeneralizedBulk.Analysis.ae_weighted_summable
    (iidLaw (markLaw p) ι) F (fun i => nevanlinnaWeight ((X x).location i))
    (∫ y, quadraticSize p y ∂markLaw p) hi
    (fun i => nevanlinnaWeight_nonneg _) (X x).presentation.summable_weight
    (fun i => (heq i).le)
  simpa only [weightedEvent, Set.mem_setOf_eq, F, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (quadraticSize_nonneg _ _)] using hs

theorem weightedEvent_entry_summable
    {ι S : Type*} {X : S → PresentedState ι} {p : ℝ}
    {z : S × (ι → (Fin 4 → ℝ))} (hz : z ∈ weightedEvent X p) (i j : Fin 4) :
    Summable (fun n => nevanlinnaWeight ((X z.1).location n) *
      ‖(rawQuadratic p i j (z.2 n) : ℂ)‖) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (nevanlinnaWeight_nonneg _) (norm_nonneg _)) _ hz
  intro n
  simp only [Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_rawQuadratic_le_size p (z.2 n) i j) (nevanlinnaWeight_nonneg _)

end GeneralizedBulk.Gaussian
