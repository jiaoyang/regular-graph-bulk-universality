import GeneralizedBulk.Analysis.TruncationConvergence
import GeneralizedBulk.Analysis.GoodFiberMoments

/-! Genuine good-event second moments imply the probability-tail inputs
used by the full weak-law truncation theorem. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace GeneralizedBulk.Analysis
variable {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem dist_failure_probability_le_good_second (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y)
    (good : Set Ω) (hgood : MeasurableSet good)
    (hi : IntegrableOn (fun x => dist (X x) (Y x)^2) good P) (V ε : ℝ)
    (hV : (∫ x in good,dist (X x) (Y x)^2 ∂P) ≤ V) (hε : 0 < ε) :
    P.real {x | ε < dist (X x) (Y x)} ≤ P.real goodᶜ + V/ε^2 := by
  let tail := {x | ε^2 ≤ dist (X x) (Y x)^2}
  have htail : MeasurableSet tail := measurableSet_le measurable_const ((hX.dist hY).pow_const 2)
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := P.restrict good)
    (Eventually.of_forall (fun x => sq_nonneg (dist (X x) (Y x)))) hi (ε^2)
  have ht : P.real (tail ∩ good) ≤ V/ε^2 := by
    rw [← measureReal_restrict_apply htail]
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    simpa only [mul_comm] using hm.trans hV
  have hsub : {x | ε < dist (X x) (Y x)} ⊆ (tail ∩ good) ∪ goodᶜ := by
    intro x hx
    by_cases hg : x ∈ good
    · left
      refine ⟨?_,hg⟩
      exact (sq_lt_sq₀ hε.le (dist_nonneg)).mpr hx |>.le
    · exact Or.inr hg
  have hb := (measureReal_mono (μ := P) hsub).trans (measureReal_union_le _ _)
  linarith

theorem dist_failure_probability_le_second (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y)
    (hi : Integrable (fun x => dist (X x) (Y x)^2) P) (V ε : ℝ)
    (hV : (∫ x,dist (X x) (Y x)^2 ∂P) ≤ V) (hε : 0 < ε) :
    P.real {x | ε < dist (X x) (Y x)} ≤ V/ε^2 := by
  have hh := dist_failure_probability_le_good_second P X Y hX hY univ MeasurableSet.univ
    (by simpa only [IntegrableOn,Measure.restrict_univ] using hi) V ε (by simpa using hV) hε
  simpa using hh

theorem truncation_probability_tails_of_good_second
    {ΩN : ℕ → Type*} [∀ n,MeasurableSpace (ΩN n)]
    (P : ∀ n,Measure (ΩN n)) [∀ n,IsProbabilityMeasure (P n)]
    (X : ∀ n,ΩN n → E) (XR : ℕ → ∀ n,ΩN n → E)
    (hX : ∀ n,Measurable (X n)) (hXR : ∀ R n,Measurable (XR R n))
    (good : ∀ n,Set (ΩN n)) (hgood : ∀ n,MeasurableSet (good n))
    (hbad : Tendsto (fun n => (P n).real (good n)ᶜ) atTop (𝓝 0))
    (v : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝 0))
    (hv : ∀ R,Tendsto (v R) atTop (𝓝 (b R)))
    (hmoment : ∀ R,∀ᶠ n in atTop,
      IntegrableOn (fun x => dist (X n x) (XR R n x)^2) (good n) (P n) ∧
        (∫ x in good n,dist (X n x) (XR R n x)^2 ∂P n) ≤ v R n) :
    ∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∃ R0,∀ R,R0 ≤ R → ∀ᶠ n in atTop,(P n).real {x | ε < dist (X n x) (XR R n x)} ≤ δ := by
  intro ε δ hε hδ
  have hb' := hb.div_const (ε^2)
  have hsmall := (tendsto_order.mp hb').2 (δ/2) (by simpa using half_pos hδ)
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp hsmall
  refine ⟨R0,fun R hR => ?_⟩
  have ht := hbad.add ((hv R).div_const (ε^2))
  have hlt : 0+b R/ε^2 < δ := by have := hR0 R hR; linarith
  filter_upwards [hmoment R,(tendsto_order.mp ht).2 δ hlt] with n hn hnb
  exact (dist_failure_probability_le_good_second (P n) (X n) (XR R n) (hX n) (hXR R n)
    (good n) (hgood n) hn.1 (v R n) ε hn.2 hε).trans hnb.le

theorem target_probability_of_second_tendsto_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (Y : Ω → E) (hX : ∀ R,Measurable (X R)) (hY : Measurable Y)
    (hi : ∀ R,Integrable (fun x => dist (X R x) (Y x)^2) P)
    (hL2 : Tendsto (fun R => ∫ x,dist (X R x) (Y x)^2 ∂P) atTop (𝓝 0)) :
    ∀ ε δ : ℝ,0 < ε → 0 < δ → ∀ᶠ R in atTop,P.real {x | ε < dist (X R x) (Y x)} ≤ δ := by
  intro ε δ hε hδ
  have ht := hL2.div_const (ε^2)
  filter_upwards [(tendsto_order.mp ht).2 δ (by simpa using hδ)] with R hR
  exact (dist_failure_probability_le_second P (X R) Y (hX R) hY (hi R) _ ε le_rfl hε).trans hR.le

theorem dist_pi_sq_le_sum_sq {ι : Type*} [Fintype ι] (X Y : ι → E) :
    dist X Y^2 ≤ ∑ i,dist (X i) (Y i)^2 := by
  have hs : 0 ≤ ∑ i,dist (X i) (Y i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb : dist X Y ≤ Real.sqrt (∑ i,dist (X i) (Y i)^2) := by
    apply (dist_pi_le_iff (Real.sqrt_nonneg _)).mpr
    intro i
    have hi := Finset.single_le_sum (f := fun j => dist (X j) (Y j)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    apply (sq_le_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hs]
    exact hi
  have hh := pow_le_pow_left₀ dist_nonneg hb 2
  simpa only [Real.sq_sqrt hs] using hh

theorem pi_good_second_of_coordinate_seconds {ι : Type*} [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ι → E) (hX : Measurable X) (hY : Measurable Y)
    (good : Set Ω) (hi : ∀ i,IntegrableOn (fun x => dist (X x i) (Y x i)^2) good P)
    (V : ι → ℝ) (hV : ∀ i,(∫ x in good,dist (X x i) (Y x i)^2 ∂P) ≤ V i) :
    IntegrableOn (fun x => dist (X x) (Y x)^2) good P ∧
      (∫ x in good,dist (X x) (Y x)^2 ∂P) ≤ ∑ i,V i := by
  have hsum : Integrable (fun x => ∑ i,dist (X x i) (Y x i)^2) (P.restrict good) :=
    integrable_finset_sum _ (fun i _ => hi i)
  have hwhole : IntegrableOn (fun x => dist (X x) (Y x)^2) good P :=
    hsum.mono' ((hX.dist hY).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact dist_pi_sq_le_sum_sq (X x) (Y x)))
  refine ⟨hwhole,?_⟩
  calc
    _ ≤ ∫ x in good,∑ i,dist (X x i) (Y x i)^2 ∂P := integral_mono hwhole hsum (fun x => dist_pi_sq_le_sum_sq _ _)
    _ = ∑ i,∫ x in good,dist (X x i) (Y x i)^2 ∂P := integral_finset_sum _ (fun i _ => hi i)
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hV i)

theorem pi_dist_failure_probability_le_good_seconds {ι : Type*} [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ι → E) (hX : Measurable X) (hY : Measurable Y)
    (good : Set Ω) (hgood : MeasurableSet good)
    (hi : ∀ i,IntegrableOn (fun x => dist (X x i) (Y x i)^2) good P)
    (V : ι → ℝ) (hV : ∀ i,(∫ x in good,dist (X x i) (Y x i)^2 ∂P) ≤ V i) (ε : ℝ) (hε : 0 < ε) :
    P.real {x | ε < dist (X x) (Y x)} ≤ P.real goodᶜ + (∑ i,V i)/ε^2 := by
  have hh := pi_good_second_of_coordinate_seconds P X Y hX hY good hi V hV
  exact dist_failure_probability_le_good_second P X Y hX hY good hgood hh.1 _ ε hh.2 hε

end GeneralizedBulk.Analysis
