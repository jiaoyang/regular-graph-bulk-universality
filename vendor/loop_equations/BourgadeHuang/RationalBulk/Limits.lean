import BourgadeHuang.AnchoredSequenceCompactness
import BourgadeHuang.RationalBulk.FactorialMoments

/-! Arbitrary absolute-error Nevanlinna hierarchies have genuine subsequential
laws satisfying every exact loop equation and exponential anchor bounds. -/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem VanishingHierarchy.comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {β : ℝ}
    {X : ℕ → Ω → AnchoredCountingState} (h : VanishingHierarchy μ β X)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) :
    VanishingHierarchy μ β (fun N => X (r N)) := by
  intro n w hw aux haux
  exact (h n w hw aux haux).comp hr

theorem exactHierarchy_of_anchored_sequence_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (β : ℝ) (X : ℕ → Ω → AnchoredCountingState) (hX : ∀N,Measurable (X N))
    (hm : ∀N q : ℕ,Integrable (fun ω => ‖(X N ω).val.2‖^q) μ)
    (h : VanishingHierarchy μ β X)
    (ν : ProbabilityMeasure AnchoredCountingState)
    (hw : WeakLawConverges μ X (ν : Measure AnchoredCountingState)) :
    ExactHierarchy (ν : Measure AnchoredCountingState) β := by
  intro n w hw0 aux haux
  obtain ⟨C,hC,hb⟩ := growth_loopIntegrand β hw0 haux
  obtain ⟨M,hM⟩ := uniform_anchor_moments_of_vanishingHierarchy μ β X hX hm h (2*(n+2))
  have ht := hw.integral_complex_of_polynomial_growth hX
    (fun s => loopIntegrand β s w aux) (continuous_loopIntegrand β hw0 haux)
    (fun s => ‖s.val.2‖) C hC (n+2) (fun s => by simpa only [abs_norm] using hb s)
    (fun N => by simpa only [abs_norm] using hm N (2*(n+2))) M
    (fun N => by simpa only [abs_norm] using hM N)
  exact ⟨ht.1,tendsto_nhds_unique ht.2 (h n w hw0 aux haux)⟩

theorem exponential_anchor_of_anchored_sequence_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (β : ℝ) (X : ℕ → Ω → AnchoredCountingState) (hX : ∀N,Measurable (X N))
    (hm : ∀N q : ℕ,Integrable (fun ω => ‖(X N ω).val.2‖^q) μ)
    (h : VanishingHierarchy μ β X)
    (ν : ProbabilityMeasure AnchoredCountingState)
    (hw : WeakLawConverges μ X (ν : Measure AnchoredCountingState)) :
    ∃a : ℝ,0 < a ∧ Integrable
      (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) (ν : Measure AnchoredCountingState) := by
  obtain ⟨C,hC,hb⟩ := eventually_factorial_anchor_moments_of_vanishingHierarchy μ β X hX hm h
  have ht (q : ℕ) : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖^(2*q))
      (ν : Measure AnchoredCountingState) ∧
      (∫s : AnchoredCountingState,‖s.val.2‖^(2*q) ∂ν) ≤ C^q*(q.factorial:ℝ) := by
    obtain ⟨M,hM⟩ := uniform_anchor_moments_of_vanishingHierarchy μ β X hX hm h (2*(2*q))
    have hs := hw.integral_norm_pow hX (fun s => s.val.2)
      (continuous_snd.comp continuous_subtype_val) (2*q) (fun N => hm N _) M hM
    exact ⟨hs.1,le_of_tendsto hs.2 (hb q)⟩
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨(2*C)⁻¹,by positivity,?_⟩
  apply integrable_exp_sq_of_factorial_moments (ν : Measure AnchoredCountingState)
    (fun s => ‖s.val.2‖) (continuous_snd.comp continuous_subtype_val).norm.measurable.aestronglyMeasurable
    hCpos.le (by positivity) _ (fun q => (ht q).1) (fun q => (ht q).2)
  have he : (2*C)⁻¹*C = (1/2:ℝ) := by field_simp; ring
  rw [he]
  norm_num

theorem exists_exact_anchored_subsequence_of_vanishingHierarchy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (β : ℝ) (X : ℕ → Ω → AnchoredCountingState) (hX : ∀N,Measurable (X N))
    (hm : ∀N q : ℕ,Integrable (fun ω => ‖(X N ω).val.2‖^q) μ)
    (h : VanishingHierarchy μ β X) :
    ∃(ν : ProbabilityMeasure AnchoredCountingState) (r : ℕ → ℕ),StrictMono r ∧
      WeakLawConverges μ (fun N => X (r N)) (ν : Measure AnchoredCountingState) ∧
      ExactHierarchy (ν : Measure AnchoredCountingState) β ∧
      ∃a : ℝ,0 < a ∧ Integrable
        (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) (ν : Measure AnchoredCountingState) := by
  obtain ⟨ν,r,hr,hw⟩ := exists_anchored_subsequence_of_uniform_anchor_moments μ X hX hm
    (uniform_anchor_moments_of_vanishingHierarchy μ β X hX hm h)
  exact ⟨ν,r,hr,hw,
    exactHierarchy_of_anchored_sequence_limit μ β _ (fun N => hX (r N))
      (fun N q => hm (r N) q) (h.comp hr.tendsto_atTop) ν hw,
    exponential_anchor_of_anchored_sequence_limit μ β _ (fun N => hX (r N))
      (fun N q => hm (r N) q) (h.comp hr.tendsto_atTop) ν hw⟩

end BourgadeHuang.RationalBulk
