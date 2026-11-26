import GeneralizedBulk.Analysis.GoodFiberMoments

/-! Conditional first moments transfer tightness of scalar anchors to
nonnegative marked envelopes, without uncapped scalar moment assumptions. -/
noncomputable section
open MeasureTheory Filter Set
namespace GeneralizedBulk.Analysis

theorem uniform_tails_of_conditional_first_bound
    {S T : ℕ → Type*} [∀ n,MeasurableSpace (S n)] [∀ n,MeasurableSpace (T n)]
    (P : ∀ n,Measure (S n)) [∀ n,IsProbabilityMeasure (P n)]
    (Q : ∀ n,Measure (T n)) [∀ n,IsProbabilityMeasure (Q n)]
    (g : ∀ n,S n → ℝ) (hg : ∀ n,Measurable (g n))
    (f : ∀ n,S n × T n → ℝ) (hf : ∀ n,Measurable (f n))
    (hf0 : ∀ n z,0 ≤ f n z) (C : ℝ) (hC : 0 ≤ C)
    (hsection : ∀ n s,Integrable (fun t => f n (s,t)) (Q n))
    (hbound : ∀ n s,(∫ t,f n (s,t) ∂Q n) ≤ C*g n s)
    (htight : ∀ δ : ℝ,0 < δ → ∃ A : ℝ,0 < A ∧
      ∀ n,(P n).real {s | A < g n s} ≤ δ) :
    ∀ δ : ℝ,0 < δ → ∃ B : ℝ,0 < B ∧
      ∀ n,((P n).prod (Q n)).real {z | B < f n z} ≤ δ := by
  intro δ hδ
  obtain ⟨A,hA,hAt⟩ := htight (δ/2) (by linarith)
  let B := 1+2*C*A/δ
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,fun n => ?_⟩
  let good := {s | g n s≤A}
  have hgood : MeasurableSet good := measurableSet_le (hg n) measurable_const
  have hi := integrableOn_prod_good_of_fiber_bound (P n) (Q n) good hgood (f n) (hf n)
    (hf0 n) (C*A) (mul_nonneg hC hA.le) (fun s hs => hsection n s)
    (fun s hs => (hbound n s).trans (mul_le_mul_of_nonneg_left hs hC))
  let tail := {z | B≤f n z}
  have htail : MeasurableSet tail := measurableSet_le measurable_const (hf n)
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := ((P n).prod (Q n)).restrict (good ×ˢ univ))
    (ae_of_all _ (hf0 n)) hi.1 B
  have hlocal : ((P n).prod (Q n)).real (tail ∩ (good ×ˢ univ)) ≤ C*A/B := by
    rw [← measureReal_restrict_apply htail]
    apply (le_div_iff₀ hB).mpr
    simpa only [mul_comm] using hm.trans hi.2
  have hsub : {z | B<f n z} ⊆ (tail ∩ (good ×ˢ univ)) ∪ (good ×ˢ univ)ᶜ := by
    intro z hz
    change B<f n z at hz
    by_cases hg : z ∈ good ×ˢ univ
    · exact Or.inl ⟨hz.le,hg⟩
    · exact Or.inr hg
  have hbad : ((P n).prod (Q n)).real (good ×ˢ univ)ᶜ ≤ δ/2 := by
    rw [product_good_failure_mass]
    simpa only [good,compl_setOf,not_le] using hAt n
  have hfrac : C*A/B ≤ δ/2 := by
    apply (div_le_iff₀ hB).mpr
    have he : B*δ=δ+2*C*A := by dsimp [B]; field_simp
    rw [div_mul_eq_mul_div,le_div_iff₀ (by norm_num : (0 : ℝ)<2)]
    calc
      C*A*2 ≤ δ+2*C*A := by linarith
      _ = δ*B := by rw [mul_comm δ B,he]
  have hb := (measureReal_mono (μ := (P n).prod (Q n)) hsub).trans (measureReal_union_le _ _)
  linarith

end GeneralizedBulk.Analysis
