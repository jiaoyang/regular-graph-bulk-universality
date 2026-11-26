import GeneralizedBulk.Analysis.GoodFiberIntegral
import GeneralizedBulk.Analysis.CappedMomentTransfer

/-! Conditional truncation variances and finite good-event scalar caps yield
actual two-step probability tails, without uncapped finite scalar moments. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace GeneralizedBulk.Analysis

set_option maxHeartbeats 2500000 in
theorem truncation_probability_le_capped_scalar
    {Ω T V : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    [Finite T] [MeasurableSingletonClass T] [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure T) [IsProbabilityMeasure Q]
    (good : Set Ω) (hgood : MeasurableSet good) (f : Ω → ℝ) (hf : Measurable f) (hf0 : ∀ ω,0 ≤ f ω)
    (cap C a v cutoff ε : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hcut : 0 < cutoff) (hε : 0 < ε) (hcap : cutoff ≤ cap)
    (hfirst : (∫ ω,good.indicator (fun ω => min (f ω) cap) ω ∂P) ≤ C)
    (e : Ω × T → V) (he : Measurable e) (o : Ω → ℝ) (ho : Integrable o P) (ho0 : ∀ ω,0 ≤ o ω)
    (hvariance : ∀ ω ∈ good,(∫ t,‖e (ω,t)‖^2 ∂Q) ≤ a*f ω+v+2*o ω) :
    (P.prod Q).real {z | ε < ‖e z‖} ≤ P.real goodᶜ+C/cutoff+
      (a*cutoff+|v|+2*(∫ ω,o ω ∂P))/ε^2 := by
  let Y := good.indicator (fun ω => min (f ω) cap)
  have hY0 (ω) : 0 ≤ Y ω := Set.indicator_nonneg (fun ω _ => le_min (hf0 ω) (hcut.le.trans hcap)) ω
  have hY : Integrable Y P := (integrable_nonnegative_cap P f hf hf0 cap (hcut.le.trans hcap)).indicator hgood
  have hmark := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hY0) hY cutoff
  have hsubf : {ω | ω ∈ good ∧ cutoff < f ω} ⊆ {ω | cutoff ≤ Y ω} := by
    intro ω hω
    dsimp [Y]
    rw [Set.indicator_of_mem hω.1]
    exact le_min hω.2.le hcap
  have hftail : P.real {ω | ω ∈ good ∧ cutoff < f ω} ≤ C/cutoff := by
    apply (le_div_iff₀ hcut).mpr
    have hm := mul_le_mul_of_nonneg_left (measureReal_mono (μ := P) hsubf) hcut.le
    nlinarith only [hm,hmark,hfirst]
  let cut : Set Ω := good ∩ {ω | f ω ≤ cutoff}
  have hcutmeas : MeasurableSet cut := hgood.inter (measurableSet_le hf measurable_const)
  let g := fun ω => a*cutoff+|v|+2*o ω
  have hg : Integrable g P := (integrable_const (a*cutoff+|v|)).add (ho.const_mul 2)
  have hg0 (ω) : 0 ≤ g ω := by
    have hh := ho0 ω
    dsimp [g]
    positivity
  have hfiber := integrableOn_prod_good_of_fiber_integral_bound P Q cut hcutmeas
    (fun z => ‖e z‖^2) (he.norm.pow_const 2) (fun z => sq_nonneg _) g hg
    (fun ω _ => Integrable.of_finite)
    (fun ω hω => (hvariance ω hω.1).trans (by
      dsimp [g]
      have hm := mul_le_mul_of_nonneg_left hω.2 ha
      linarith [le_abs_self v]))
  have hInt : (∫ z in cut ×ˢ univ,‖e z‖^2 ∂P.prod Q) ≤ a*cutoff+|v|+2*(∫ ω,o ω ∂P) := by
    apply hfiber.2.trans
    apply (setIntegral_le_integral hg (Eventually.of_forall hg0)).trans_eq
    rw [integral_add (integrable_const _) (ho.const_mul 2),integral_const_mul,integral_const,
      measureReal_univ_eq_one,one_smul]
  let Z := (cut ×ˢ (univ : Set T)).indicator (fun z => ‖e z‖^2)
  have hZ : Integrable Z (P.prod Q) := (integrable_indicator_iff (hcutmeas.prod MeasurableSet.univ)).mpr hfiber.1
  have hZ0 (z) : 0 ≤ Z z := Set.indicator_nonneg (fun z _ => sq_nonneg _) z
  have hm2 := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hZ0) hZ (ε^2)
  have hcutsub : {z | z.1 ∈ cut ∧ ε < ‖e z‖} ⊆ {z | ε^2 ≤ Z z} := by
    intro z hz
    have hzc : z ∈ cut ×ˢ (univ : Set T) := ⟨hz.1,mem_univ _⟩
    change ε^2 ≤ (cut ×ˢ (univ : Set T)).indicator (fun z => ‖e z‖^2) z
    rw [Set.indicator_of_mem hzc]
    exact (sq_le_sq₀ hε.le (norm_nonneg _)).mpr hz.2.le
  have htailcut : (P.prod Q).real {z | z.1 ∈ cut ∧ ε < ‖e z‖} ≤
      (a*cutoff+|v|+2*(∫ ω,o ω ∂P))/ε^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    have hm := mul_le_mul_of_nonneg_left (measureReal_mono (μ := P.prod Q) hcutsub) (sq_nonneg ε)
    have hZi : (∫ z,Z z ∂P.prod Q) ≤ a*cutoff+|v|+2*(∫ ω,o ω ∂P) := by
      rw [integral_indicator (hcutmeas.prod MeasurableSet.univ)]
      exact hInt
    nlinarith only [hm,hm2,hZi]
  have hsub : {z | ε < ‖e z‖} ⊆
      (goodᶜ ×ˢ univ) ∪ ({ω | ω ∈ good ∧ cutoff < f ω} ×ˢ univ) ∪ {z | z.1 ∈ cut ∧ ε < ‖e z‖} := by
    intro z hz
    by_cases hg : z.1 ∈ good
    · by_cases hf : cutoff < f z.1
      · exact Or.inl (Or.inr ⟨⟨hg,hf⟩,mem_univ _⟩)
      · exact Or.inr ⟨⟨hg,le_of_not_gt hf⟩,hz⟩
    · exact Or.inl (Or.inl ⟨hg,mem_univ _⟩)
  have hprod (A : Set Ω) : (P.prod Q).real (A ×ˢ univ)=P.real A := by
    rw [measureReal_def,Measure.prod_prod]
    simp only [measure_univ,mul_one,measureReal_def]
  calc
    _ ≤ (P.prod Q).real ((goodᶜ ×ˢ univ) ∪ ({ω | ω ∈ good ∧ cutoff < f ω} ×ˢ univ) ∪
        {z | z.1 ∈ cut ∧ ε < ‖e z‖}) := measureReal_mono hsub
    _ ≤ ((P.prod Q).real (goodᶜ ×ˢ univ)+(P.prod Q).real ({ω | ω ∈ good ∧ cutoff < f ω} ×ˢ univ))+
        (P.prod Q).real {z | z.1 ∈ cut ∧ ε < ‖e z‖} :=
      (measureReal_union_le _ _).trans (add_le_add_right (measureReal_union_le _ _) _)
    _ = (P.real goodᶜ+P.real {ω | ω ∈ good ∧ cutoff < f ω})+
        (P.prod Q).real {z | z.1 ∈ cut ∧ ε < ‖e z‖} := by rw [hprod,hprod]
    _ ≤ _ := add_le_add (add_le_add_left hftail _) htailcut

set_option maxHeartbeats 3000000 in
theorem capped_truncation_probability_two_step
    {Ω : Type*} [MeasurableSpace Ω] {T : ℕ → Type*} [∀ n,MeasurableSpace (T n)]
    [∀ n,Finite (T n)] [∀ n,MeasurableSingletonClass (T n)]
    {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : ∀ n,Measure (T n)) [∀ n,IsProbabilityMeasure (Q n)]
    (good : ℕ → Set Ω) (hgood : ∀ n,MeasurableSet (good n))
    (hbad : Tendsto (fun n => P.real (good n)ᶜ) atTop (nhds 0))
    (cap : ℕ → ℝ) (hcap : Tendsto cap atTop atTop)
    (f : ℕ → ℕ → Ω → ℝ) (hf : ∀ k n,Measurable (f k n)) (hf0 : ∀ k n ω,0 ≤ f k n ω)
    (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hfirst : ∀ k,∀ᶠ n in atTop,(∫ ω,(good n).indicator (fun ω => min (f k n ω) (cap n)) ω ∂P) ≤ C)
    (e : ∀ k n : ℕ,Ω × T n → V) (he : ∀ k n,Measurable (e k n))
    (v : ℕ → ℝ) (hv : Tendsto v atTop (nhds 0))
    (o : ℕ → Ω → ℝ) (ho : ∀ᶠ n in atTop,Integrable (o n) P) (ho0 : ∀ n ω,0 ≤ o n ω)
    (hoint : Tendsto (fun n => ∫ ω,o n ω ∂P) atTop (nhds 0))
    (hvariance : ∀ᶠ k in atTop,∀ᶠ n in atTop,∀ ω ∈ good n,
      (∫ t,‖e k n (ω,t)‖^2 ∂Q n) ≤ A/((k : ℝ)+1)*f k n ω+v n+2*o n ω) :
    ∀ ε δ : ℝ,0 < ε → 0 < δ → ∃ k0 : ℕ,∀ k : ℕ,k0 ≤ k →
      ∀ᶠ n in atTop,(P.prod (Q n)).real {z | ε < ‖e k n z‖} ≤ δ := by
  intro ε δ hε hδ
  let cutoff := 1+4*C/δ
  have hcut : 0 < cutoff := by dsimp [cutoff]; positivity
  have hCT : C/cutoff ≤ δ/4 := by
    apply (div_le_iff₀ hcut).mpr
    have heq : δ/4*cutoff=C+δ/4 := by
      dsimp [cutoff]
      field_simp [hδ.ne']
      ring
    rw [heq]
    linarith
  have hkInv : Tendsto (fun k : ℕ => ((k : ℝ)+1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hkTerm : Tendsto (fun k : ℕ => (A/((k : ℝ)+1)*cutoff)/ε^2) atTop (nhds 0) := by
    have hh := hkInv.const_mul (A*cutoff/ε^2)
    convert hh using 1
    · funext k
      ring
    · simp only [mul_zero]
  obtain ⟨kTerm,hkTermBound⟩ := eventually_atTop.mp ((tendsto_order.mp hkTerm).2 (δ/4) (by positivity))
  obtain ⟨kVariance,hkVariance⟩ := eventually_atTop.mp hvariance
  refine ⟨max kTerm kVariance,fun k hk => ?_⟩
  have hrest : Tendsto (fun n => P.real (good n)ᶜ+(|v n|+2*(∫ ω,o n ω ∂P))/ε^2) atTop (nhds 0) := by
    simpa only [abs_zero,mul_zero,zero_add,zero_div] using hbad.add ((hv.abs.add (hoint.const_mul 2)).div_const (ε^2))
  have hrestsmall := (tendsto_order.mp hrest).2 (δ/2) (by positivity)
  filter_upwards [hfirst k,hkVariance k ((le_max_right _ _).trans hk),ho,hcap.eventually (eventually_ge_atTop cutoff),hrestsmall]
    with n hnfirst hnvar hno hncap hnrest
  have hfinite := truncation_probability_le_capped_scalar P (Q n) (good n) (hgood n) (f k n) (hf k n) (hf0 k n)
    (cap n) C (A/((k : ℝ)+1)) (v n) cutoff ε hC (by positivity) hcut hε hncap hnfirst
    (e k n) (he k n) (o n) hno (ho0 n) hnvar
  have hsplit : P.real (good n)ᶜ+C/cutoff+
      (A/((k : ℝ)+1)*cutoff+|v n|+2*(∫ ω,o n ω ∂P))/ε^2 =
      C/cutoff+(A/((k : ℝ)+1)*cutoff)/ε^2+
        (P.real (good n)ᶜ+(|v n|+2*(∫ ω,o n ω ∂P))/ε^2) := by ring
  rw [hsplit] at hfinite
  have hkSmall := hkTermBound k ((le_max_left _ _).trans hk)
  linarith

end GeneralizedBulk.Analysis
