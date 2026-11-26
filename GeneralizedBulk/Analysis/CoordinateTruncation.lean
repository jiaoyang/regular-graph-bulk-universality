import GeneralizedBulk.Analysis.TruncationProbability

/-! Finite coordinate probability tails imply genuine joint weak convergence. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace GeneralizedBulk.Analysis
variable {Ω E I S : Type*} [MeasurableSpace Ω] [Fintype I] [PseudoMetricSpace E]

theorem pi_dist_failure_probability_le (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → I → E) (ε : ℝ) (hε : 0 ≤ ε) :
    P.real {x | ε < dist (X x) (Y x)} ≤
      ∑ i,P.real {x | ε < dist (X x i) (Y x i)} := by
  have hsub : {x | ε < dist (X x) (Y x)} ⊆ ⋃ i,{x | ε < dist (X x i) (Y x i)} := by
    intro x hx
    by_cases h : ∃ i,ε < dist (X x i) (Y x i)
    · exact mem_iUnion.mpr h
    · have hall : ∀ i,dist (X x i) (Y x i) ≤ ε := fun i => le_of_not_gt (fun hi => h ⟨i,hi⟩)
      exact False.elim ((not_lt_of_ge ((dist_pi_le_iff hε).mpr hall)) hx)
  exact (measureReal_mono hsub).trans (measureReal_iUnion_fintype_le _)

private theorem card_budget (δ : ℝ) (hδ : 0 ≤ δ) :
    (Fintype.card I : ℝ) * (δ / ((Fintype.card I : ℝ)+1)) ≤ δ := by
  have hd : 0 < (Fintype.card I : ℝ)+1 := by positivity
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hd).mpr
  nlinarith

theorem coordinate_prelimit_probability_tails
    {ΩN : ℕ → Type*} [∀ n,MeasurableSpace (ΩN n)]
    (P : ∀ n,Measure (ΩN n)) [∀ n,IsProbabilityMeasure (P n)]
    (X : ∀ n,ΩN n → I → E) (XR : ℕ → ∀ n,ΩN n → I → E)
    (hpre : ∀ i,∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∃ R0,∀ R,R0 ≤ R → ∀ᶠ n in atTop,
        (P n).real {x | ε < dist (X n x i) (XR R n x i)} ≤ δ) :
    ∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∃ R0,∀ R,R0 ≤ R → ∀ᶠ n in atTop,
        (P n).real {x | ε < dist (X n x) (XR R n x)} ≤ δ := by
  intro ε δ hε hδ
  have hb : 0 < δ/((Fintype.card I : ℝ)+1) := div_pos hδ (by positivity)
  choose cut hcut using fun i => hpre i ε (δ/((Fintype.card I : ℝ)+1)) hε hb
  let R0 := Finset.univ.sup cut
  refine ⟨R0,fun R hR => ?_⟩
  have heach : ∀ᶠ n in atTop,∀ i,
      (P n).real {x | ε < dist (X n x i) (XR R n x i)} ≤ δ/((Fintype.card I : ℝ)+1) :=
    eventually_all.mpr (fun i => hcut i R ((Finset.le_sup (Finset.mem_univ i)).trans hR))
  filter_upwards [heach] with n hn
  apply (pi_dist_failure_probability_le (P n) (X n) (XR R n) ε hε.le).trans
  apply (Finset.sum_le_sum (fun i _ => hn i)).trans
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using card_budget (I := I) δ hδ.le

theorem coordinate_target_probability_tails (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → I → E) (Y : Ω → I → E)
    (htarget : ∀ i,∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∀ᶠ R in atTop,P.real {x | ε < dist (X R x i) (Y x i)} ≤ δ) :
    ∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∀ᶠ R in atTop,P.real {x | ε < dist (X R x) (Y x)} ≤ δ := by
  intro ε δ hε hδ
  have hb : 0 < δ/((Fintype.card I : ℝ)+1) := div_pos hδ (by positivity)
  have heach := eventually_all.mpr (fun i => htarget i ε (δ/((Fintype.card I : ℝ)+1)) hε hb)
  filter_upwards [heach] with R hR
  apply (pi_dist_failure_probability_le P (X R) Y ε hε.le).trans
  apply (Finset.sum_le_sum (fun i _ => hR i)).trans
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using card_budget (I := I) δ hδ.le

/-- Keeping the scalar coordinate fixed in every truncation lets entrywise
probability estimates control the actual joint scalar/field metric. -/
theorem weakLaw_of_state_coordinate_truncations
    {T : Type*} [MeasurableSpace T]
    {ΩNs : ℕ → Type*} [∀ n,MeasurableSpace (ΩNs n)]
    [PseudoMetricSpace S] [MeasurableSpace S] [BorelSpace S] [TopologicalSpace.SeparableSpace S] [SecondCountableTopology S]
    [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.SeparableSpace E] [SecondCountableTopology E]
    (P : ∀ n,Measure (ΩNs n)) [∀ n,IsProbabilityMeasure (P n)]
    (Q : Measure T) [IsProbabilityMeasure Q]
    (X : ∀ n,ΩNs n → S × (I → E)) (XR : ℕ → ∀ n,ΩNs n → S × (I → E))
    (YR : ℕ → T → S × (I → E)) (Y : T → S × (I → E))
    (hX : ∀ n,Measurable (X n)) (hXR : ∀ R n,Measurable (XR R n))
    (hYR : ∀ R,Measurable (YR R)) (hY : Measurable Y)
    (hstateN : ∀ R n x,(X n x).1=(XR R n x).1)
    (hstate : ∀ R x,(YR R x).1=(Y x).1)
    (hfinite : ∀ R,External.WeakLawConverges (fun n => (P n).map (XR R n)) (Q.map (YR R)))
    (hpre : ∀ i,∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∃ R0,∀ R,R0 ≤ R → ∀ᶠ n in atTop,
        (P n).real {x | ε < dist ((X n x).2 i) ((XR R n x).2 i)} ≤ δ)
    (htarget : ∀ i,∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∀ᶠ R in atTop,Q.real {x | ε < dist ((YR R x).2 i) ((Y x).2 i)} ≤ δ) :
    External.WeakLawConverges (fun n => (P n).map (X n)) (Q.map Y) := by
  have hdistN (R n x) : dist (X n x) (XR R n x) = dist (X n x).2 (XR R n x).2 := by
    rw [Prod.dist_eq,hstateN R n x,dist_self,max_eq_right dist_nonneg]
  have hdist (R x) : dist (YR R x) (Y x) = dist (YR R x).2 (Y x).2 := by
    rw [Prod.dist_eq,hstate R x,dist_self,max_eq_right dist_nonneg]
  apply weakLaw_of_probability_truncations P Q X XR YR Y hX hXR hYR hY hfinite
  · simpa only [hdistN] using coordinate_prelimit_probability_tails P
      (fun n x => (X n x).2) (fun R n x => (XR R n x).2) hpre
  · simpa only [hdist] using coordinate_target_probability_tails Q
      (fun R x => (YR R x).2) (fun x => (Y x).2) htarget

end GeneralizedBulk.Analysis
