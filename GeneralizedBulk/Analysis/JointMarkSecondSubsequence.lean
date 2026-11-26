import GeneralizedBulk.Analysis.JointMarkSubsequence

/-! Exact second moments already suffice for joint anchored-state/finite-mark
subsequence extraction, including arbitrary graph outcomes. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology ENNReal BigOperators
namespace GeneralizedBulk.Analysis

theorem isTightMeasureSet_of_uniform_norm_second
    {V : Type*} [NormedAddCommGroup V] [ProperSpace V] [MeasurableSpace V] [BorelSpace V]
    (μ : ℕ → Measure V) [∀ n,IsProbabilityMeasure (μ n)]
    (hi : ∀ n,Integrable (fun x => ‖x‖^2) (μ n)) (M : ℝ)
    (hM : ∀ n,(∫ x,‖x‖^2 ∂μ n) ≤ M) : IsTightMeasureSet (range μ) := by
  rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨∅,isCompact_empty,fun η hη => by simp [htop]⟩
  have hδ : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨B,hB⟩ := exists_nat_gt (max 0 (M/ε.toReal))
  have hBpos : 0 < (B : ℝ) := (le_max_left _ _).trans_lt hB
  have hMB : M ≤ (B : ℝ)*ε.toReal := ((div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hB)).le
  refine ⟨Metric.closedBall 0 ((B : ℝ)+1),isCompact_closedBall _ _,?_⟩
  rintro _ ⟨n,rfl⟩
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ n)
    (Eventually.of_forall (fun x => sq_nonneg ‖x‖)) (hi n) (B : ℝ)
  have htail : (μ n {x | (B : ℝ) ≤ ‖x‖^2}).toReal ≤ ε.toReal := by
    change (B : ℝ)*(μ n {x | (B : ℝ) ≤ ‖x‖^2}).toReal ≤ _ at hMarkov
    nlinarith [hM n]
  have hsub : (Metric.closedBall (0 : V) ((B : ℝ)+1))ᶜ ⊆ {x | (B : ℝ) ≤ ‖x‖^2} := by
    intro x hx
    have hn : (B : ℝ)+1 < ‖x‖ := by
      simpa only [mem_compl_iff,Metric.mem_closedBall,dist_zero_right,not_le] using hx
    have hn1 : 1 ≤ ‖x‖ := by linarith [Nat.cast_nonneg (α := ℝ) B]
    change (B : ℝ) ≤ ‖x‖^2
    have hprod := mul_nonneg (norm_nonneg x) (sub_nonneg.mpr hn1)
    nlinarith
  calc
    _ ≤ μ n {x | (B : ℝ) ≤ ‖x‖^2} := measure_mono hsub
    _ = ENNReal.ofReal ((μ n {x | (B : ℝ) ≤ ‖x‖^2}).toReal) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal htail
    _ = ε := ENNReal.ofReal_toReal htop

theorem anchored_mark_subsequence_of_tight_scalar_second
    {ι : Type*} [Fintype ι] (μ : ℕ → ProbabilityMeasure (AnchoredCountingState × (ι → ℝ)))
    (hscalar : IsTightMeasureSet (range (fun n => (μ n : Measure (AnchoredCountingState × (ι → ℝ))).map Prod.fst)))
    (hi : ∀ n,Integrable (fun z : AnchoredCountingState × (ι → ℝ) => ‖z.2‖^2) (μ n : Measure (AnchoredCountingState × (ι → ℝ)))) (M : ℝ)
    (hM : ∀ n,(∫ z : AnchoredCountingState × (ι → ℝ),‖z.2‖^2 ∂(μ n : Measure (AnchoredCountingState × (ι → ℝ)))) ≤ M) :
    ∃ (ν : ProbabilityMeasure (AnchoredCountingState × (ι → ℝ))) (r : ℕ → ℕ),StrictMono r ∧
      Tendsto (μ ∘ r) atTop (𝓝 ν) := by
  let marks := fun n => (μ n : Measure (AnchoredCountingState × (ι → ℝ))).map Prod.snd
  letI : ∀ n,IsProbabilityMeasure (marks n) := fun n => isProbabilityMeasure_map measurable_snd.aemeasurable
  have himarks (n : ℕ) : Integrable (fun x : ι → ℝ => ‖x‖^2) (marks n) := by
    exact (integrable_map_measure (continuous_norm.pow 2).aestronglyMeasurable measurable_snd.aemeasurable).mpr (hi n)
  have hmarksM (n : ℕ) : (∫ x : ι → ℝ,‖x‖^2 ∂marks n) ≤ M := by
    dsimp only [marks]
    rw [integral_map measurable_snd.aemeasurable (continuous_norm.pow 2).aestronglyMeasurable]
    exact hM n
  have ht := isTightMeasureSet_of_tight_marginals (fun n => (μ n : Measure (AnchoredCountingState × (ι → ℝ)))) hscalar
    (isTightMeasureSet_of_uniform_norm_second marks himarks M hmarksM)
  exact laws_subsequence_of_tight_compact_embedding anchoredMarkCompactification isEmbedding_anchoredMarkCompactification
    measurableEmbedding_anchoredMarkCompactification μ ht

theorem anchored_mark_map_subsequence_of_tight_scalar_second
    {ι : Type*} [Fintype ι] {ΩN : ℕ → Type*} [∀ n,MeasurableSpace (ΩN n)]
    (P : ∀ n,Measure (ΩN n)) [∀ n,IsProbabilityMeasure (P n)]
    (S : ∀ n,ΩN n → AnchoredCountingState) (marks : ∀ n,ΩN n → (ι → ℝ))
    (hS : ∀ n,Measurable (S n)) (hmarks : ∀ n,Measurable (marks n))
    (hscalar : IsTightMeasureSet (range (fun n => (P n).map (S n))))
    (hi : ∀ n,Integrable (fun x => ‖marks n x‖^2) (P n)) (M : ℝ)
    (hM : ∀ n,(∫ x,‖marks n x‖^2 ∂P n) ≤ M) :
    ∃ (ν : ProbabilityMeasure (AnchoredCountingState × (ι → ℝ))) (r : ℕ → ℕ),StrictMono r ∧
      External.WeakLawConverges (fun n => (P (r n)).map (fun x => (S (r n) x,marks (r n) x))) (ν : Measure _) := by
  let F := fun n (x : ΩN n) => (S n x,marks n x)
  have hF (n : ℕ) : Measurable (F n) := (hS n).prodMk (hmarks n)
  let laws : ℕ → ProbabilityMeasure (AnchoredCountingState × (ι → ℝ)) :=
    fun n => ⟨(P n).map (F n),isProbabilityMeasure_map (hF n).aemeasurable⟩
  have hscalar' : IsTightMeasureSet (range (fun n => (laws n : Measure (AnchoredCountingState × (ι → ℝ))).map Prod.fst)) := by
    have he (n : ℕ) : (laws n : Measure (AnchoredCountingState × (ι → ℝ))).map Prod.fst = (P n).map (S n) := by
      change ((P n).map (F n)).map Prod.fst = _
      rw [Measure.map_map measurable_fst (hF n)]
      rfl
    simpa only [he] using hscalar
  have hli (n : ℕ) : Integrable (fun z : AnchoredCountingState × (ι → ℝ) => ‖z.2‖^2) (laws n : Measure _) :=
    (integrable_map_measure (continuous_snd.norm.pow 2).aestronglyMeasurable (hF n).aemeasurable).mpr (hi n)
  have hlM (n : ℕ) : (∫ z : AnchoredCountingState × (ι → ℝ),‖z.2‖^2 ∂(laws n : Measure _)) ≤ M := by
    change (∫ z : AnchoredCountingState × (ι → ℝ),‖z.2‖^2 ∂(P n).map (F n)) ≤ M
    rw [integral_map (hF n).aemeasurable (continuous_snd.norm.pow 2).aestronglyMeasurable]
    exact hM n
  obtain ⟨ν,r,hr,hw⟩ := anchored_mark_subsequence_of_tight_scalar_second laws hscalar' hli M hlM
  refine ⟨ν,r,hr,?_⟩
  intro G
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hw G

end GeneralizedBulk.Analysis
