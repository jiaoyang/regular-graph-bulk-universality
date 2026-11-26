import GeneralizedBulk.Graph.ArticleWassersteinCommonEnergy

/-! The fixed-energy, shrinking-window supremum in revised Corollary 1.3.
The comparison measure is fixed at E for every candidate in the supremum.
The common BS and scalar fourth-moment events are proved graph events.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators Classical ENNReal

namespace GeneralizedBulk.Graph

/-- The exact energy window in revised Corollary 1.3. -/
def FixedEnergyWindow {d M k : ℕ} {g : RegularGraph M d}
    (A : GraphEigenCandidate d M k g) (E δ : ℝ) : Prop :=
  ∀ a, |A.val.eigenvalue a - E| ≤ δ

/-- Literal physical Euclidean W₂ supremum against the fixed product Gaussian
star law at E. The complete orthonormal candidate family is included. -/
def fixedEnergyStarWassersteinSup {d M k : ℕ} (hd : 3 ≤ d)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    (g : RegularGraph M d) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ A : GraphEigenCandidate d M k g, ⨆ (_ : FixedEnergyWindow A E δ),
    GaussianWave.wassersteinTwo A.val.eigenStarLaw
      (commonEnergyStarGaussian d k E (by omega) (strictBulk_abs_le_degree d hd E hE))

theorem measurable_fixedEnergyStarWassersteinSup {d M k : ℕ} (hd : 3 ≤ d)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1)) (δ : ℝ) :
    Measurable (fun g : RegularGraph M d =>
      fixedEnergyStarWassersteinSup (k := k) hd E hE g δ) :=
  measurable_of_finite _

theorem fixedEnergyStarWassersteinSup_eq_zero_of_empty {d M k : ℕ} (hd : 3 ≤ d)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    (g : RegularGraph M d) (δ : ℝ)
    (h : ¬ ∃ A : GraphEigenCandidate d M k g, FixedEnergyWindow A E δ) :
    fixedEnergyStarWassersteinSup (k := k) hd E hE g δ = 0 := by
  apply le_antisymm ?_ (zero_le _)
  apply iSup_le
  intro A
  apply iSup_le
  intro hA
  exact (h ⟨A, hA⟩).elim

/-- Uniform convergence of the fixed-energy conditional W₂ discrepancy,
first in the existential bad-event form. No candidate is selected on an
empty window, and no moment, Gaussianity, BS or HY premise is supplied. -/
theorem uniform_graph_star_wasserstein_fixed_energy
    (d : ℕ) (hd : 3 ≤ d) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hlim : Tendsto N atTop atTop) [∀ n, Nonempty (RegularGraph (N n) d)]
    (k : ℕ) (_hk : 0 < k)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n =>
      (regularGraphLaw (N n) d {g | ∃ A : GraphEigenCandidate d (N n) k g,
        FixedEnergyWindow A E (δ n) ∧
        ε ≤ GaussianWave.wassersteinTwo A.val.eigenStarLaw
          (commonEnergyStarGaussian d k E (by omega)
            (strictBulk_abs_le_degree d hd E hE))}).toReal) atTop (𝓝 0) := by
  classical
  letI (n : ℕ) : IsProbabilityMeasure (regularGraphLaw (N n) d) :=
    regularGraphLaw_isProbability _ _
  let P := fun n => regularGraphLaw (N n) d
  have hopen : IsOpen {x : ℝ | x ^ 2 < 4 * ((d : ℝ) - 1)} :=
    isOpen_lt (continuous_id.pow 2) continuous_const
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen E hE
  let K : Set ℝ := Metric.closedBall E (ρ / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hEK : E ∈ K := by
    apply Metric.mem_closedBall.mpr
    simp
    linarith
  have hKbulk : ∀ x ∈ K, x ^ 2 < 4 * ((d : ℝ) - 1) := by
    intro x hx
    apply hball
    rw [Metric.mem_ball]
    exact (Metric.mem_closedBall.mp hx).trans_lt (by linarith)
  have hKabs : ∀ x ∈ K, |x| < 2 * Real.sqrt ((d : ℝ) - 1) := by
    intro x hx
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    apply (sq_lt_sq₀ (abs_nonneg x)
      (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt ((d : ℝ) - 1))).mp
    rw [sq_abs, mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (d : ℝ) - 1)]
    norm_num
    exact hKbulk x hx
  have hsmall : ∀ᶠ n in atTop, δ n ≤ ρ / 2 :=
    ((tendsto_order.mp hδ).2 (ρ / 2) (by linarith)).mono (fun _ h => h.le)
  obtain ⟨bsGood, _hbsMeas, hbsBad, hBS⟩ := exists_uniformCandidateBS d k hd N hlim
    (fun n => inferInstance) K hKabs (fun n => 2 * δ n)
  let rootGood : ∀ n, Set (RegularGraph (N n) d) :=
    fun _ => {g | ¬ HasBadRootFourth g K}
  have hrootBad : Tendsto (fun n => (P n (rootGood n)ᶜ).toReal) atTop (𝓝 0) := by
    simpa only [rootGood, Set.compl_setOf, not_not] using
      uniform_root_fourth_probability d hd N hN hlim K hK hKbulk
  let good : ∀ n, Set (RegularGraph (N n) d) := fun n =>
    (bsGood n ∩ rootGood n) ∩ {g | δ n ≤ ρ / 2}
  have hbadBase := GaussianWave.bad_probability_inter_tendsto_zero P bsGood rootGood
    hbsBad hrootBad
  have hbad : Tendsto (fun n => (P n (good n)ᶜ).toReal) atTop (𝓝 0) := by
    apply hbadBase.congr'
    filter_upwards [hsmall] with n hn
    congr 2
    ext g
    simp only [good, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_setOf_eq, hn, and_true]
  have hadm {n : ℕ} {g : RegularGraph (N n) d}
      (A : GraphEigenCandidate d (N n) k g) (hg : g ∈ good n)
      (hA : FixedEnergyWindow A E (δ n)) :
      GaussianWave.StarAdmissible A.val K (2 * δ n) := by
    constructor
    · intro a
      apply Metric.mem_closedBall.mpr
      rw [Real.dist_eq]
      exact (hA a).trans hg.2
    · intro a b
      have hab := abs_sub_le (A.val.eigenvalue a) E (A.val.eigenvalue b)
      rw [abs_sub_comm E] at hab
      linarith [hA a, hA b]
  have htight : GaussianWave.TightInProbability P (fun _ _ => (4 : ℝ)) := by
    intro ε hε
    refine ⟨4, Eventually.of_forall (fun _ => ?_)⟩
    simpa using hε
  intro ε hε
  let bad : ∀ n, Set (RegularGraph (N n) d) := fun n =>
    {g | ∃ A : GraphEigenCandidate d (N n) k g, FixedEnergyWindow A E (δ n) ∧
      ε ≤ GaussianWave.wassersteinTwo A.val.eigenStarLaw
        (commonEnergyStarGaussian d k E (by omega) (strictBulk_abs_le_degree d hd E hE))}
  apply GaussianWave.probability_bad_tendsto_zero_of_good_subsequences P good bad hbad
    (fun _ _ => (4 : ℝ)) htight
  intro C r hr g hg
  by_contra hnot
  have hfreq : ∃ᶠ j in atTop, g j ∈ bad (r j) := by
    simpa only [not_eventually, not_not] using hnot
  obtain ⟨t, ht, hb⟩ := extraction_of_frequently_atTop hfreq
  let rr := r ∘ t
  have hrr : StrictMono rr := hr.comp ht
  let g' : ∀ j, RegularGraph (N (rr j)) d := fun j => g (t j)
  let A : ∀ j, GraphEigenCandidate d (N (rr j)) k (g' j) :=
    fun j => Classical.choose (hb j)
  have hwindow (j : ℕ) : FixedEnergyWindow (A j) E (δ (rr j)) :=
    (Classical.choose_spec (hb j)).1
  have hlarge (j : ℕ) : ε ≤ GaussianWave.wassersteinTwo (A j).val.eigenStarLaw
      (commonEnergyStarGaussian d k E (by omega) (strictBulk_abs_le_degree d hd E hE)) :=
    (Classical.choose_spec (hb j)).2
  have hg' (j : ℕ) : g' j ∈ good (rr j) := (hg (t j)).1
  have hadm' (j : ℕ) : GaussianWave.StarAdmissible (A j).val K (2 * δ (rr j)) :=
    hadm (A j) (hg' j) (hwindow j)
  let D : ∀ j, GaussianWave.RegularEigenData d (N (rr j)) k := fun j => (A j).val
  have hEig (a : Fin k) : Tendsto (fun j => (D j).eigenvalue a) atTop (𝓝 E) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    have hδsmall := (tendsto_order.mp (hδ.comp hrr.tendsto_atTop)).2 η hη
    filter_upwards [hδsmall] with j hj
    rw [Real.dist_eq]
    exact ((hwindow j) a).trans_lt hj
  have hBS' : GaussianWave.BSJointClassification (fun j => (D j).eigenStarLaw) :=
    hBS rr hrr g' A (fun j => (hg' j).1.1) hadm' E hEK hEig
  have hroot (j : ℕ) (a : Fin k) :
      (N (rr j) : ℝ) * ∑ v, (D j).eigenvector a v ^ 4 ≤ 4 :=
    graphEigenCandidate_root_fourth_le_four (g' j) K hKbulk (hg' j).1.2
      (A j) a ((hadm' j).1 a)
  have hW := eigenvectors_star_wasserstein_common_energy (by omega : 2 ≤ d)
    (N ∘ rr) D E (strictBulk_abs_le_degree d hd E hE) hEig 4 hroot hBS'
  obtain ⟨j, hj⟩ := ((tendsto_order.mp hW).2 ε hε).exists
  exact (not_lt_of_ge (hlarge j)) hj

/-- Revised Corollary 1.3 along every admissible size sequence. The target
Gaussian product is fixed at E, the window is max_a |lambda_a-E| ≤ delta,
and an empty supremum is zero. All analytic estimates are proved internally. -/
theorem uniform_graph_star_wasserstein_fixed_energy_sup
    (d : ℕ) (hd : 3 ≤ d) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hlim : Tendsto N atTop atTop) [∀ n, Nonempty (RegularGraph (N n) d)]
    (k : ℕ) (hk : 0 < k)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    (δ : ℕ → ℝ) (_hδnonneg : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n =>
      (regularGraphLaw (N n) d {g |
        ε ≤ fixedEnergyStarWassersteinSup (k := k) hd E hE g (δ n)}).toReal)
          atTop (𝓝 0) := by
  letI (n : ℕ) : IsProbabilityMeasure (regularGraphLaw (N n) d) :=
    regularGraphLaw_isProbability _ _
  intro ε hε
  obtain ⟨η, hη0, hηε⟩ := exists_between hε
  have hbad := uniform_graph_star_wasserstein_fixed_energy d hd N hN hlim k hk E hE δ hδ η hη0
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => ?_) hbad
  apply ENNReal.toReal_mono (measure_ne_top (regularGraphLaw (N n) d) _)
  apply measure_mono
  intro g hg
  have hsup : η < fixedEnergyStarWassersteinSup (k := k) hd E hE g (δ n) := hηε.trans_le hg
  obtain ⟨A, hA⟩ := lt_iSup_iff.mp hsup
  obtain ⟨hwindow, hW⟩ := lt_iSup_iff.mp hA
  exact ⟨A, hwindow, hW.le⟩

end GeneralizedBulk.Graph
