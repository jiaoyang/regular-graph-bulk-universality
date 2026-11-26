import GeneralizedBulk.Graph.WassersteinEnsemble
import GeneralizedBulk.Graph.ProbabilityWidth

/-! The literal supremum and graph-selected tuple forms of the article's
qualitative Gaussian-star corollary. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators Classical ENNReal

namespace GeneralizedBulk.Graph

/-- The physical Euclidean Wasserstein supremum over all admissible real
orthonormal eigenfamilies on one graph. Empty suprema are zero. -/
def graphStarWassersteinSup {d M k : ℕ} (hd : 3 ≤ d)
    (g : RegularGraph M d) (K : Set ℝ) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ A : GraphEigenCandidate d M k g,
    ⨆ (_ : GaussianWave.StarAdmissible A.val K δ),
      GaussianWave.wassersteinTwo A.val.eigenStarLaw
        (A.val.eigenStarGaussian (by omega))

theorem measurable_graphStarWassersteinSup {d M k : ℕ} (hd : 3 ≤ d)
    (K : Set ℝ) (δ : ℝ) :
    Measurable (fun g : RegularGraph M d => graphStarWassersteinSup (k := k) hd g K δ) :=
  measurable_of_finite _

theorem graphStarWassersteinSup_eq_zero_of_empty {d M k : ℕ} (hd : 3 ≤ d)
    (g : RegularGraph M d) (K : Set ℝ) (δ : ℝ)
    (h : ¬ ∃ A : GraphEigenCandidate d M k g,
      GaussianWave.StarAdmissible A.val K δ) :
    graphStarWassersteinSup (k := k) hd g K δ = 0 := by
  apply le_antisymm ?_ (zero_le _)
  apply iSup_le
  intro A
  apply iSup_le
  intro hadm
  exact (h ⟨A, hadm⟩).elim

/-- The displayed supremum converges to zero in probability. The supremum
includes arbitrary eigenspace rotations and contributes zero when empty. -/
theorem uniform_graph_star_wasserstein_sup
    (d : ℕ) (hd : 3 ≤ d) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hlim : Tendsto N atTop atTop) [∀ n, Nonempty (RegularGraph (N n) d)]
    (k : ℕ) (hk : 0 < k) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K, E ^ 2 < 4 * ((d : ℝ) - 1))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n =>
      (regularGraphLaw (N n) d {g |
        ε ≤ graphStarWassersteinSup (k := k) hd g K (δ n)}).toReal) atTop (𝓝 0) := by
  letI (n : ℕ) : IsProbabilityMeasure (regularGraphLaw (N n) d) :=
    regularGraphLaw_isProbability _ _
  intro ε hε
  obtain ⟨η, hη0, hηε⟩ := exists_between hε
  have hbad := uniform_graph_star_wasserstein d hd N hN hlim k hk K hK hbulk δ hδ η hη0
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => ?_) hbad
  apply ENNReal.toReal_mono (measure_ne_top (regularGraphLaw (N n) d) _)
  apply measure_mono
  intro g hg
  have hsup : η < graphStarWassersteinSup (k := k) hd g K (δ n) := hηε.trans_le hg
  obtain ⟨A, hA⟩ := lt_iSup_iff.mp hsup
  obtain ⟨hadm, hW⟩ := lt_iSup_iff.mp hA
  exact ⟨A, hadm, hW.le⟩

theorem measurable_selected_graph_star_wasserstein {d M k : ℕ} (hd : 3 ≤ d)
    (A : (g : RegularGraph M d) → GraphEigenCandidate d M k g) :
    Measurable (fun g => GaussianWave.wassersteinTwo (A g).val.eigenStarLaw
      ((A g).val.eigenStarGaussian (by omega))) :=
  measurable_of_finite _

/-- Every actual graph-dependent orthonormal eigenvector tuple whose
eigenvalues converge in probability to one strict bulk energy has its
conditional empirical star law asymptotic to the product of variance-one
Gaussian stars at its own eigenvalues. No measurability assumption on the
selection is necessary: each labelled graph space is finite. -/
theorem selected_graph_star_wasserstein
    (d : ℕ) (hd : 3 ≤ d) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hlim : Tendsto N atTop atTop) [∀ n, Nonempty (RegularGraph (N n) d)]
    (k : ℕ) (hk : 0 < k)
    (A : ∀ n, (g : RegularGraph (N n) d) → GraphEigenCandidate d (N n) k g)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    (henergy : ∀ a (t : ℝ), 0 < t → Tendsto (fun n =>
      (regularGraphLaw (N n) d {g | t ≤ |(A n g).val.eigenvalue a - E|}).toReal)
        atTop (𝓝 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n =>
      (regularGraphLaw (N n) d {g |
        ε ≤ GaussianWave.wassersteinTwo (A n g).val.eigenStarLaw
          ((A n g).val.eigenStarGaussian (by omega))}).toReal) atTop (𝓝 0) := by
  letI (n : ℕ) : IsProbabilityMeasure (regularGraphLaw (N n) d) :=
    regularGraphLaw_isProbability _ _
  let r : ∀ n, RegularGraph (N n) d → ℝ := fun n g =>
    ∑ a : Fin k, |(A n g).val.eigenvalue a - E|
  have hr := finite_sum_inProbability_zero (fun n => regularGraphLaw (N n) d) k hk
    (fun n g a => |(A n g).val.eigenvalue a - E|) henergy
  obtain ⟨δ, hδpos, hδanti, hδlim, hδbad⟩ :=
    exists_shrinking_probability_width (fun n => regularGraphLaw (N n) d) r hr
  have hopen : IsOpen {x : ℝ | x ^ 2 < 4 * ((d : ℝ) - 1)} :=
    isOpen_lt (continuous_id.pow 2) continuous_const
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen E hE
  let K : Set ℝ := Metric.closedBall E (ρ / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKbulk : ∀ x ∈ K, x ^ 2 < 4 * ((d : ℝ) - 1) := by
    intro x hx
    apply hball
    rw [Metric.mem_ball]
    exact (Metric.mem_closedBall.mp hx).trans_lt (by linarith)
  have hsmall : ∀ᶠ n in atTop, δ n ≤ ρ / 2 :=
    ((tendsto_order.mp hδlim).2 (ρ / 2) (by linarith)).mono (fun _ h => h.le)
  have hδtwo : Tendsto (fun n => 2 * δ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hδlim.const_mul 2
  have hadm (n : ℕ) (hn : δ n ≤ ρ / 2) (g : RegularGraph (N n) d)
      (hg : r n g ≤ δ n) :
      GaussianWave.StarAdmissible (A n g).val K (2 * δ n) := by
    have ha (a : Fin k) : |(A n g).val.eigenvalue a - E| ≤ δ n :=
      (Finset.single_le_sum (fun b _ => abs_nonneg ((A n g).val.eigenvalue b - E))
        (Finset.mem_univ a)).trans hg
    constructor
    · intro a
      apply Metric.mem_closedBall.mpr
      rw [Real.dist_eq]
      exact (ha a).trans hn
    · intro a b
      have hab := abs_sub_le ((A n g).val.eigenvalue a) E ((A n g).val.eigenvalue b)
      rw [abs_sub_comm E] at hab
      linarith [ha a, ha b]
  intro ε hε
  have hbad := uniform_graph_star_wasserstein d hd N hN hlim k hk K hK hKbulk
    (fun n => 2 * δ n) hδtwo ε hε
  apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
    (hsmall.mono (fun n hn => ?_)) (by simpa using hδbad.add hbad)
  have hsub : {g : RegularGraph (N n) d |
      ε ≤ GaussianWave.wassersteinTwo (A n g).val.eigenStarLaw
        ((A n g).val.eigenStarGaussian (by omega))} ⊆
      {g | δ n < r n g} ∪ {g | ∃ B : GraphEigenCandidate d (N n) k g,
        GaussianWave.StarAdmissible B.val K (2 * δ n) ∧
        ε ≤ GaussianWave.wassersteinTwo B.val.eigenStarLaw
          (B.val.eigenStarGaussian (by omega))} := by
    intro g hg
    by_cases hlarge : δ n < r n g
    · exact Or.inl hlarge
    · exact Or.inr ⟨A n g, hadm n hn g (le_of_not_gt hlarge), hg⟩
  exact (measureReal_mono hsub).trans (measureReal_union_le _ _)

end GeneralizedBulk.Graph
