import GeneralizedBulk.Graph.UniformRootFourth
import GeneralizedBulk.Graph.UniformCandidateBS
import GaussianWave.BulkInput

/-! Uniform Euclidean W₂ Gaussian-star convergence for the literal uniform
regular-graph ensemble, including arbitrary eigenspace rotations. -/
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology BigOperators Classical RealInnerProductSpace ENNReal

namespace GeneralizedBulk.Graph
open CanonicalSpectrum

private theorem candidate_root_fourth_le_four {d M k : ℕ} (g : RegularGraph M d)
    (hd : 3≤d) (K : Set ℝ) (hbulk : ∀ E∈K,E^2<4*((d : ℝ)-1))
    (hg : ¬HasBadRootFourth g K) (A : GraphEigenCandidate d M k g)
    (a : Fin k) (ha : A.val.eigenvalue a∈K) :
    (M : ℝ)*∑ v,A.val.eigenvector a v^4 ≤ 4 := by
  classical
  let q : EuclideanSpace ℝ (Fin M) :=
    (WithLp.equiv 2 (Fin M → ℝ)).symm (A.val.eigenvector a)
  have hnorm : ‖q‖=1 := by
    have hsq : ‖q‖^2=1 := by
      rw [←real_inner_self_eq_norm_sq]
      change (∑ v,A.val.eigenvector a v*A.val.eigenvector a v)=1
      simpa only [if_pos rfl] using A.val.orthonormal a a
    nlinarith [norm_nonneg q]
  have heigen : (g.val.adjMatrix ℝ).toEuclideanLin q=A.val.eigenvalue a • q := by
    apply PiLp.ext
    intro v
    change (∑ w,g.val.adjMatrix ℝ v w*A.val.eigenvector a w)=
      A.val.eigenvalue a*A.val.eigenvector a v
    simpa only [A.property] using A.val.eigen_equation a v
  have hne : A.val.eigenvalue a ≠ d := by
    intro he
    have hb := hbulk _ ha
    rw [he] at hb
    nlinarith [sq_nonneg ((d : ℝ)-2)]
  by_contra hnot
  apply hg
  exact ⟨⟨A.val.eigenvalue a,q,hnorm,heigen,hne⟩,ha,lt_of_not_ge hnot⟩

/-- The article's uniform Gaussian-star corollary for the actual finite
uniform graph measures. Candidates range over all orthonormal eigenvector
tuples and all exact neighbor enumerations for the sampled graph. The
comparison is the genuine infimum-over-couplings Euclidean W₂ distance,
with the product Gaussian law at each vector's own eigenvalue.

Only degree, admissible graph sizes tending to infinity, a compact strict
bulk set, positive channel count, and vanishing energy width are inputs.
BS, HY, entropy and moment estimates are all constructed internally. -/
theorem uniform_graph_star_wasserstein
    (d : ℕ) (hd : 3≤d) (N : ℕ → ℕ) (hN : ∀ n,0<N n)
    (hlim : Tendsto N atTop atTop) [∀ n,Nonempty (RegularGraph (N n) d)]
    (k : ℕ) (hk : 0<k) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E∈K,E^2<4*((d : ℝ)-1))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ ε : ℝ≥0∞,0<ε → Tendsto (fun n =>
      (regularGraphLaw (N n) d {g | ∃ A : GraphEigenCandidate d (N n) k g,
        GaussianWave.StarAdmissible A.val K (δ n) ∧
        ε ≤ GaussianWave.wassersteinTwo A.val.eigenStarLaw
          (A.val.eigenStarGaussian (by omega))}).toReal) atTop (𝓝 0) := by
  letI (n : ℕ) : IsProbabilityMeasure (regularGraphLaw (N n) d) :=
    regularGraphLaw_isProbability _ _
  have habs : ∀ E∈K,|E|<2*Real.sqrt ((d : ℝ)-1) := by
    intro E hE
    have hdr : (3 : ℝ)≤d := by exact_mod_cast hd
    have hn : (0 : ℝ)≤(d : ℝ)-1 := by linarith
    apply (sq_lt_sq₀ (abs_nonneg E) (by positivity : (0 : ℝ)≤2*Real.sqrt ((d : ℝ)-1))).mp
    rw [sq_abs,mul_pow,Real.sq_sqrt hn]
    norm_num
    exact hbulk E hE
  obtain ⟨bsGood,hbsMeas,hbsBad,hBS⟩ := exists_uniformCandidateBS d k hd N hlim
    (fun n => inferInstance) K habs δ
  let good : ∀ n,Set (RegularGraph (N n) d) := fun n =>
    bsGood n ∩ {g | ¬HasBadRootFourth g K}
  have hrootBad : Tendsto (fun n =>
      (regularGraphLaw (N n) d ({g | ¬HasBadRootFourth g K}ᶜ)).toReal) atTop (𝓝 0) := by
    simpa only [Set.compl_setOf,not_not] using uniform_root_fourth_probability d hd N hN hlim K hK hbulk
  have hbad : Tendsto (fun n => (regularGraphLaw (N n) d (good n)ᶜ).toReal)
      atTop (𝓝 0) :=
    GaussianWave.bad_probability_inter_tendsto_zero (fun n => regularGraphLaw (N n) d)
      bsGood (fun _ => {g | ¬HasBadRootFourth g K}) hbsBad hrootBad
  have htight : GaussianWave.TightInProbability (fun n => regularGraphLaw (N n) d)
      (fun _ _ => (4 : ℝ)) := by
    intro ε hε
    refine ⟨4,Eventually.of_forall (fun _ => ?_)⟩
    simpa using hε
  apply GaussianWave.uniform_normalizedStar_wasserstein_inProbability hd hk N
    (fun n => regularGraphLaw (N n) d) (fun n g => GraphEigenCandidate d (N n) k g)
    (fun _ _ A => A.val) K hK δ hδ good hbad (fun _ _ => 4) htight
  · intro n g A hg hadm a
    exact candidate_root_fourth_le_four g hd K hbulk hg.2 A a (hadm.1 a)
  · intro r hr ω s hg hadm E hEK hEig
    exact hBS r hr ω s (fun j => (hg j).1) hadm E hEK hEig

end GeneralizedBulk.Graph
