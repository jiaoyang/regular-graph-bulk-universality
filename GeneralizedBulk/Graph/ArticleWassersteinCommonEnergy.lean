import GeneralizedBulk.Graph.ArticleWassersteinCorollaries
import GaussianWave.TwoEdgeGaussian

/-! Conditional Gaussian-star limits for arbitrary graph-selected tuples,
with the comparison law fixed at their common limiting bulk energy. -/
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology BigOperators Classical ENNReal RealInnerProductSpace

namespace GeneralizedBulk.Graph

theorem strictBulk_abs_le_degree (d : ℕ) (_hd : 3 ≤ d) (E : ℝ)
    (hE : E ^ 2 < 4 * ((d : ℝ) - 1)) : |E| ≤ (d : ℝ) := by
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hsq : E ^ 2 ≤ (d : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((d : ℝ) - 2)]
  exact (sq_le_sq₀ (abs_nonneg E) hdR).mp (by simpa only [sq_abs] using hsq)

/-- The actual product of independent variance-one Gaussian stars at one
fixed common energy, represented in the physical star coordinates. -/
def commonEnergyStarGaussian (d k : ℕ) (E : ℝ) (hd : 2 ≤ d)
    (hE : |E| ≤ (d : ℝ)) : Measure ((Fin k × Fin (d + 1)) → ℝ) :=
  GaussianWave.gaussianCovarianceLaw (GaussianWave.jointStarCovariance d k E)
    (GaussianWave.canonicalJointStar_posSemidef d k E hd hE)

instance commonEnergyStarGaussian_isProbability (d k : ℕ) (E : ℝ) (hd : 2 ≤ d)
    (hE : |E| ≤ (d : ℝ)) :
    IsProbabilityMeasure (commonEnergyStarGaussian d k E hd hE) := by
  unfold commonEnergyStarGaussian
  infer_instance

theorem commonEnergyStarGaussian_product (d k : ℕ) (E : ℝ) (hd : 2 ≤ d)
    (hE : |E| ≤ (d : ℝ)) :
    commonEnergyStarGaussian d k E hd hE =
      Measure.map GaussianWave.flattenChannels (Measure.pi (fun _a : Fin k =>
        GaussianWave.gaussianCovarianceLaw
          (GaussianWave.RegularEigenData.starWaveCovariance d E)
          (GaussianWave.RegularEigenData.starWaveCovariance_posSemidef d E hd hE))) := by
  apply GaussianWave.gaussian_eq_flattened_product
  intro t
  have heq : GaussianWave.jointStarCovariance d k E =
      GaussianWave.channelBlockCovariance
        (fun _ : Fin k => GaussianWave.RegularEigenData.starWaveCovariance d E) := by
    ext a b
    simp only [GaussianWave.jointStarCovariance, GaussianWave.channelBlockCovariance]
    split_ifs <;> simp
  simpa only [commonEnergyStarGaussian, heq] using
    GaussianWave.gaussianCovarianceLaw_characteristic (GaussianWave.jointStarCovariance d k E)
      (GaussianWave.canonicalJointStar_posSemidef d k E hd hE) t

theorem commonEnergyStarGaussian_coordinate_fourth (d k : ℕ) (E : ℝ) (hd : 2 ≤ d)
    (hE : |E| ≤ (d : ℝ)) (a : Fin k × Fin (d + 1)) :
    (∫ x, x a ^ 4 ∂commonEnergyStarGaussian d k E hd hE) = 3 := by
  rw [commonEnergyStarGaussian, GaussianWave.gaussianCovarianceLaw_coordinate_fourth]
  have hdiag : GaussianWave.jointStarCovariance d k E a a = 1 := by
    simp only [GaussianWave.jointStarCovariance, if_pos rfl, one_mul]
    refine Fin.cases ?_ (fun j => ?_) a.2 <;>
      simp [GaussianWave.RegularEigenData.starWaveCovariance]
  rw [hdiag]
  norm_num

theorem commonEnergyStarGaussian_coordinate_second (d k : ℕ) (E : ℝ) (hd : 2 ≤ d)
    (hE : |E| ≤ (d : ℝ)) (a : Fin k × Fin (d + 1)) :
    (∫ x, x a ^ 2 ∂commonEnergyStarGaussian d k E hd hE) = 1 := by
  rw [commonEnergyStarGaussian, GaussianWave.gaussianCovarianceLaw_coordinate_second]
  simp only [GaussianWave.jointStarCovariance, if_pos rfl, one_mul]
  refine Fin.cases ?_ (fun j => ?_) a.2 <;>
    simp [GaussianWave.RegularEigenData.starWaveCovariance]

theorem measurable_selected_graph_star_wasserstein_common_energy
    {d M k : ℕ} (hd : 2 ≤ d) (E : ℝ) (hE : |E| ≤ (d : ℝ))
    (A : (g : RegularGraph M d) → GraphEigenCandidate d M k g) :
    Measurable (fun g => GaussianWave.wassersteinTwo (A g).val.eigenStarLaw
      (commonEnergyStarGaussian d k E hd hE)) :=
  measurable_of_finite _

/-- The deterministic conditional-law limit with a fixed Gaussian comparison
at the common energy. The BS and fourth assumptions are eliminated in the
actual uniform-graph application below. -/
theorem eigenvectors_star_wasserstein_common_energy
    {d k : ℕ} (hd : 2 ≤ d) (N : ℕ → ℕ)
    (D : ∀ n, GaussianWave.RegularEigenData d (N n) k)
    (E : ℝ) (hE : |E| ≤ (d : ℝ))
    (hEig : ∀ a, Tendsto (fun n => (D n).eigenvalue a) atTop (𝓝 E))
    (M : ℝ) (hroot : ∀ n a, (N n : ℝ) * ∑ v, (D n).eigenvector a v ^ 4 ≤ M)
    (hBS : GaussianWave.BSJointClassification (fun n => (D n).eigenStarLaw)) :
    Tendsto (fun n => GaussianWave.wassersteinTwo (D n).eigenStarLaw
      (commonEnergyStarGaussian d k E hd hE)) atTop (𝓝 0) := by
  obtain ⟨hC, hweak⟩ := GaussianWave.eigenvectors_normalizedStar_weakConverges hd N
    (fun _ => k) D (fun _ => id) (fun _ => Function.injective_id) E hEig M hroot hBS
  have hw : GaussianWave.WeakLawConverges (fun n => (D n).eigenStarLaw)
      (commonEnergyStarGaussian d k E hd hE) := hweak
  have hμ (n : ℕ) := GaussianWave.integral_squareMass_sq_le (D n).eigenStarLaw
    (fun a => (D n).integrable_starLaw _ _) M (fun a => by
      rw [GaussianWave.RegularEigenData.eigenStarLaw, (D n).integral_star_coordinate_fourth]
      exact hroot n a.1)
  have hν := GaussianWave.integral_squareMass_sq_le (commonEnergyStarGaussian d k E hd hE)
    (fun a => GaussianWave.gaussianCovarianceLaw_coordinate_integrable_pow _ _ a 4) 3
    (fun a => (commonEnergyStarGaussian_coordinate_fourth d k E hd hE a).le)
  exact GaussianWave.wassersteinTwo_tendsto_zero_of_common_weak_limit
    (fun n => (D n).eigenStarLaw) (fun _ => commonEnergyStarGaussian d k E hd hE)
    (commonEnergyStarGaussian d k E hd hE) hw (fun _ => tendsto_const_nhds)
    (fun n => (hμ n).1) (fun _ => hν.1)
    (M * (Fintype.card (Fin k × Fin (d + 1)) : ℝ) ^ 2)
    (3 * (Fintype.card (Fin k × Fin (d + 1)) : ℝ) ^ 2)
    (fun n => (hμ n).2) (fun _ => hν.2)

/-- Uniform scalar fourth control applies to every channel of every actual
orthonormal eigenfamily on the same good graph. -/
theorem graphEigenCandidate_root_fourth_le_four {d M k : ℕ}
    (g : RegularGraph M d) (K : Set ℝ)
    (hbulk : ∀ x ∈ K, x ^ 2 < 4 * ((d : ℝ) - 1))
    (hg : ¬ HasBadRootFourth g K) (A : GraphEigenCandidate d M k g)
    (a : Fin k) (ha : A.val.eigenvalue a ∈ K) :
    (M : ℝ) * ∑ v, A.val.eigenvector a v ^ 4 ≤ 4 := by
  let q : EuclideanSpace ℝ (Fin M) :=
    (WithLp.equiv 2 (Fin M → ℝ)).symm (A.val.eigenvector a)
  have hnorm : ‖q‖ = 1 := by
    have hsq : ‖q‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      change (∑ v, A.val.eigenvector a v * A.val.eigenvector a v) = 1
      simpa only [if_pos rfl] using A.val.orthonormal a a
    nlinarith [norm_nonneg q]
  have heigen : (g.val.adjMatrix ℝ).toEuclideanLin q = A.val.eigenvalue a • q := by
    apply PiLp.ext
    intro v
    change (∑ w, g.val.adjMatrix ℝ v w * A.val.eigenvector a w) =
      A.val.eigenvalue a * A.val.eigenvector a v
    simpa only [A.property] using A.val.eigen_equation a v
  have hne : A.val.eigenvalue a ≠ d := by
    intro he
    have hb := hbulk _ ha
    rw [he] at hb
    nlinarith [sq_nonneg ((d : ℝ) - 2)]
  by_contra hnot
  exact hg ⟨⟨A.val.eigenvalue a, q, hnorm, heigen, hne⟩, ha, lt_of_not_ge hnot⟩

/-- The article's graph-selected tuple consequence with a fixed common-energy
Gaussian limit, in actual conditional Euclidean Wasserstein distance. Every
graph-dependent selection is automatically measurable on the finite labelled
graph spaces. No BS, HY, fourth-moment or Gaussianity input is assumed. -/
theorem selected_graph_star_wasserstein_common_energy
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
          (commonEnergyStarGaussian d k E (by omega)
            (strictBulk_abs_le_degree d hd E hE))}).toReal) atTop (𝓝 0) := by
  letI (n : ℕ) : IsProbabilityMeasure (regularGraphLaw (N n) d) :=
    regularGraphLaw_isProbability _ _
  let P := fun n => regularGraphLaw (N n) d
  let r : ∀ n, RegularGraph (N n) d → ℝ := fun n g =>
    ∑ a : Fin k, |(A n g).val.eigenvalue a - E|
  have hr := finite_sum_inProbability_zero P k hk
    (fun n g a => |(A n g).val.eigenvalue a - E|) henergy
  obtain ⟨δ, _hδpos, _hδanti, hδlim, hδbad⟩ := exists_shrinking_probability_width P r hr
  have hopen : IsOpen {x : ℝ | x ^ 2 < 4 * ((d : ℝ) - 1)} :=
    isOpen_lt (continuous_id.pow 2) continuous_const
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen E hE
  let K : Set ℝ := Metric.closedBall E (ρ / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hEK : E ∈ K := by apply Metric.mem_closedBall.mpr; simp; linarith
  have hKbulk : ∀ x ∈ K, x ^ 2 < 4 * ((d : ℝ) - 1) := by
    intro x hx
    apply hball
    rw [Metric.mem_ball]
    exact (Metric.mem_closedBall.mp hx).trans_lt (by linarith)
  have hKabs : ∀ x ∈ K, |x| < 2 * Real.sqrt ((d : ℝ) - 1) := by
    intro x hx
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    apply (sq_lt_sq₀ (abs_nonneg x) (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt ((d : ℝ) - 1))).mp
    rw [sq_abs, mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (d : ℝ) - 1)]
    norm_num
    exact hKbulk x hx
  have hsmall : ∀ᶠ n in atTop, δ n ≤ ρ / 2 :=
    ((tendsto_order.mp hδlim).2 (ρ / 2) (by linarith)).mono (fun _ h => h.le)
  let energyGood : ∀ n, Set (RegularGraph (N n) d) := fun n =>
    {g | r n g ≤ δ n ∧ δ n ≤ ρ / 2}
  have henergyBad : Tendsto (fun n => (P n (energyGood n)ᶜ).toReal) atTop (𝓝 0) := by
    apply hδbad.congr'
    filter_upwards [hsmall] with n hn
    congr 2
    ext g
    simp only [energyGood, Set.mem_compl_iff, Set.mem_setOf_eq, hn, and_true, not_le]
  obtain ⟨bsGood, _hbsMeas, hbsBad, hBS⟩ := exists_uniformCandidateBS d k hd N hlim
    (fun n => inferInstance) K hKabs (fun n => 2 * δ n)
  let rootGood : ∀ n, Set (RegularGraph (N n) d) := fun _ => {g | ¬ HasBadRootFourth g K}
  have hrootBad : Tendsto (fun n => (P n (rootGood n)ᶜ).toReal) atTop (𝓝 0) := by
    simpa only [rootGood, Set.compl_setOf, not_not] using
      uniform_root_fourth_probability d hd N hN hlim K hK hKbulk
  let good : ∀ n, Set (RegularGraph (N n) d) := fun n =>
    (bsGood n ∩ rootGood n) ∩ energyGood n
  have hbad : Tendsto (fun n => (P n (good n)ᶜ).toReal) atTop (𝓝 0) :=
    GaussianWave.bad_probability_inter_tendsto_zero P
      (fun n => bsGood n ∩ rootGood n) energyGood
      (GaussianWave.bad_probability_inter_tendsto_zero P bsGood rootGood hbsBad hrootBad)
      henergyBad
  have hadm (n : ℕ) (g : RegularGraph (N n) d) (hg : g ∈ energyGood n) :
      GaussianWave.StarAdmissible (A n g).val K (2 * δ n) := by
    have ha (a : Fin k) : |(A n g).val.eigenvalue a - E| ≤ δ n :=
      (Finset.single_le_sum (fun b _ => abs_nonneg ((A n g).val.eigenvalue b - E))
        (Finset.mem_univ a)).trans hg.1
    constructor
    · intro a
      apply Metric.mem_closedBall.mpr
      rw [Real.dist_eq]
      exact (ha a).trans hg.2
    · intro a b
      have hab := abs_sub_le ((A n g).val.eigenvalue a) E ((A n g).val.eigenvalue b)
      rw [abs_sub_comm E] at hab
      linarith [ha a, ha b]
  have htight : GaussianWave.TightInProbability P (fun _ _ => (4 : ℝ)) := by
    intro ε hε
    refine ⟨4, Eventually.of_forall (fun _ => ?_)⟩
    simpa using hε
  intro ε hε
  apply GaussianWave.probability_bad_tendsto_zero_of_good_subsequences P good
    (fun n => {g | ε ≤ GaussianWave.wassersteinTwo (A n g).val.eigenStarLaw
      (commonEnergyStarGaussian d k E (by omega) (strictBulk_abs_le_degree d hd E hE))})
    hbad (fun _ _ => 4) htight
  intro C rr hrr g hg
  let D : ∀ j, GaussianWave.RegularEigenData d (N (rr j)) k := fun j => (A (rr j) (g j)).val
  have hgg (j : ℕ) : g j ∈ good (rr j) := (hg j).1
  have hadm' (j : ℕ) : GaussianWave.StarAdmissible (D j) K (2 * δ (rr j)) :=
    hadm (rr j) (g j) (hgg j).2
  have hEig (a : Fin k) : Tendsto (fun j => (D j).eigenvalue a) atTop (𝓝 E) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    have hδsmall := (tendsto_order.mp (hδlim.comp hrr.tendsto_atTop)).2 η hη
    filter_upwards [hδsmall] with j hj
    rw [Real.dist_eq]
    have ha : |(D j).eigenvalue a - E| ≤ r (rr j) (g j) :=
      Finset.single_le_sum (fun b _ => abs_nonneg ((A (rr j) (g j)).val.eigenvalue b - E))
        (Finset.mem_univ a)
    exact (ha.trans (hgg j).2.1).trans_lt hj
  have hBS' : GaussianWave.BSJointClassification (fun j => (D j).eigenStarLaw) :=
    hBS rr hrr g (fun j => A (rr j) (g j)) (fun j => (hgg j).1.1) hadm' E hEK hEig
  have hroot (j : ℕ) (a : Fin k) :
      (N (rr j) : ℝ) * ∑ v, (D j).eigenvector a v ^ 4 ≤ 4 :=
    graphEigenCandidate_root_fourth_le_four (g j) K hKbulk (hgg j).1.2
      (A (rr j) (g j)) a ((hadm' j).1 a)
  have hW := eigenvectors_star_wasserstein_common_energy (by omega : 2 ≤ d)
    (N ∘ rr) D E (strictBulk_abs_le_degree d hd E hE) hEig 4 hroot hBS'
  exact ((tendsto_order.mp hW).2 ε hε).mono (fun j hj hlarge => (not_lt_of_ge hlarge) hj)

end GeneralizedBulk.Graph
