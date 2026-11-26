import GaussianWave.TwoEdgeGaussian
import GaussianWave.GoodGraphConvergence
import GaussianWave.VaryingConditionalMarks

/-!
# Quenched two-edge Gaussian marks on actual varying graph spaces

The conditional marks are the actual finite empirical two-edge laws of the
selected regular-graph eigenvectors. Convergence of their bounded continuous
test expectations is derived from BS classification and root fourth control;
it is not supplied as a desired-conclusion hypothesis.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace GaussianWave

/-- The source classification required on every good subsequence of selected
graphs. The eigenvectors are selected graph by graph in the data `D`. -/
def SelectedBSOn
    {d k : ℕ} {N : ℕ → ℕ} {Ω : ℕ → Type*}
    (D : ∀ n, Ω n → RegularEigenData d (N n) k)
    (good : ∀ n, Set (Ω n)) : Prop :=
  ∀ r : ℕ → ℕ, StrictMono r → ∀ ω : ∀ j, Ω (r j),
    (∀ j, ω j ∈ good (r j)) →
      BSJointClassification (fun j => (D (r j) (ω j)).eigenStarLaw)

/-- Actual quenched test convergence in graph probability. The two-edge
Gaussian limit is obtained inside the proof from the eigenvector theorem. -/
theorem quenched_twoEdge_test_inProbability
    {d k : ℕ} (hd : 2 ≤ d) (leaf : Fin d)
    (N : ℕ → ℕ) {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (D : ∀ n, Ω n → RegularEigenData d (N n) k)
    (E : ℝ) (hEb : |E| ≤ (d : ℝ))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (good : ∀ n, Set (Ω n))
    (hbad : Tendsto (fun n => (P n (good n)ᶜ).toReal) atTop (𝓝 0))
    (hnear : ∀ n ω, ω ∈ good n → ∀ i, |(D n ω).eigenvalue i - E| ≤ δ n)
    (M : ∀ n, Ω n → ℝ) (htight : TightInProbability P M)
    (hroot : ∀ n ω, ω ∈ good n → ∀ i,
      (N n : ℝ) * ∑ v, (D n ω).eigenvector i v ^ 4 ≤ M n ω)
    (BS : SelectedBSOn D good)
    (f : BoundedContinuousFunction ((Fin k × Fin 4) → ℝ) ℝ) :
    VaryingConditionalMarks.ErrorInProbability P
      (fun n ω => ∫ y, f y ∂(D n ω).twoEdgeLaw leaf)
      (∫ y, f y ∂twoEdgeGaussian d k E hd hEb leaf) := by
  intro ε hε
  apply probability_bad_tendsto_zero_of_good_subsequences P good
    (fun n => {ω | ε ≤ |(∫ y, f y ∂(D n ω).twoEdgeLaw leaf) -
      ∫ y, f y ∂twoEdgeGaussian d k E hd hEb leaf|}) hbad M htight
  intro C r hr ω hω
  let D' : ∀ j, RegularEigenData d (N (r j)) k := fun j => D (r j) (ω j)
  have hEig (i : Fin k) : Tendsto (fun j => (D' j).eigenvalue i) atTop (𝓝 E) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    have hsmall := (tendsto_order.mp (hδ.comp hr.tendsto_atTop)).2 η hη
    filter_upwards [hsmall] with j hj
    rw [Real.dist_eq]
    exact (hnear (r j) (ω j) (hω j).1 i).trans_lt hj
  have hroot' (j : ℕ) (i : Fin k) :
      (N (r j) : ℝ) * ∑ v, (D' j).eigenvector i v ^ 4 ≤ C :=
    (hroot (r j) (ω j) (hω j).1 i).trans (hω j).2
  have hw := eigenvectors_twoEdge_weakConverges hd (N ∘ r) D' E hEig hEb C hroot'
    (BS r hr ω (fun j => (hω j).1)) leaf
  have htest := hw f
  have he : Tendsto (fun j =>
      (∫ y, f y ∂(D' j).twoEdgeLaw leaf) -
        ∫ y, f y ∂twoEdgeGaussian d k E hd hEb leaf) atTop (𝓝 0) := by
    simpa using htest.sub_const (∫ y, f y ∂twoEdgeGaussian d k E hd hEb leaf)
  have hsmall := (Metric.tendsto_nhds.mp he) ε hε
  filter_upwards [hsmall] with j hj
  rw [Real.dist_eq, sub_zero] at hj
  exact not_le_of_gt hj

/-- For each fixed bounded continuous mark test, the actual quenched error
vanishes in L1 and factorizes against every bounded complex graph-state test. -/
theorem quenched_twoEdge_L1_and_stable_factorization
    {d k : ℕ} (hd : 2 ≤ d) (leaf : Fin d)
    (N : ℕ → ℕ) {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (D : ∀ n, Ω n → RegularEigenData d (N n) k)
    (E : ℝ) (hEb : |E| ≤ (d : ℝ))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (good : ∀ n, Set (Ω n))
    (hbad : Tendsto (fun n => (P n (good n)ᶜ).toReal) atTop (𝓝 0))
    (hnear : ∀ n ω, ω ∈ good n → ∀ i, |(D n ω).eigenvalue i - E| ≤ δ n)
    (M : ∀ n, Ω n → ℝ) (htight : TightInProbability P M)
    (hroot : ∀ n ω, ω ∈ good n → ∀ i,
      (N n : ℝ) * ∑ v, (D n ω).eigenvector i v ^ 4 ≤ M n ω)
    (BS : SelectedBSOn D good)
    (f : BoundedContinuousFunction ((Fin k × Fin 4) → ℝ) ℝ)
    (hq : ∀ n, Measurable (fun ω => ∫ y, f y ∂(D n ω).twoEdgeLaw leaf))
    (H : ∀ n, Ω n → ℂ) (hH : ∀ n, Measurable (H n))
    (C : ℝ) (hC : ∀ n ω, ‖H n ω‖ ≤ C) :
    Tendsto (fun n => ∫ ω,
      |(∫ y, f y ∂(D n ω).twoEdgeLaw leaf) -
        ∫ y, f y ∂twoEdgeGaussian d k E hd hEb leaf| ∂P n) atTop (𝓝 0) ∧
    Tendsto (fun n =>
      (∫ ω, H n ω * Complex.ofReal (∫ y, f y ∂(D n ω).twoEdgeLaw leaf) ∂P n) -
        (∫ ω, H n ω ∂P n) * Complex.ofReal
          (∫ y, f y ∂twoEdgeGaussian d k E hd hEb leaf)) atTop (𝓝 0) := by
  have hp := quenched_twoEdge_test_inProbability hd leaf N P D E hEb δ hδ
    good hbad hnear M htight hroot BS f
  let κ : ∀ n, Ω n → ProbabilityMeasure ((Fin k × Fin 4) → ℝ) :=
    fun n ω => ⟨(D n ω).twoEdgeLaw leaf, inferInstance⟩
  let ν : ProbabilityMeasure ((Fin k × Fin 4) → ℝ) :=
    ⟨twoEdgeGaussian d k E hd hEb leaf, inferInstance⟩
  have hf (y : (Fin k × Fin 4) → ℝ) : |f y| ≤ ‖f‖ := by
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm y
  exact ⟨VaryingConditionalMarks.conditional_mark_law_L1 P κ ν f ‖f‖ hf hq hp,
    VaryingConditionalMarks.conditional_mark_law_factorization P κ ν f ‖f‖ hf hq hp H hH C hC⟩

end GaussianWave
