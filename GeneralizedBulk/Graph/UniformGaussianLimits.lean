import GeneralizedBulk.Gaussian.TwoStarEndpoints
import GeneralizedBulk.Graph.ConditionalFactorization

/-! Uniform good-graph Gaussianity for every admissible eigenchannel selection. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators Classical

namespace GeneralizedBulk.Graph

theorem exists_global_bound_of_eventually_le (v : ℕ → ℝ) (M : ℝ)
    (hM : ∀ᶠ n in atTop, v n ≤ M) : ∃ C : ℝ, ∀ n, v n ≤ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hM
  refine ⟨|M| + ∑ i ∈ Finset.range N, |v i|, fun n => ?_⟩
  have hs0 : 0 ≤ ∑ i ∈ Finset.range N, |v i| := Finset.sum_nonneg (fun i hi => abs_nonneg _)
  by_cases hn : N ≤ n
  · exact (hN n hn).trans ((le_abs_self M).trans (by linarith))
  · have hs := Finset.single_le_sum (fun i hi => abs_nonneg (v i))
      (Finset.mem_range.mpr (lt_of_not_ge hn))
    exact (le_abs_self (v n)).trans (hs.trans (by linarith [abs_nonneg M]))

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem BS_starLaw_weakConverges_eventually {k : ℕ} (hk : 0 < k)
    (P : Measure Ω) [IsProbabilityMeasure P] (K : Set ℝ)
    (BS : BSQualitativeInput D P K) (ω : ℕ → Ω)
    (hgood : ∀ᶠ n in atTop, ω n ∈ BS.good k n)
    (a : ∀ n, Fin k → Fin (N n)) (hinj : ∀ᶠ n in atTop, Function.Injective (a n))
    (hnonconstant : ∀ᶠ n in atTop, ∀ i, a n i ≠ ⟨0, D.size_pos n⟩)
    (energy : ℕ → ℝ) (hbulk : ∀ᶠ n in atTop, energy n ∈ K)
    (E : ℝ) (hE : E ∈ K) (henergy : Tendsto energy atTop (𝓝 E))
    (hEig : ∀ i, Tendsto (fun n => D.eigenvalue n (ω n) (a n i)) atTop (𝓝 E))
    (M : ℝ) (hM : ∀ᶠ n in atTop, (∫ x, ‖x‖ ^ 4 ∂D.starLaw n (ω n)
      (fun i => D.eigenvector n (ω n) (a n i))) ≤ M) :
    WeakLawConverges (fun n => D.starLaw n (ω n) (fun i => D.eigenvector n (ω n) (a n i)))
      (Gaussian.jointStarGaussianLaw d k (by have h := BS.degree_ge_three; omega) E) := by
  have hdegree : 2 ≤ d := by have h := BS.degree_ge_three; omega
  let μ := fun n => D.starLaw n (ω n) (fun i => D.eigenvector n (ω n) (a n i))
  letI : ∀ n, IsProbabilityMeasure (μ n) := fun n => D.starLaw_isProbability n (ω n) _
  obtain ⟨C, hC⟩ := Graph.exists_global_bound_of_eventually_le (fun n => ∫ x, ‖x‖ ^ 4 ∂μ n) M hM
  apply Gaussian.weakLaw_of_gaussian_subsequence_characterization μ
    (Gaussian.jointStarGaussianLaw d k hdegree E) (jointStarCovariance d k E)
    (Gaussian.jointStarGaussianLaw_characteristic d k hdegree E (D.BS_bulk_abs_lt_degree P K BS E hE))
    (fun n => D.integrable_starLaw n (ω n) _ (fun x => ‖x‖ ^ 4)) C hC
  · intro aj bl
    have heq : (fun n => ∫ x, x aj * x bl ∂μ n) =ᶠ[atTop]
        (fun n => (if aj.1 = bl.1 then 1 else 0) *
          starWaveCovariance d (D.eigenvalue n (ω n) (a n aj.1)) aj.2 bl.2) := by
      filter_upwards [hinj] with n hn
      exact D.integral_star_orthonormal_eigen_covariance n (ω n) hdegree (a n) hn aj.1 bl.1 aj.2 bl.2
    exact ((((continuous_starWaveCovariance d aj.2 bl.2).tendsto E).comp (hEig aj.1)).const_mul _).congr' heq.symm
  · intro φ hφ ρ hweak
    have hcentered : ∀ᶠ n in atTop, ∀ i : Fin k, (∑ v, D.eigenvector n (ω n) (a n i) v) = 0 := by
      filter_upwards [hnonconstant] with n hn
      intro i
      exact D.eigenvector_sum_zero n (ω n) (a n i) (hn i)
    have horth : ∀ᶠ n in atTop, ∀ i j : Fin k,
        (∑ v, D.eigenvector n (ω n) (a n i) v * D.eigenvector n (ω n) (a n j) v) =
          if i = j then 1 else 0 := by
      filter_upwards [hinj] with n hn
      intro i j
      simpa only [hn.eq_iff] using D.orthonormal n (ω n) (a n i) (a n j)
    exact BS.gaussian_limit k hk ω hgood
      (fun n i => D.eigenvector n (ω n) (a n i)) energy hbulk hcentered horth
      (D.eigen_tupleResidual_tendsto ω a energy E hEig henergy) E hE henergy φ hφ ρ hweak

theorem BS_twoEdgeLaw_weakConverges_eventually {k : ℕ} (hk : 0 < k)
    (P : Measure Ω) [IsProbabilityMeasure P] (K : Set ℝ)
    (BS : BSQualitativeInput D P K) (ω : ℕ → Ω)
    (hgood : ∀ᶠ n in atTop, ω n ∈ BS.good k n)
    (a : ∀ n, Fin k → Fin (N n)) (hinj : ∀ᶠ n in atTop, Function.Injective (a n))
    (hnonconstant : ∀ᶠ n in atTop, ∀ i, a n i ≠ ⟨0, D.size_pos n⟩)
    (energy : ℕ → ℝ) (hbulk : ∀ᶠ n in atTop, energy n ∈ K)
    (E : ℝ) (hE : E ∈ K) (henergy : Tendsto energy atTop (𝓝 E))
    (hEig : ∀ i, Tendsto (fun n => D.eigenvalue n (ω n) (a n i)) atTop (𝓝 E))
    (M : ℝ) (hM : ∀ᶠ n in atTop, (∫ x, ‖x‖ ^ 4 ∂D.starLaw n (ω n)
      (fun i => D.eigenvector n (ω n) (a n i))) ≤ M) (leaf : Fin d) :
    WeakLawConverges (fun n => D.twoEdgeLaw n (ω n) (a n) leaf)
      (Gaussian.finiteMarkLaw (E / d) k) := by
  have hdegree : 2 ≤ d := by have h := BS.degree_ge_three; omega
  let μ := fun n => D.starLaw n (ω n) (fun i => D.eigenvector n (ω n) (a n i))
  let target := Gaussian.jointStarGaussianLaw d k hdegree E
  letI : ∀ n, IsProbabilityMeasure (μ n) := fun n => D.starLaw_isProbability n (ω n) _
  have hw : WeakLawConverges μ target := D.BS_starLaw_weakConverges_eventually hk P K BS ω hgood a hinj
    hnonconstant energy hbulk E hE henergy hEig M hM
  obtain ⟨C, hC⟩ := Graph.exists_global_bound_of_eventually_le (fun n => ∫ x, ‖x‖ ^ 4 ∂μ n) M hM
  have hi (n : ℕ) : Integrable (fun x => ‖x‖ ^ 4) (μ n) := D.integrable_starLaw n (ω n) _ _
  have hp := Gaussian.vectorProductLaw_weakConverges μ target μ target hw hw hi hi C C hC hC
  have hm := Gaussian.weakLaw_linearImage _ _ (Gaussian.starEndpointRestriction (k := k) leaf) hp
  change WeakLawConverges (fun n => D.twoEdgeLaw n (ω n) (a n) leaf)
    (Gaussian.twoStarEndpointLaw d k hdegree E leaf) at hm
  rw [Gaussian.twoStarEndpointLaw_eq_finiteMarkLaw d k hdegree E (D.BS_bulk_abs_lt_degree P K BS E hE) leaf] at hm
  exact hm

def GoodEigenSelection {k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (K : Set ℝ)
    (BS : BSQualitativeInput D P K) (δ : ℕ → ℝ) (M E : ℝ) (n : ℕ)
    (s : Ω × (Fin k → Fin (N n))) : Prop :=
  s.1 ∈ BS.good k n ∧ Function.Injective s.2 ∧ (∀ i, s.2 i ≠ ⟨0, D.size_pos n⟩) ∧
    (∀ i, |D.eigenvalue n s.1 (s.2 i) - E| ≤ δ n) ∧
      (∫ x, ‖x‖ ^ 4 ∂D.starLaw n s.1 (fun i => D.eigenvector n s.1 (s.2 i))) ≤ M

/-- Uniformity includes every graph-dependent admissible eigenchannel
selection, not merely a fixed deterministic eigenbasis subsequence. -/
theorem BS_twoEdgeLaw_uniform_test {k : ℕ} (hk : 0 < k) [Nonempty Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : Set ℝ) (BS : BSQualitativeInput D P K)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (M E : ℝ) (hE : E ∈ K)
    (hne : ∀ᶠ n in atTop, ∃ s : Ω × (Fin k → Fin (N n)), D.GoodEigenSelection P K BS δ M E n s)
    (leaf : Fin d) (F : BoundedContinuousFunction ((Fin k × Fin 4) → ℝ) ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ s : Ω × (Fin k → Fin (N n)), D.GoodEigenSelection P K BS δ M E n s →
        |(∫ x, F x ∂D.twoEdgeLaw n s.1 s.2 leaf) - ∫ x, F x ∂Gaussian.finiteMarkLaw (E / d) k| < ε := by
  letI : ∀ n, Nonempty (Fin (N n)) := fun n => ⟨⟨0, D.size_pos n⟩⟩
  apply Graph.uniform_on_good_of_all_sequences_dependent
    (fun n => {s | D.GoodEigenSelection P K BS δ M E n s})
    (fun n s => ∫ x, F x ∂D.twoEdgeLaw n s.1 s.2 leaf) _ hne
  intro s hs
  have hEig (i : Fin k) : Tendsto (fun n => D.eigenvalue n (s n).1 ((s n).2 i)) atTop (𝓝 E) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hs, (tendsto_order.mp hδ).2 ε hε] with n hn hδn
    rw [Real.dist_eq]
    exact (hn.2.2.2.1 i).trans_lt hδn
  exact D.BS_twoEdgeLaw_weakConverges_eventually hk P K BS (fun n => (s n).1)
    (hs.mono (fun n hn => hn.1)) (fun n => (s n).2)
    (hs.mono (fun n hn => hn.2.1)) (hs.mono (fun n hn => hn.2.2.1))
    (fun _ => E) (Eventually.of_forall (fun _ => hE)) E hE tendsto_const_nhds hEig M
    (hs.mono (fun n hn => hn.2.2.2.2)) leaf F

end GeneralizedBulk.External.RegularSpectralData
