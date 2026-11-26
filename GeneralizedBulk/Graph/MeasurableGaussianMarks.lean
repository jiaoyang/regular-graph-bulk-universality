import GeneralizedBulk.Graph.UniformGaussianLimits

/-! Measurable empirical mark kernels and factorization against the full scalar state. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators Classical

namespace GeneralizedBulk.Graph

theorem measurable_finite_eval {S ι : Type*} [MeasurableSpace S] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (f : S → ι → ℝ) (hf : ∀ i, Measurable (fun s => f s i))
    (g : S → ι) (hg : Measurable g) : Measurable (fun s => f s (g s)) := by
  have heq : (fun s => f s (g s)) = (fun s => ∑ i : ι, if g s = i then f s i else 0) := by
    funext s
    simp
  rw [heq]
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite (by
    change MeasurableSet (g ⁻¹' ({i} : Set ι))
    exact hg (measurableSet_singleton i))
    (hf i) measurable_const

theorem abs_integral_bounded_test {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (F : BoundedContinuousFunction E ℝ) :
    |∫ x, F x ∂μ| ≤ ‖F‖ := by
  simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall (fun x => F.norm_coe_le_norm x))

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ)

theorem measurable_selectedEigenvector
    (a v : Ω → Fin (N n)) (ha : Measurable a) (hv : Measurable v) :
    Measurable (fun ω => D.eigenvector n ω (a ω) (v ω)) := by
  apply Graph.measurable_finite_eval
    (fun ω w => D.eigenvector n ω (a ω) w) _ v hv
  intro w
  exact Graph.measurable_finite_eval (fun ω i => D.eigenvector n ω i w)
    (fun i => D.measurable_eigenvector n i w) a ha

theorem measurable_selectedStarSample {k : ℕ} (a : Ω → Fin k → Fin (N n))
    (ha : ∀ i, Measurable (fun ω => a ω i)) (sample : Fin (N n) × Equiv.Perm (Fin d)) :
    Measurable (fun ω => D.starSample n ω (fun i => D.eigenvector n ω (a ω i)) sample) := by
  apply measurable_pi_lambda
  rintro ⟨i, j⟩
  refine Fin.cases ?_ (fun j => ?_) j
  · exact (D.measurable_selectedEigenvector n (fun ω => a ω i) (fun _ => sample.1)
      (ha i) measurable_const).const_mul _
  · exact (D.measurable_selectedEigenvector n (fun ω => a ω i)
      (fun ω => D.neighbor n ω sample.1 (sample.2 j)) (ha i)
      (D.measurable_neighbor n sample.1 (sample.2 j))).const_mul _

def twoStarSampleMark {k : ℕ} (ω : Ω) (q : Fin k → Fin (N n) → ℝ)
    (s t : Fin (N n) × Equiv.Perm (Fin d)) (leaf : Fin d) : (Fin k × Fin 4) → ℝ :=
  (Gaussian.starEndpointRestriction (k := k) leaf).mulVec
    (Gaussian.mergeVectors (D.starSample n ω q s, D.starSample n ω q t))

theorem integral_twoEdgeLaw_finite {k : ℕ} (ω : Ω) (a : Fin k → Fin (N n))
    (leaf : Fin d) (F : BoundedContinuousFunction ((Fin k × Fin 4) → ℝ) ℝ) :
    (∫ x, F x ∂D.twoEdgeLaw n ω a leaf) =
      ((Fintype.card (Fin (N n) × Equiv.Perm (Fin d)) : ℝ)⁻¹) ^ 2 *
        ∑ s, ∑ t, F (D.twoStarSampleMark n ω (fun i => D.eigenvector n ω (a i)) s t leaf) := by
  let μ := D.starLaw n ω (fun i => D.eigenvector n ω (a i))
  letI : IsProbabilityMeasure μ := D.starLaw_isProbability n ω _
  let R := Gaussian.starEndpointRestriction (k := k) leaf
  have hm : AEStronglyMeasurable (fun x => F (R.mulVec x)) (Gaussian.vectorProductLaw μ μ) :=
    (F.compContinuous ⟨_, Gaussian.continuous_finiteMatrixAction R⟩).continuous.aestronglyMeasurable
  have hi : Integrable (fun xy => F (R.mulVec (Gaussian.mergeVectors xy))) (μ.prod μ) :=
    (F.compContinuous ⟨_, (Gaussian.continuous_finiteMatrixAction R).comp Gaussian.continuous_mergeVectors⟩).integrable _
  rw [twoEdgeLaw, integral_map (Gaussian.measurable_finiteMatrixAction R).aemeasurable F.continuous.aestronglyMeasurable,
    Gaussian.vectorProductLaw, integral_map Gaussian.continuous_mergeVectors.measurable.aemeasurable hm,
    integral_prod _ hi]
  dsimp only [μ]
  simp_rw [D.integral_starLaw n ω (fun i => D.eigenvector n ω (a i))]
  rw [← Finset.mul_sum]
  dsimp only [twoStarSampleMark]
  ring

theorem measurable_twoEdgeLaw_test {k : ℕ} (a : Ω → Fin k → Fin (N n))
    (ha : ∀ i, Measurable (fun ω => a ω i)) (leaf : Fin d)
    (F : BoundedContinuousFunction ((Fin k × Fin 4) → ℝ) ℝ) :
    Measurable (fun ω => ∫ x, F x ∂D.twoEdgeLaw n ω (a ω) leaf) := by
  have heq : (fun ω => ∫ x, F x ∂D.twoEdgeLaw n ω (a ω) leaf) =
      (fun ω => ((Fintype.card (Fin (N n) × Equiv.Perm (Fin d)) : ℝ)⁻¹) ^ 2 *
        ∑ s, ∑ t, F (D.twoStarSampleMark n ω (fun i => D.eigenvector n ω (a ω i)) s t leaf)) :=
    funext (fun ω => D.integral_twoEdgeLaw_finite n ω (a ω) leaf F)
  rw [heq]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro s hs
  apply Finset.measurable_sum
  intro t ht
  apply F.continuous.measurable.comp
  exact (Gaussian.measurable_finiteMatrixAction (Gaussian.starEndpointRestriction leaf)).comp
    (Gaussian.continuous_mergeVectors.measurable.comp
      ((D.measurable_selectedStarSample n a ha s).prodMk (D.measurable_selectedStarSample n a ha t)))

/-- Arbitrary bounded measurable tests of the full scalar state factor from
the actual empirical two-edge mark kernel. Admissibility is required only on
the common high-probability graph event. -/
theorem BS_bounded_scalar_mark_factorization {k : ℕ} (hk : 0 < k) [Nonempty Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : Set ℝ) (BS : BSQualitativeInput D P K)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (M E : ℝ) (hE : E ∈ K)
    (a : ∀ n, Ω → Fin k → Fin (N n)) (ha : ∀ n i, Measurable (fun ω => a n ω i))
    (good : ℕ → Set Ω) (hgood : ∀ n, MeasurableSet (good n))
    (hbad : Tendsto (fun n => (P (good n)ᶜ).toReal) atTop (𝓝 0))
    (hadmissible : ∀ᶠ n in atTop, ∀ ω ∈ good n, D.GoodEigenSelection P K BS δ M E n (ω, a n ω))
    (leaf : Fin d) (F : BoundedContinuousFunction ((Fin k × Fin 4) → ℝ) ℝ)
    (H : ℕ → Ω → ℂ) (hH : ∀ n, Measurable (H n)) (C : ℝ) (hC : ∀ n ω, ‖H n ω‖ ≤ C) :
    Tendsto (fun n => (∫ ω, H n ω * (↑(∫ x, F x ∂D.twoEdgeLaw n ω (a n ω) leaf) : ℂ) ∂P) -
      (∫ ω, H n ω ∂P) * (↑(∫ x, F x ∂Gaussian.finiteMarkLaw (E / d) k) : ℂ)) atTop (𝓝 0) := by
  have hne : ∀ᶠ n in atTop, ∃ s : Ω × (Fin k → Fin (N n)), D.GoodEigenSelection P K BS δ M E n s := by
    filter_upwards [hadmissible, (tendsto_order.mp hbad).2 1 (by norm_num)] with n hn hsmall
    by_contra he
    have hEmpty : good n = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro ω hω
      exact he ⟨(ω, a n ω), hn ω hω⟩
    simp only [hEmpty, Set.compl_empty, measure_univ, ENNReal.toReal_one] at hsmall
    linarith
  have hu := D.BS_twoEdgeLaw_uniform_test hk P K BS δ hδ M E hE hne leaf F
  have hμ (n : ℕ) (ω : Ω) : IsProbabilityMeasure (D.twoEdgeLaw n ω (a n ω) leaf) := by
    letI := D.starLaw_isProbability n ω (fun i => D.eigenvector n ω (a n ω i))
    exact MeasureTheory.isProbabilityMeasure_map
      (Gaussian.measurable_finiteMatrixAction (Gaussian.starEndpointRestriction leaf)).aemeasurable
  apply Graph.bounded_scalar_mark_factorization (fun _ => P) good hgood
    (fun n ω => ∫ x, F x ∂D.twoEdgeLaw n ω (a n ω) leaf)
    (fun n => D.measurable_twoEdgeLaw_test n (a n) (ha n) leaf F)
    (∫ x, F x ∂Gaussian.finiteMarkLaw (E / d) k) ‖F‖
    (fun n ω => @Graph.abs_integral_bounded_test _ _ _ _ (hμ n ω) F)
    (Graph.abs_integral_bounded_test _ F) _ hbad H hH C hC
  intro ε hε
  filter_upwards [hu ε hε, hadmissible] with n hn ha
  intro ω hω
  exact hn (ω, a n ω) (ha ω hω)

end GeneralizedBulk.External.RegularSpectralData
