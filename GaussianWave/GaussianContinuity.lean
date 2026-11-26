import GaussianWave.GaussianProduct
import GaussianWave.Compactness

/-!
# Continuity of actual finite Gaussian covariance laws

Entrywise convergence of finite positive semidefinite covariance matrices
implies weak convergence of the constructed Gaussian laws. The proof uses
computed coordinate fourth moments, proved compactness, and characteristic
uniqueness. It does not assume continuity of matrix square roots.

The weak-characteristic compactness argument is adapted from the earlier
project's `GeneralizedBulk/Gaussian/WeakCharacteristic.lean` without importing it.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace GaussianWave

def linearCharacteristic {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    BoundedContinuousFunction (ι → ℝ) ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I))
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_finiteLinearForm t)).mul continuous_const))
    1 (fun x => by simp [Complex.norm_exp])

lemma weakLaw_complex_integral {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E]
    (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hweak : WeakLawConverges μ ν) (f : BoundedContinuousFunction E ℂ) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  let laws : ℕ → ProbabilityMeasure E := fun n => ⟨μ n, inferInstance⟩
  let limit : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have h : Tendsto laws atTop (𝓝 limit) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hweak
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h f

lemma weakLaw_characteristic {ι : Type*} [Fintype ι]
    (μ : ℕ → Measure (ι → ℝ)) (ν : Measure (ι → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hweak : WeakLawConverges μ ν) (t : ι → ℝ) :
    Tendsto (fun n => ∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂μ n)
      atTop (𝓝 (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂ν)) :=
  weakLaw_complex_integral μ ν hweak (linearCharacteristic t)

/-- Pointwise characteristic convergence plus a fourth-moment tightness bound
implies actual bounded-continuous weak convergence. -/
theorem weakLaw_of_characteristic_of_norm_fourth
    {ι : Type*} [Fintype ι] (μ : ℕ → Measure (ι → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν]
    (hi : ∀ n, Integrable (fun x => ‖x‖ ^ 4) (μ n)) (M : ℝ)
    (hM : ∀ n, (∫ x, ‖x‖ ^ 4 ∂μ n) ≤ M)
    (hcf : ∀ t : ι → ℝ,
      Tendsto (fun n => ∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂μ n)
        atTop (𝓝 (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂ν))) :
    WeakLawConverges μ ν := by
  intro F
  apply tendsto_of_subseq_tendsto
  intro r hr
  obtain ⟨t, ht, hrt⟩ := strictMono_subseq_of_tendsto_atTop hr
  let laws : ℕ → ProbabilityMeasure (ι → ℝ) := fun n => ⟨μ (r (t n)), inferInstance⟩
  obtain ⟨ρ, s, hs, hconv⟩ := finite_laws_subsequence_of_uniform_norm_fourth laws
    (fun n => hi (r (t n))) M (fun n => hM (r (t n)))
  let φ := r ∘ t ∘ s
  have hφ : StrictMono φ := hrt.comp hs
  have hweak : WeakLawConverges (fun n => μ (φ n)) (ρ : Measure (ι → ℝ)) := by
    intro G
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv G
  have heq : (ρ : Measure (ι → ℝ)) = ν := by
    apply measure_eq_of_linear_characteristic
    intro a
    exact tendsto_nhds_unique (weakLaw_characteristic _ _ hweak a)
      ((hcf a).comp hφ.tendsto_atTop)
  refine ⟨t ∘ s, ?_⟩
  have h := hweak F
  rw [heq] at h
  exact h

lemma finiteCovarianceQuadratic_tendsto {ι : Type*} [Fintype ι]
    (C : ℕ → Matrix ι ι ℝ) (D : Matrix ι ι ℝ)
    (hCD : ∀ i j, Tendsto (fun n => C n i j) atTop (𝓝 (D i j))) (t : ι → ℝ) :
    Tendsto (fun n => finiteCovarianceQuadratic (C n) t) atTop
      (𝓝 (finiteCovarianceQuadratic D t)) := by
  exact tendsto_finset_sum Finset.univ (fun i _ => tendsto_finset_sum Finset.univ
    (fun j _ => ((hCD i j).const_mul (t i)).mul_const (t j)))

/-- Covariance convergence gives a uniform diagonal bound, including all initial
terms of the sequence and allowing an empty coordinate type. -/
lemma covariance_sequence_diagonal_bound {ι : Type*} [Fintype ι]
    (C : ℕ → Matrix ι ι ℝ) (D : Matrix ι ι ℝ)
    (hCD : ∀ i j, Tendsto (fun n => C n i j) atTop (𝓝 (D i j))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n i, C n i i ≤ B := by
  classical
  have hb (i : ι) : ∃ b : ℝ, ∀ n, C n i i ≤ b := by
    obtain ⟨b, hb⟩ := (hCD i i).bddAbove_range
    exact ⟨b, fun n => hb (Set.mem_range_self n)⟩
  choose b hb using hb
  refine ⟨∑ i, |b i|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro n i
  exact (hb i n).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (b j)) (Finset.mem_univ i)))

/-- The canonical Gaussian targets vary weakly continuously with their finite
covariance matrix, even across changes of rank. -/
theorem gaussianCovarianceLaw_weakConverges {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : ℕ → Matrix ι ι ℝ) (hC : ∀ n, (C n).PosSemidef)
    (D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (hCD : ∀ i j, Tendsto (fun n => C n i j) atTop (𝓝 (D i j))) :
    WeakLawConverges (fun n => gaussianCovarianceLaw (C n) (hC n))
      (gaussianCovarianceLaw D hD) := by
  obtain ⟨B, hB0, hB⟩ := covariance_sequence_diagonal_bound C D hCD
  apply weakLaw_of_characteristic_of_norm_fourth _ _
    (fun n => (gaussianCovarianceLaw_norm_fourth_le (C n) (hC n) B hB0 (hB n)).1)
    (3 * B ^ 2 * (Fintype.card ι : ℝ) ^ 2)
    (fun n => (gaussianCovarianceLaw_norm_fourth_le (C n) (hC n) B hB0 (hB n)).2)
  intro t
  have hq := finiteCovarianceQuadratic_tendsto C D hCD t
  have he := Complex.continuous_exp.continuousAt.tendsto.comp
    (Complex.continuous_ofReal.continuousAt.tendsto.comp (hq.const_mul (-(1 / 2 : ℝ))))
  have hc (n : ℕ) :
      (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I)
        ∂gaussianCovarianceLaw (C n) (hC n)) =
          Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic (C n) t) : ℂ) :=
    gaussianCovarianceLaw_characteristic (C n) (hC n) t
  have hd :
      (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I)
        ∂gaussianCovarianceLaw D hD) =
          Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic D t) : ℂ) :=
    gaussianCovarianceLaw_characteristic D hD t
  simpa only [hc, hd] using he

end GaussianWave
