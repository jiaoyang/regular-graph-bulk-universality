import GeneralizedBulk.Graph.WindowEigenSelection
import GeneralizedBulk.Graph.StarFourthNorm
import GeneralizedBulk.Graph.MeasurableGaussianMarks

/-!
BS factorization on every actual retained-count stratum. The arbitrary scalar
test is supported on that stratum; a nearby bulk padding list supplies a
globally admissible selection without declaring the stratum high probability.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def windowCountWeight (n : ℕ) (E sigma R : ℝ) (m : ℕ) (H : Ω → ℂ) (ω : Ω) : ℂ :=
  if D.windowEigenCount n ω E sigma (-R) R = m then H ω else 0

theorem measurable_windowCountWeight (n : ℕ) (E sigma R : ℝ) (m : ℕ)
    (H : Ω → ℂ) (hH : Measurable H) : Measurable (D.windowCountWeight n E sigma R m H) :=
  Measurable.ite ((D.measurable_windowEigenCount n E sigma (-R) R) (measurableSet_singleton m))
    hH measurable_const

/-- The retained-count event may have any probability. Qualitative BS is
applied on the common graph good event, using actual one-color fourth
moments and a nearby measurable padding selection. -/
theorem BS_window_count_factorization {m : ℕ} (hm : 0 < m) [Nonempty Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : Set ℝ) (BS : BSQualitativeInput D P K)
    (E sigma R : ℝ) (hsigma : 0 < sigma) (hE : E ∈ K) (hEd : E ≠ (d : ℝ))
    (delta : ℕ → ℝ) (hdelta : Tendsto delta atTop (𝓝 0))
    (hwindow : ∀ᶠ n in atTop, microscopicStep (N n) sigma * R ≤ delta n)
    (good : ℕ → Set Ω) (hgood : ∀ n, MeasurableSet (good n))
    (hbad : Tendsto (fun n => (P (good n)ᶜ).toReal) atTop (𝓝 0))
    (hBS : ∀ᶠ n in atTop, good n ⊆ BS.good m n)
    (fallback : ∀ n, Ω → Fin m → Fin (N n))
    (hmeas : ∀ n i, Measurable (fun ω => fallback n ω i))
    (hfallback : ∀ᶠ n in atTop, ∀ ω ∈ good n,
      Function.Injective (fallback n ω) ∧
      (∀ i, fallback n ω i ≠ ⟨0,D.size_pos n⟩) ∧
      (∀ i, |D.eigenvalue n ω (fallback n ω i) - E| ≤ delta n))
    (hfourth : ∀ᶠ n in atTop, ∀ ω ∈ good n, ∀ k : Fin (N n),
      k ≠ ⟨0,D.size_pos n⟩ → |D.eigenvalue n ω k - E| ≤ delta n → ∀ j : Fin (d + 1),
      |D.empiricalFourthWickDiscrepancy n ω (fun _ : Fin 1 => k) (0,j) (0,j) (0,j) (0,j)| ≤ 1)
    (leaf : Fin d) (F : BoundedContinuousFunction ((Fin m × Fin 4) → ℝ) ℝ)
    (H : ℕ → Ω → ℂ) (hH : ∀ n, Measurable (H n)) (C : ℝ) (hC : ∀ n ω, ‖H n ω‖ ≤ C) :
    Tendsto (fun n => (∫ ω, D.windowCountWeight n E sigma R m (H n) ω *
      (↑(∫ x, F x ∂D.twoEdgeLaw n ω
        (D.paddedWindowSelection n ω E sigma (-R) R (fallback n)) leaf) : ℂ) ∂P) -
      (∫ ω, D.windowCountWeight n E sigma R m (H n) ω ∂P) *
        (↑(∫ x, F x ∂Gaussian.finiteMarkLaw (E / d) m) : ℂ)) atTop (𝓝 0) := by
  let selection := fun n ω => D.paddedWindowSelection n ω E sigma (-R) R (fallback n)
  let M : ℝ := ((m * (d + 1) : ℕ) : ℝ) * 4
  have hsel (n i) : Measurable (fun ω => selection n ω i) :=
    D.measurable_paddedWindowSelection n E sigma (-R) R (fallback n) (hmeas n) i
  have hadmissible : ∀ᶠ n in atTop, ∀ ω ∈ good n,
      D.GoodEigenSelection P K BS delta M E n (ω,selection n ω) := by
    filter_upwards [hBS,hfallback,hfourth,hwindow,
      D.windowEigenIndex_nonconstant_eventually E sigma R hsigma hEd] with n hbs hf hfour hw hnon
    intro ω hω
    have hprops : Function.Injective (selection n ω) ∧
        (∀ i, selection n ω i ≠ ⟨0,D.size_pos n⟩) ∧
        (∀ i, |D.eigenvalue n ω (selection n ω i) - E| ≤ delta n) := by
      by_cases hc : m ≤ D.windowEigenCount n ω E sigma (-R) R
      · have heq : selection n ω = fun i => D.windowEigenIndex n ω E sigma (-R) R i.val := by
          simp only [selection,paddedWindowSelection,hc,ite_true]
        rw [heq]
        exact ⟨D.windowEigenIndex_injective n ω E sigma (-R) R hsigma hc,
          fun i => hnon ω i.val (i.isLt.trans_le hc),
          fun i => (D.windowEigenIndex_near n ω E sigma R hsigma i.val (i.isLt.trans_le hc)).trans hw⟩
      · simpa only [selection,paddedWindowSelection,hc,ite_false] using hf ω hω
    refine ⟨hbs hω,hprops.1,hprops.2.1,hprops.2.2,?_⟩
    have hb := D.starLaw_norm_fourth_le_of_one_color_Wick n ω hm (selection n ω) 1
      (fun a j => hfour ω hω _ (hprops.2.1 a) (hprops.2.2 a) j)
    simpa only [M,show (3 : ℝ) + 1 = 4 by norm_num] using hb
  have hC0 : 0 ≤ C := (norm_nonneg (H 0 (Classical.choice (inferInstance : Nonempty Ω)))).trans
    (hC 0 (Classical.choice (inferInstance : Nonempty Ω)))
  apply D.BS_bounded_scalar_mark_factorization hm P K BS delta hdelta M E hE selection hsel
    good hgood hbad hadmissible leaf F
    (fun n => D.windowCountWeight n E sigma R m (H n))
    (fun n => D.measurable_windowCountWeight n E sigma R m (H n) (hH n)) C
  intro n ω
  unfold windowCountWeight
  split_ifs
  · exact hC n ω
  · simpa only [norm_zero] using hC0

end GeneralizedBulk.External.RegularSpectralData
