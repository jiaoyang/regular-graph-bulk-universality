import GeneralizedBulk.Graph.FixedEnergyWassersteinFinite
import GeneralizedBulk.Graph.ArithmeticAdmissibility

/-! Revised Corollary 1.3, with the literal arithmetic size domain of the
article. The limiting Gaussian product is fixed at E throughout the supremum.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace GeneralizedBulk.Graph

/-- The ordinary real-valued supremum in the article. Finiteness is proved
before converting the extended nonnegative presentation to a real number. -/
def fixedEnergyStarWassersteinSupReal {d M k : ℕ} (hd : 3 ≤ d)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    (g : RegularGraph M d) (δ : ℝ) : ℝ :=
  (fixedEnergyStarWassersteinSup (k := k) hd E hE g δ).toReal

theorem ofReal_fixedEnergyStarWassersteinSupReal {d M k : ℕ} (hd : 3 ≤ d)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    (g : RegularGraph M d) (δ : ℝ) :
    ENNReal.ofReal (fixedEnergyStarWassersteinSupReal (k := k) hd E hE g δ) =
      fixedEnergyStarWassersteinSup (k := k) hd E hE g δ :=
  ENNReal.ofReal_toReal (ne_of_lt (fixedEnergyStarWassersteinSup_lt_top hd E hE g δ))

theorem measurable_fixedEnergyStarWassersteinSupReal {d M k : ℕ} (hd : 3 ≤ d)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1)) (δ : ℝ) :
    Measurable (fun g : RegularGraph M d =>
      fixedEnergyStarWassersteinSupReal (k := k) hd E hE g δ) :=
  measurable_of_finite _

theorem fixedEnergyStarWassersteinSupReal_eq_zero_of_empty {d M k : ℕ} (hd : 3 ≤ d)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    (g : RegularGraph M d) (δ : ℝ)
    (h : ¬ ∃ A : GraphEigenCandidate d M k g, FixedEnergyWindow A E δ) :
    fixedEnergyStarWassersteinSupReal (k := k) hd E hE g δ = 0 := by
  rw [fixedEnergyStarWassersteinSupReal,
    fixedEnergyStarWassersteinSup_eq_zero_of_empty hd E hE g δ h, ENNReal.toReal_zero]

/-- Corollary 1.3 of the revised article: the physical W₂ supremum over all
ordered orthonormal eigenvector tuples in the shrinking window about E tends
to zero in graph probability, as M tends to infinity through M>d with M*d even.
No graph-existence, BS/HY, moment or Gaussianity premise is required. -/
theorem corollary_1_3
    (d : ℕ) (hd : 3 ≤ d) (k : ℕ) (hk : 0 < k)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    (δ : ℕ → ℝ) (hδnonneg : ∀ M, 0 ≤ δ M) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun M =>
      (regularGraphLaw M d {g |
        ε ≤ fixedEnergyStarWassersteinSup (k := k) hd E hE g (δ M)}).toReal)
      (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) (𝓝 0) := by
  intro ε hε
  rw [← admissibleSizeFilter_eq_arithmetic d]
  apply Filter.tendsto_of_seq_tendsto
  intro N hN
  have hparts : Tendsto N atTop atTop ∧
      ∀ᶠ n in atTop, AdmissibleSize d (N n) := by
    simpa only [admissibleSizeFilter, tendsto_inf, tendsto_principal, Set.mem_setOf_eq] using hN
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hparts.2
  let sizes : ℕ → ℕ := fun n => N (n+T)
  have hsize (n : ℕ) : AdmissibleSize d (sizes n) := hT (n+T) (by omega)
  letI : ∀ n, Nonempty (RegularGraph (sizes n) d) := fun n => (hsize n).2
  have hlim : Tendsto sizes atTop atTop :=
    hparts.1.comp (tendsto_add_atTop_nat T)
  have h := uniform_graph_star_wasserstein_fixed_energy_sup d hd sizes
    (fun n => (hsize n).1) hlim k hk E hE (fun n => δ (sizes n))
    (fun n => hδnonneg (sizes n)) (hδ.comp hlim) ε hε
  exact (tendsto_add_atTop_iff_nat T).mp h

/-- The real-valued form of revised Corollary 1.3, with exactly the arithmetic
size domain and positive real thresholds used for convergence in probability. -/
theorem corollary_1_3_real
    (d : ℕ) (hd : 3 ≤ d) (k : ℕ) (hk : 0 < k)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    (δ : ℕ → ℝ) (hδnonneg : ∀ M, 0 ≤ δ M) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun M =>
      (regularGraphLaw M d {g |
        ε ≤ fixedEnergyStarWassersteinSupReal (k := k) hd E hE g (δ M)}).toReal)
      (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) (𝓝 0) := by
  intro ε hε
  have hconv := corollary_1_3 d hd k hk E hE δ hδnonneg hδ
    (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  have hvalid : ∀ᶠ M : ℕ in atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)},
      d < M ∧ Even (M*d) := by
    rw [eventually_inf_principal]
    exact Eventually.of_forall (fun _ hM => hM)
  apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) ?_ hconv
  filter_upwards [hvalid] with M hM
  letI : Nonempty (RegularGraph M d) := regularGraph_nonempty_of_arithmetic d M hM.1 hM.2
  letI : IsProbabilityMeasure (regularGraphLaw M d) := regularGraphLaw_isProbability M d
  apply ENNReal.toReal_mono (measure_ne_top (regularGraphLaw M d) _)
  apply measure_mono
  intro g hg
  exact (ENNReal.ofReal_le_ofReal hg).trans_eq
    (ofReal_fixedEnergyStarWassersteinSupReal hd E hE g (δ M))

/-- The width sequence need only be nonnegative and tend to zero at sizes
where the graph ensemble exists. Its values at all other sizes are irrelevant. -/
theorem corollary_1_3_along_sizes
    (d : ℕ) (hd : 3 ≤ d) (k : ℕ) (hk : 0 < k)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    (δ : ℕ → ℝ)
    (hδnonneg : ∀ M, d < M → Even (M*d) → 0 ≤ δ M)
    (hδ : Tendsto δ (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) (𝓝 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun M =>
      (regularGraphLaw M d {g |
        ε ≤ fixedEnergyStarWassersteinSup (k := k) hd E hE g (δ M)}).toReal)
      (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) (𝓝 0) := by
  intro ε hε
  rw [← admissibleSizeFilter_eq_arithmetic d]
  apply Filter.tendsto_of_seq_tendsto
  intro N hN
  have hparts : Tendsto N atTop atTop ∧
      ∀ᶠ n in atTop, AdmissibleSize d (N n) := by
    simpa only [admissibleSizeFilter, tendsto_inf, tendsto_principal, Set.mem_setOf_eq] using hN
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hparts.2
  let sizes : ℕ → ℕ := fun n => N (n+T)
  have hsize (n : ℕ) : AdmissibleSize d (sizes n) := hT (n+T) (by omega)
  have harith (n : ℕ) : d < sizes n ∧ Even (sizes n*d) :=
    (admissibleSize_iff_arithmetic d (sizes n)).mp (hsize n)
  letI : ∀ n, Nonempty (RegularGraph (sizes n) d) := fun n => (hsize n).2
  have hlim : Tendsto sizes atTop atTop :=
    hparts.1.comp (tendsto_add_atTop_nat T)
  have hlimSizes : Tendsto sizes atTop
      (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) :=
    tendsto_inf.mpr ⟨hlim, tendsto_principal.mpr (Eventually.of_forall harith)⟩
  have h := uniform_graph_star_wasserstein_fixed_energy_sup d hd sizes
    (fun n => (hsize n).1) hlim k hk E hE (fun n => δ (sizes n))
    (fun n => hδnonneg (sizes n) (harith n).1 (harith n).2) (hδ.comp hlimSizes) ε hε
  exact (tendsto_add_atTop_iff_nat T).mp h

/-- Corollary 1.3 with real thresholds and width convergence solely through
the article's admissible sizes, without any off-domain condition on delta. -/
theorem corollary_1_3_real_along_sizes
    (d : ℕ) (hd : 3 ≤ d) (k : ℕ) (hk : 0 < k)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    (δ : ℕ → ℝ)
    (hδnonneg : ∀ M, d < M → Even (M*d) → 0 ≤ δ M)
    (hδ : Tendsto δ (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun M =>
      (regularGraphLaw M d {g |
        ε ≤ fixedEnergyStarWassersteinSupReal (k := k) hd E hE g (δ M)}).toReal)
      (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) (𝓝 0) := by
  intro ε hε
  have hconv := corollary_1_3_along_sizes d hd k hk E hE δ hδnonneg hδ
    (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  have heq (M : ℕ) :
      {g : RegularGraph M d | ε ≤ fixedEnergyStarWassersteinSupReal (k := k) hd E hE g (δ M)} =
      {g | ENNReal.ofReal ε ≤ fixedEnergyStarWassersteinSup (k := k) hd E hE g (δ M)} := by
    ext g
    constructor
    · intro hg
      exact (ENNReal.ofReal_le_ofReal hg).trans_eq
        (ofReal_fixedEnergyStarWassersteinSupReal hd E hE g (δ M))
    · intro hg
      have h := ENNReal.toReal_mono
        (ne_of_lt (fixedEnergyStarWassersteinSup_lt_top (k := k) hd E hE g (δ M))) hg
      simpa only [ENNReal.toReal_ofReal hε.le] using h
  simpa only [heq] using hconv

end GeneralizedBulk.Graph
