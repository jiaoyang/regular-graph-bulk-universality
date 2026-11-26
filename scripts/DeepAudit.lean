import GeneralizedBulk
import GaussianWave
import BourgadeHuang
import LocalLaw.Audit
import SpectralConsequences.Audit
import Lean.Util.CollectAxioms

/-! Exact signatures and import-order consistency for the article endpoint and
the constructors that discharge the original input records. These checks are
stronger than searching final types for a list of forbidden constant names.
-/
noncomputable section
set_option linter.unusedVariables false
open Lean Elab Command MeasureTheory Filter
open scoped Topology ENNReal

-- `@` prevents implicit proof or typeclass parameters from being supplied by
-- elaboration. A newly added hypothesis changes this exact function type.
example : ∀ (d : ℕ) (hd : 3 ≤ d) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hlim : Tendsto N atTop atTop) [∀ n, Nonempty (GeneralizedBulk.Graph.RegularGraph (N n) d)]
    (E : ℝ) (hE : E^2 < 4*((d : ℝ)-1)),
    GeneralizedBulk.External.WeakLawConverges (fun n => Measure.map
      (GeneralizedBulk.Graph.uniformGraphPointProcess d (N n) E
        (Real.pi*GeneralizedBulk.KestenMcKay.rawDensity d E))
      (GeneralizedBulk.Graph.regularGraphLaw (N n) d)) GeneralizedBulk.sineOneLaw :=
  @GeneralizedBulk.Graph.uniform_regular_graph_bulk_universality

namespace GeneralizedBulk.External
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]

example : ∀ (D : RegularSpectralData d N Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n, Measure.map (D.spectralRegularGraph n) P = Graph.regularGraphLaw (N n) d)
    (hd : 3 ≤ d), HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)) :=
  @RegularSpectralData.provedHYCoarseInput d N Ω _

example : ∀ (D : RegularSpectralData d N Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n, Measure.map (D.spectralRegularGraph n) P = Graph.regularGraphLaw (N n) d)
    (hd : 3 ≤ d) (K : Set ℝ) (α : ℝ), 0 < α → HYMesoscopicInput D P K α :=
  @RegularSpectralData.provedHYMesoscopicInput d N Ω _

example : ∀ (D : RegularSpectralData d N Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n, Measure.map (D.spectralRegularGraph n) P = Graph.regularGraphLaw (N n) d)
    (hd : 3 ≤ d) (K : Set ℝ) (c : ℝ), 0 < c → c < 1/2 →
    HYLocalStarInput D P K c (KestenMcKay.treeGreenStar d (by exact_mod_cast hd)) :=
  @RegularSpectralData.provedHYLocalStarInput d N Ω _

example : ∀ (D : RegularSpectralData d N Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n, Measure.map (D.spectralRegularGraph n) P = Graph.regularGraphLaw (N n) d)
    (hd : 3 ≤ d), HYGeometryInput D P :=
  @RegularSpectralData.provedHYGeometryInput N Ω _ d

example : ∀ (D : RegularSpectralData d N Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n, Measure.map (D.spectralRegularGraph n) P = Graph.regularGraphLaw (N n) d)
    (hd : 3 ≤ d) (K : Set ℝ), IsCompact K →
    (∀ x ∈ K, |x| < 2*Real.sqrt (d-1 : ℝ)) → BSQualitativeInput D P K :=
  @RegularSpectralData.provedBSQualitativeInput d N Ω _
end GeneralizedBulk.External

namespace GeneralizedBulk.Graph
open GeneralizedBulk.External GeneralizedBulk.Entropy.ChannelRates

example : ∀ (d : ℕ) (hd : 3 ≤ d) (E : ℝ) (hE : E^2 < 4*((d : ℝ)-1)),
    WeakLawConvergesAlong
      (fun M => Measure.map
        (uniformGraphPointProcess d M E (Real.pi*KestenMcKay.rawDensity d E))
        (regularGraphLaw M d))
      (admissibleSizeFilter d) sineOneLaw :=
  @uniform_regular_graph_bulk_universality_along_admissible_sizes

example : ∀ (d : ℕ) (hd : 3 ≤ d) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K, E^2 < 4*((d : ℝ)-1)),
    let χ := mixedFourthUniformExponent d hd
    let C := 4*mixedFourthFailureConstant d
    0 < χ ∧ 0 < C ∧
      (∀ M : ℕ, MeasurableSet (mixedFourthGood d hd M K)) ∧
      (∀ᶠ M : ℕ in admissibleSizeFilter d, 1-C*(M : ℝ)^(-(1/32 : ℝ)) ≤
        (regularGraphLaw M d).real (mixedFourthGood d hd M K)) :=
  @uniform_graph_mixed_fourth_along_admissible_sizes

example : ∀ (d : ℕ) (hd : 3 ≤ d) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K, E^2 < 4*((d : ℝ)-1)),
    ∃ b χ C : ℝ, 0 < b ∧ 0 < χ ∧ 0 < C ∧
      (∀ M : ℕ, MeasurableSet (mixedFourthGood d hd M K)) ∧
      (∀ M : ℕ, AdmissibleSize d M →
        1-C*(M : ℝ)^(-b) ≤ (regularGraphLaw M d).real (mixedFourthGood d hd M K)) ∧
      ∀ M : ℕ, 0 < M → ∀ g ∈ mixedFourthGood d hd M K,
        ∀ k : ℕ, 0 < k → k ≤ 4 →
        ∀ A : GraphEigenCandidate d M k g, (∀ a, A.val.eigenvalue a ∈ K) →
        ∀ j1 j2 j3 j4 : Fin k × Fin (d+1),
          |starFourthDifference A.val (by omega) j1 j2 j3 j4| ≤ C*(M : ℝ)^(-χ) :=
  @article_polynomial_mixed_fourth

example : ∀ d k : ℕ, Nonempty (RegularGraph (k*(d+1)) d) :=
  @regularGraph_nonempty_clique_blocks

example : ∀ d : ℕ, ∃ᶠ M in atTop, AdmissibleSize d M :=
  @frequently_admissibleSize

example (d : ℕ) : NeBot (admissibleSizeFilter d) := inferInstance

example : ∀ (d M : ℕ), d < M → Even (M*d) → Nonempty (RegularGraph M d) :=
  @regularGraph_nonempty_of_arithmetic

example : ∀ (d M : ℕ), 0 < M →
    (Nonempty (RegularGraph M d) ↔ d < M ∧ Even (M*d)) :=
  @regularGraph_nonempty_iff_arithmetic

example : ∀ (d M : ℕ), AdmissibleSize d M ↔ d < M ∧ Even (M*d) :=
  @admissibleSize_iff_arithmetic

example : ∀ d : ℕ,
    admissibleSizeFilter d = atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)} :=
  @admissibleSizeFilter_eq_arithmetic

example : ∀ d : ℕ, NeBot (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) :=
  @arithmeticSizeFilter_neBot

-- Check the literal candidate set and the fixed comparison law as well as
-- the complete theorem type. These checks exclude unnamed moment premises.
example : ∀ (d M k : ℕ) (hd : 3 ≤ d) (E : ℝ)
    (hE : E^2 < 4*((d : ℝ)-1)) (g : RegularGraph M d) (δ : ℝ), ℝ≥0∞ :=
  @fixedEnergyStarWassersteinSup

example {d M k : ℕ} (hd : 3 ≤ d) (E : ℝ)
    (hE : E^2 < 4*((d : ℝ)-1)) (g : RegularGraph M d) (δ : ℝ) :
    fixedEnergyStarWassersteinSup (k := k) hd E hE g δ =
      ⨆ A : GraphEigenCandidate d M k g, ⨆ (_ : ∀ a, |A.val.eigenvalue a-E| ≤ δ),
        GaussianWave.wassersteinTwo A.val.eigenStarLaw
          (commonEnergyStarGaussian d k E (by omega)
            (strictBulk_abs_le_degree d hd E hE)) := rfl

example : ∀ (d M k : ℕ) (hd : 3 ≤ d) (E : ℝ)
    (hE : E^2 < 4*((d : ℝ)-1)) (δ : ℝ),
    Measurable (fun g : RegularGraph M d =>
      fixedEnergyStarWassersteinSup (k := k) hd E hE g δ) :=
  @measurable_fixedEnergyStarWassersteinSup

example : ∀ (d M k : ℕ) (hd : 3 ≤ d) (E : ℝ)
    (hE : E^2 < 4*((d : ℝ)-1)) (g : RegularGraph M d) (δ : ℝ),
    (¬ ∃ A : GraphEigenCandidate d M k g, ∀ a, |A.val.eigenvalue a-E| ≤ δ) →
      fixedEnergyStarWassersteinSup (k := k) hd E hE g δ = 0 :=
  @fixedEnergyStarWassersteinSup_eq_zero_of_empty

example : ∀ (d M k : ℕ) (hd : 3 ≤ d) (E : ℝ)
    (hE : E^2 < 4*((d : ℝ)-1)) (g : RegularGraph M d)
    (A : GraphEigenCandidate d M k g),
    GaussianWave.wassersteinTwoSquared A.val.eigenStarLaw
      (commonEnergyStarGaussian d k E (by omega)
        (strictBulk_abs_le_degree d hd E hE)) ≤
      ENNReal.ofReal (4*(Fintype.card (Fin k × Fin (d+1)) : ℝ)) :=
  @graphEigenCandidate_wassersteinTwoSquared_common_energy_le

example : ∀ (d M k : ℕ) (hd : 3 ≤ d) (E : ℝ)
    (hE : E^2 < 4*((d : ℝ)-1)) (g : RegularGraph M d) (δ : ℝ),
    fixedEnergyStarWassersteinSup (k := k) hd E hE g δ ≤
      ENNReal.ofReal (4*(Fintype.card (Fin k × Fin (d+1)) : ℝ)) ^ (1/2 : ℝ) :=
  @fixedEnergyStarWassersteinSup_le

example : ∀ (d M k : ℕ) (hd : 3 ≤ d) (E : ℝ)
    (hE : E^2 < 4*((d : ℝ)-1)) (g : RegularGraph M d) (δ : ℝ),
    fixedEnergyStarWassersteinSup (k := k) hd E hE g δ < ⊤ :=
  @fixedEnergyStarWassersteinSup_lt_top

example : ∀ (d M k : ℕ) (hd : 3 ≤ d) (E : ℝ)
    (hE : E^2 < 4*((d : ℝ)-1)) (g : RegularGraph M d) (δ : ℝ), ℝ :=
  @fixedEnergyStarWassersteinSupReal

example {d M k : ℕ} (hd : 3 ≤ d) (E : ℝ)
    (hE : E^2 < 4*((d : ℝ)-1)) (g : RegularGraph M d) (δ : ℝ) :
    fixedEnergyStarWassersteinSupReal (k := k) hd E hE g δ =
      (fixedEnergyStarWassersteinSup (k := k) hd E hE g δ).toReal := rfl

example : ∀ (d M k : ℕ) (hd : 3 ≤ d) (E : ℝ)
    (hE : E^2 < 4*((d : ℝ)-1)) (g : RegularGraph M d) (δ : ℝ),
    ENNReal.ofReal (fixedEnergyStarWassersteinSupReal (k := k) hd E hE g δ) =
      fixedEnergyStarWassersteinSup (k := k) hd E hE g δ :=
  @ofReal_fixedEnergyStarWassersteinSupReal

example : ∀ (d M k : ℕ) (hd : 3 ≤ d) (E : ℝ)
    (hE : E^2 < 4*((d : ℝ)-1)) (δ : ℝ),
    Measurable (fun g : RegularGraph M d =>
      fixedEnergyStarWassersteinSupReal (k := k) hd E hE g δ) :=
  @measurable_fixedEnergyStarWassersteinSupReal

example : ∀ (d M k : ℕ) (hd : 3 ≤ d) (E : ℝ)
    (hE : E^2 < 4*((d : ℝ)-1)) (g : RegularGraph M d) (δ : ℝ),
    (¬ ∃ A : GraphEigenCandidate d M k g, ∀ a, |A.val.eigenvalue a-E| ≤ δ) →
      fixedEnergyStarWassersteinSupReal (k := k) hd E hE g δ = 0 :=
  @fixedEnergyStarWassersteinSupReal_eq_zero_of_empty

example : ∀ (d : ℕ) (hd : 3 ≤ d) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hlim : Tendsto N atTop atTop) [∀ n, Nonempty (RegularGraph (N n) d)]
    (k : ℕ) (hk : 0 < k) (E : ℝ) (hE : E^2 < 4*((d : ℝ)-1))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)),
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n =>
      (regularGraphLaw (N n) d {g | ∃ A : GraphEigenCandidate d (N n) k g,
        (∀ a, |A.val.eigenvalue a-E| ≤ δ n) ∧
        ε ≤ GaussianWave.wassersteinTwo A.val.eigenStarLaw
          (commonEnergyStarGaussian d k E (by omega)
            (strictBulk_abs_le_degree d hd E hE))}).toReal) atTop (𝓝 0) :=
  @uniform_graph_star_wasserstein_fixed_energy

example : ∀ (d : ℕ) (hd : 3 ≤ d) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hlim : Tendsto N atTop atTop) [∀ n, Nonempty (RegularGraph (N n) d)]
    (k : ℕ) (hk : 0 < k) (E : ℝ) (hE : E^2 < 4*((d : ℝ)-1))
    (δ : ℕ → ℝ) (hδnonneg : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0)),
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n =>
      (regularGraphLaw (N n) d {g |
        ε ≤ fixedEnergyStarWassersteinSup (k := k) hd E hE g (δ n)}).toReal)
          atTop (𝓝 0) :=
  @uniform_graph_star_wasserstein_fixed_energy_sup

example : ∀ (d : ℕ) (hd : 3 ≤ d) (k : ℕ) (hk : 0 < k)
    (E : ℝ) (hE : E^2 < 4*((d : ℝ)-1))
    (δ : ℕ → ℝ) (hδnonneg : ∀ M, 0 ≤ δ M) (hδ : Tendsto δ atTop (𝓝 0)),
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun M =>
      (regularGraphLaw M d {g |
        ε ≤ fixedEnergyStarWassersteinSup (k := k) hd E hE g (δ M)}).toReal)
      (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) (𝓝 0) :=
  @corollary_1_3

example : ∀ (d : ℕ) (hd : 3 ≤ d) (k : ℕ) (hk : 0 < k)
    (E : ℝ) (hE : E^2 < 4*((d : ℝ)-1))
    (δ : ℕ → ℝ) (hδnonneg : ∀ M, 0 ≤ δ M) (hδ : Tendsto δ atTop (𝓝 0)),
    ∀ ε : ℝ, 0 < ε → Tendsto (fun M =>
      (regularGraphLaw M d {g |
        ε ≤ fixedEnergyStarWassersteinSupReal (k := k) hd E hE g (δ M)}).toReal)
      (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) (𝓝 0) :=
  @corollary_1_3_real

example : ∀ (d : ℕ) (hd : 3 ≤ d) (k : ℕ) (hk : 0 < k)
    (E : ℝ) (hE : E^2 < 4*((d : ℝ)-1)) (δ : ℕ → ℝ)
    (hδnonneg : ∀ M, d < M → Even (M*d) → 0 ≤ δ M)
    (hδ : Tendsto δ (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) (𝓝 0)),
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun M =>
      (regularGraphLaw M d {g |
        ε ≤ fixedEnergyStarWassersteinSup (k := k) hd E hE g (δ M)}).toReal)
      (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) (𝓝 0) :=
  @corollary_1_3_along_sizes

example : ∀ (d : ℕ) (hd : 3 ≤ d) (k : ℕ) (hk : 0 < k)
    (E : ℝ) (hE : E^2 < 4*((d : ℝ)-1)) (δ : ℕ → ℝ)
    (hδnonneg : ∀ M, d < M → Even (M*d) → 0 ≤ δ M)
    (hδ : Tendsto δ (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) (𝓝 0)),
    ∀ ε : ℝ, 0 < ε → Tendsto (fun M =>
      (regularGraphLaw M d {g |
        ε ≤ fixedEnergyStarWassersteinSupReal (k := k) hd E hE g (δ M)}).toReal)
      (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) (𝓝 0) :=
  @corollary_1_3_real_along_sizes

example : ∀ (d : ℕ) (hd : 3 ≤ d) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hlim : Tendsto N atTop atTop) [∀ n, Nonempty (RegularGraph (N n) d)]
    (k : ℕ) (hk : 0 < k) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K, E^2 < 4*((d : ℝ)-1))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)),
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n =>
      (regularGraphLaw (N n) d {g |
        ε ≤ graphStarWassersteinSup (k := k) hd g K (δ n)}).toReal) atTop (𝓝 0) :=
  @uniform_graph_star_wasserstein_sup

example : ∀ (d : ℕ) (hd : 3 ≤ d) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hlim : Tendsto N atTop atTop) [∀ n, Nonempty (RegularGraph (N n) d)]
    (k : ℕ) (hk : 0 < k)
    (A : ∀ n, (g : RegularGraph (N n) d) → GraphEigenCandidate d (N n) k g)
    (E : ℝ) (hE : E^2 < 4*((d : ℝ)-1))
    (henergy : ∀ a (t : ℝ), 0 < t → Tendsto (fun n =>
      (regularGraphLaw (N n) d {g | t ≤ |(A n g).val.eigenvalue a-E|}).toReal)
        atTop (𝓝 0)),
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n =>
      (regularGraphLaw (N n) d {g |
        ε ≤ GaussianWave.wassersteinTwo (A n g).val.eigenStarLaw
          ((A n g).val.eigenStarGaussian (by omega))}).toReal) atTop (𝓝 0) :=
  @selected_graph_star_wasserstein

example : ∀ (d : ℕ) (hd : 3 ≤ d) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hlim : Tendsto N atTop atTop) [∀ n, Nonempty (RegularGraph (N n) d)]
    (k : ℕ) (hk : 0 < k)
    (A : ∀ n, (g : RegularGraph (N n) d) → GraphEigenCandidate d (N n) k g)
    (E : ℝ) (hE : E^2 < 4*((d : ℝ)-1))
    (henergy : ∀ a (t : ℝ), 0 < t → Tendsto (fun n =>
      (regularGraphLaw (N n) d {g | t ≤ |(A n g).val.eigenvalue a-E|}).toReal)
        atTop (𝓝 0)),
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n =>
      (regularGraphLaw (N n) d {g |
        ε ≤ GaussianWave.wassersteinTwo (A n g).val.eigenStarLaw
          (commonEnergyStarGaussian d k E (by omega)
            (strictBulk_abs_le_degree d hd E hE))}).toReal) atTop (𝓝 0) :=
  @selected_graph_star_wasserstein_common_energy

end GeneralizedBulk.Graph

run_cmd do
  let endpoints : Array Name := #[
    `GeneralizedBulk.Graph.uniform_regular_graph_bulk_universality,
    `GeneralizedBulk.External.RegularSpectralData.bulk_universality,
    `GeneralizedBulk.Graph.uniform_graph_star_wasserstein,
    `GeneralizedBulk.Graph.uniform_root_fourth_probability,
    `GeneralizedBulk.Graph.uniform_graph_mixed_fourth,
    `GeneralizedBulk.Graph.uniform_regular_graph_bulk_universality_along_admissible_sizes,
    `GeneralizedBulk.Graph.uniform_graph_mixed_fourth_along_admissible_sizes,
    `GeneralizedBulk.Graph.article_polynomial_mixed_fourth,
    `GeneralizedBulk.Graph.regularGraph_nonempty_clique_blocks,
    `GeneralizedBulk.Graph.frequently_admissibleSize,
    `GeneralizedBulk.Graph.regularGraph_nonempty_of_arithmetic,
    `GeneralizedBulk.Graph.regularGraph_nonempty_iff_arithmetic,
    `GeneralizedBulk.Graph.admissibleSize_iff_arithmetic,
    `GeneralizedBulk.Graph.admissibleSizeFilter_eq_arithmetic,
    `GeneralizedBulk.Graph.arithmeticSizeFilter_neBot,
    `GeneralizedBulk.Graph.uniform_graph_star_wasserstein_sup,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSup,
    `GeneralizedBulk.Graph.measurable_fixedEnergyStarWassersteinSup,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSup_eq_zero_of_empty,
    `GeneralizedBulk.Graph.graphEigenCandidate_wassersteinTwoSquared_common_energy_le,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSup_le,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSup_lt_top,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSupReal,
    `GeneralizedBulk.Graph.ofReal_fixedEnergyStarWassersteinSupReal,
    `GeneralizedBulk.Graph.measurable_fixedEnergyStarWassersteinSupReal,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSupReal_eq_zero_of_empty,
    `GeneralizedBulk.Graph.uniform_graph_star_wasserstein_fixed_energy,
    `GeneralizedBulk.Graph.uniform_graph_star_wasserstein_fixed_energy_sup,
    `GeneralizedBulk.Graph.corollary_1_3,
    `GeneralizedBulk.Graph.corollary_1_3_real,
    `GeneralizedBulk.Graph.corollary_1_3_along_sizes,
    `GeneralizedBulk.Graph.corollary_1_3_real_along_sizes,
    `GeneralizedBulk.Graph.selected_graph_star_wasserstein,
    `GeneralizedBulk.Graph.selected_graph_star_wasserstein_common_energy,
    `GeneralizedBulk.External.RegularSpectralData.provedBSQualitativeInput,
    `GeneralizedBulk.External.RegularSpectralData.provedHYCoarseInput,
    `GeneralizedBulk.External.RegularSpectralData.provedHYMesoscopicInput,
    `GeneralizedBulk.External.RegularSpectralData.provedHYLocalStarInput,
    `GeneralizedBulk.External.RegularSpectralData.provedHYGeometryInput]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for endpoint in endpoints do
    let info ← getConstInfo endpoint
    let axioms ← collectAxioms endpoint
    for a in axioms do
      unless allowed.contains a do
        throwError "Unexpected endpoint axiom {a} at {endpoint}"
    liftTermElabM do
      Meta.forallTelescope info.type fun parameters _ => do
        logInfo m!"Exact endpoint inventory: {endpoint}; {parameters.size} parameters; universes {info.levelParams}; axioms {axioms}"
        for parameter in parameters do
          let decl ← parameter.fvarId!.getDecl
          let domain ← Meta.ppExpr decl.type
          logInfo m!"{decl.userName} ({repr decl.binderInfo}): {domain}"
  logInfo "PASSED: exact literal uniform-graph, arithmetic admissibility, all-size mixed-fourth, fixed-energy Corollary 1.3, supremum, selected-tuple and all five BS/HY constructor signatures contain only the declared model and parameter hypotheses; arithmetic size filters have explicit nonvacuity witnesses."

run_cmd do
  let original ← getEnv
  let roots : Array Name := #[`GeneralizedBulk, `GaussianWave, `BourgadeHuang,
    `LocalLaw, `SpectralConsequences]
  let alternate ← liftM <| importModules #[
    {module := `SpectralConsequences.Audit}, {module := `LocalLaw.Audit},
    {module := `BourgadeHuang}, {module := `GaussianWave},
    {module := `GeneralizedBulk}] {} 0
  let mut compared := 0
  let mut alternateCount := 0
  let mut originChanges := 0
  for (name, info) in original.constants.toList do
    if let some idx := original.getModuleIdxFor? name then
      let moduleName := original.header.moduleNames[idx.toNat]!
      if roots.any (·.isPrefixOf moduleName) then
        if !info.isUnsafe && !info.isPartial then
          let some other := alternate.toKernelEnv.find? name
            | throwError "Import order lost project declaration {name}"
          unless info.type == other.type && info.value? true == other.value? true &&
              info.levelParams == other.levelParams do
            throwError "Import order changed declaration type/body/universes: {name}"
          compared := compared + 1
          if let some otherIdx := alternate.getModuleIdxFor? name then
            let otherModule := alternate.header.moduleNames[otherIdx.toNat]!
            if moduleName != otherModule then
              originChanges := originChanges + 1
              logInfo m!"Identical shared declaration changes import-origin attribution: {name}: {moduleName} / {otherModule}"
          else
            throwError "Alternate import environment has no project origin for {name}"
  for (name, info) in alternate.constants.toList do
    if let some idx := alternate.getModuleIdxFor? name then
      let moduleName := alternate.header.moduleNames[idx.toNat]!
      if roots.any (·.isPrefixOf moduleName) then
        if !info.isUnsafe && !info.isPartial then
          alternateCount := alternateCount + 1
  unless compared == alternateCount do
    throwError "Root import order changed the safe local declaration set: {compared} / {alternateCount}"
  logInfo m!"PASSED: {compared} safe local declarations have identical types, bodies and universes under reversed root-import order; {originChanges} shared declaration origin changes."
