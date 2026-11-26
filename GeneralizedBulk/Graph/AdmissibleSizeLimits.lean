import GeneralizedBulk.ProvedRegularGraphUniversality

/-!
The article's limit along the admissible positive graph sizes, expressed
directly as a filter on the size `M`. The conversion from the sequence endpoint
uses the sequential criterion for countably generated filters. In particular,
no uniformity or additional analytic estimate is assumed here.

The target `sineOneLaw` is the standard Gaussian-beta bulk-limit definition:
the vendored `RationalBulk.gaussianBeta_vague_full_convergence` proves that its
beta-one specialization is the full limit of the normalized Lebesgue-density
ensembles `exp(-sum x_i^2/(4M)) * product_{i<j} |x_i-x_j|`.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology

namespace GeneralizedBulk.External

/-- Weak convergence of laws along a specified index filter, tested by every
bounded continuous real function on the state space. -/
def WeakLawConvergesAlong {I V : Type*} [TopologicalSpace V] [MeasurableSpace V]
    (laws : I → Measure V) (sizes : Filter I) (limit : Measure V) : Prop :=
  ∀ F : BoundedContinuousFunction V ℝ,
    Tendsto (fun M => ∫ x, F x ∂laws M) sizes (𝓝 (∫ x, F x ∂limit))

end GeneralizedBulk.External

namespace GeneralizedBulk.Graph
open External

/-- A positive size for which the literal labelled simple regular-graph
ensemble is nonempty. -/
def AdmissibleSize (d M : ℕ) : Prop :=
  0 < M ∧ Nonempty (RegularGraph M d)

/-- Size tends to infinity while ranging over precisely the admissible
positive sizes of the graph ensemble. -/
def admissibleSizeFilter (d : ℕ) : Filter ℕ :=
  atTop ⊓ principal {M | AdmissibleSize d M}

instance (d : ℕ) : IsCountablyGenerated (admissibleSizeFilter d) := by
  unfold admissibleSizeFilter
  infer_instance

/-- An eventual statement valid on every admissible sequence is valid directly
along the admissible-size filter. The property is arbitrary. -/
theorem eventually_admissibleSizeFilter_of_sequences (d : ℕ) (p : ℕ → Prop)
    (h : ∀ (N : ℕ → ℕ), (∀ n,0<N n) → Tendsto N atTop atTop →
      (∀ n,Nonempty (RegularGraph (N n) d)) → ∀ᶠ n in atTop,p (N n)) :
    ∀ᶠ M in admissibleSizeFilter d,p M := by
  apply Filter.eventually_iff_seq_eventually.mpr
  intro N hN
  have hparts : Tendsto N atTop atTop ∧
      ∀ᶠ n in atTop, AdmissibleSize d (N n) := by
    simpa only [admissibleSizeFilter, tendsto_inf, tendsto_principal, mem_setOf_eq] using hN
  obtain ⟨k,hk⟩ := Filter.eventually_atTop.mp hparts.2
  let sizes : ℕ → ℕ := fun n => N (n+k)
  have hsize (n : ℕ) : AdmissibleSize d (sizes n) := hk (n+k) (by omega)
  have hlim : Tendsto sizes atTop atTop := hparts.1.comp (tendsto_add_atTop_nat k)
  have hshift : ∀ᶠ n in atTop,p (N (n+k)) :=
    h sizes (fun n => (hsize n).1) hlim (fun n => (hsize n).2)
  rw [← Filter.map_add_atTop_eq_nat k]
  exact hshift

/-- The literal fixed-degree and fixed-energy bulk limit, with size tending
to infinity through the actual admissible graph sizes. All eigenvalues and
their multiplicities are retained, and the scale is exactly `pi * rho_d(E)`. -/
theorem uniform_regular_graph_bulk_universality_along_admissible_sizes
    (d : ℕ) (hd : 3 ≤ d) (E : ℝ) (hE : E^2 < 4*((d : ℝ)-1)) :
    WeakLawConvergesAlong
      (fun M => Measure.map
        (uniformGraphPointProcess d M E (Real.pi*KestenMcKay.rawDensity d E))
        (regularGraphLaw M d))
      (admissibleSizeFilter d) sineOneLaw := by
  intro F
  apply Filter.tendsto_of_seq_tendsto
  intro N hN
  have hparts : Tendsto N atTop atTop ∧
      ∀ᶠ n in atTop, AdmissibleSize d (N n) := by
    simpa only [admissibleSizeFilter, tendsto_inf, tendsto_principal, mem_setOf_eq] using hN
  obtain ⟨k,hk⟩ := Filter.eventually_atTop.mp hparts.2
  let sizes : ℕ → ℕ := fun n => N (n+k)
  have hsize (n : ℕ) : AdmissibleSize d (sizes n) := hk (n+k) (by omega)
  letI : ∀ n, Nonempty (RegularGraph (sizes n) d) := fun n => (hsize n).2
  have hlim : Tendsto sizes atTop atTop :=
    hparts.1.comp (tendsto_add_atTop_nat k)
  have h := uniform_regular_graph_bulk_universality d hd sizes (fun n => (hsize n).1) hlim E hE F
  exact (tendsto_add_atTop_iff_nat k).mp h

end GeneralizedBulk.Graph
