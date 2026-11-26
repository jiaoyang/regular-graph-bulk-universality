import GeneralizedBulk.RegularGraphUniversality
import GeneralizedBulk.LocalLaw.ProvedCoarseInput
import GeneralizedBulk.LocalLaw.ProvedLocalStarInput
import GeneralizedBulk.LocalLaw.ProvedGeometryInput
import GeneralizedBulk.Graph.UniformEnsemble

/-! Bulk universality with all BS and HY estimates proved internally, followed
by the literal uniform finite-graph ensemble statement. Only model parameters
and the strict bulk-energy condition remain. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Full-sequence bulk point-process universality for the original uniform
graph marginal, with no BS, HY, moment or Gaussianity premise. -/
theorem bulk_universality (D : RegularSpectralData d N Ω)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P = regularGraphLaw (N n) d)
    (hd : 3 ≤ d) (E : ℝ) (hE : E^2 < 4*((d : ℝ)-1)) :
    let parameters := Parameters.regular d E (by exact_mod_cast hd) hE
    WeakLawConverges (fun n => P.map
      (fun ω => (D.microscopicCountingState n ω E parameters.scale parameters.center).val.1))
      sineOneLaw := by
  let HC := D.provedHYCoarseInput P hUniform hd
  obtain ⟨K,gap,L,hK,_hEK,hgap,hbulk,hwindow,hL⟩ :=
    exists_compact_bulk_window d E hE
  let c := entropyHeight 2 d HC.rigidity_exponent
  have hc := canonical_entropy_height_bounds d HC.rigidity_exponent HC.rigidity_exponent_pos
  change 0 < c ∧ c < channelNoiseExponent (channelTheta 1 d) ∧
    c < channelNoiseExponent (channelTheta 2 d) ∧ c < HC.rigidity_exponent ∧ c ≤ 1/16 at hc
  let HL := D.provedHYLocalStarInput P hUniform hd K c hc.1 (by linarith [hc.2.2.2.2])
  let HG := D.provedHYGeometryInput P hUniform hd
  exact D.bulk_universality_of_HY P hUniform hd HC K hK hbulk c
    hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2 HL E hE gap hgap hwindow L hL HG

end GeneralizedBulk.External.RegularSpectralData

namespace GeneralizedBulk.Graph
open GeneralizedBulk.External

/-- The actual microscopic eigenvalue counting measure of a finite graph.
The distinguished mode and all multiplicities are retained. -/
def uniformGraphPointProcess (d M : ℕ) (E sigma : ℝ)
    (g : RegularGraph M d) : LocalCountingMeasure :=
  finiteCountingConfiguration (fun i => (M : ℝ)*sigma*(CanonicalSpectrum.graphValue g i-E))

theorem measurable_uniformGraphPointProcess (d M : ℕ) (E sigma : ℝ) :
    Measurable (uniformGraphPointProcess d M E sigma) := measurable_of_finite _

/-- The article's fixed-degree bulk theorem for the literal uniform law on
all labelled simple regular graphs, along every positive admissible size
sequence. The only inputs describe this ensemble and the strict bulk energy. -/
theorem uniform_regular_graph_bulk_universality_parameters
    (d : ℕ) (hd : 3 ≤ d) (N : ℕ → ℕ) (hN : ∀ n,0 < N n)
    (hlim : Tendsto N atTop atTop) [∀ n,Nonempty (RegularGraph (N n) d)]
    (E : ℝ) (hE : E^2 < 4*((d : ℝ)-1)) :
    let parameters := Parameters.regular d E (by exact_mod_cast hd) hE
    WeakLawConverges (fun n => Measure.map
      (uniformGraphPointProcess d (N n) E parameters.scale) (regularGraphLaw (N n) d))
      sineOneLaw := by
  let D := canonicalSpectralData d N hN hlim
  have h := D.bulk_universality (uniformEnsembleLaw d N)
    (canonicalSpectralData_uniform d N hN hlim) hd E hE
  intro parameters
  change WeakLawConverges (fun n => (uniformEnsembleLaw d N).map
    (fun ω => (D.microscopicCountingState n ω E parameters.scale parameters.center).val.1)) sineOneLaw at h
  have he (n : ℕ) : (uniformEnsembleLaw d N).map
      (fun ω => (D.microscopicCountingState n ω E parameters.scale parameters.center).val.1) =
      (regularGraphLaw (N n) d).map (uniformGraphPointProcess d (N n) E parameters.scale) := by
    have hm := measurable_uniformGraphPointProcess d (N n) E parameters.scale
    rw [← uniformEnsembleLaw_map_eval d N n,Measure.map_map hm (measurable_pi_apply n)]
    rfl
  simpa only [he] using h

/-- The literal normalization displayed in the article: each particle is
N*pi*rho_d(E)*(lambda-E), and the only randomness is the uniform graph. -/
theorem uniform_regular_graph_bulk_universality
    (d : ℕ) (hd : 3 ≤ d) (N : ℕ → ℕ) (hN : ∀ n,0 < N n)
    (hlim : Tendsto N atTop atTop) [∀ n,Nonempty (RegularGraph (N n) d)]
    (E : ℝ) (hE : E^2 < 4*((d : ℝ)-1)) :
    WeakLawConverges (fun n => Measure.map
      (uniformGraphPointProcess d (N n) E (Real.pi*KestenMcKay.rawDensity d E))
      (regularGraphLaw (N n) d)) sineOneLaw := by
  have h := uniform_regular_graph_bulk_universality_parameters d hd N hN hlim E hE
  simpa only [KestenMcKay.regular_scale_eq_pi_density] using h

end GeneralizedBulk.Graph
