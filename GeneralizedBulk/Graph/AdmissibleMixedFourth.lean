import GeneralizedBulk.Graph.AdmissibleSizeLimits
import GeneralizedBulk.Graph.UniformMixedFourth

/-! The common mixed-fourth good event with size tending directly to infinity
through admissible positive graph sizes. The exponents and constants are the
same fixed degree-dependent quantities as in the sequence endpoint. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace GeneralizedBulk.Graph
open GeneralizedBulk.Entropy.ChannelRates

/-- The article's one-event polynomial mixed-fourth probability bound along
the literal admissible-size filter, with positive degree-only constants.
The finite-size theorem `mixedFourthGood_moment` gives the moment conclusion
on this very event simultaneously for every allowed eigenfamily and slot. -/
theorem uniform_graph_mixed_fourth_along_admissible_sizes
    (d : ℕ) (hd : 3≤d)
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E∈K,E^2<4*((d : ℝ)-1)) :
    let χ := mixedFourthUniformExponent d hd
    let C := 4*mixedFourthFailureConstant d
    0<χ ∧ 0<C ∧
      (∀ M : ℕ,MeasurableSet (mixedFourthGood d hd M K)) ∧
      (∀ᶠ M : ℕ in admissibleSizeFilter d,1-C*(M : ℝ)^(-(1/32 : ℝ)) ≤
        (regularGraphLaw M d).real (mixedFourthGood d hd M K)) := by
  intro χ C
  have hC : 0<C := by dsimp [C]; linarith [mixedFourthFailureConstant_ge_ten d hd]
  refine ⟨mixedFourthUniformExponent_pos d hd,hC,
    (fun M => measurableSet_mixedFourthGood d hd M K),?_⟩
  apply eventually_admissibleSizeFilter_of_sequences d
  intro N hN hlim hgraphs
  letI : ∀ n, Nonempty (RegularGraph (N n) d) := hgraphs
  exact (uniform_graph_mixed_fourth d hd N hN hlim K hK hbulk).2.2.2.1

end GeneralizedBulk.Graph
