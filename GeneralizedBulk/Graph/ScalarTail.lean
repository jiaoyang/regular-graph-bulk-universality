import GeneralizedBulk.Graph.GraphObstruction
import GeneralizedBulk.Graph.ConditionalChebyshev
import GeneralizedBulk.Analysis.ReversibleTail

/-!
# Finite scalar tails from the actual switching model

The only analytical model input is an explicit conditional second-moment
bound on the independent proposal graph fibers. Markov, reversal, the
large-scalar obstruction and the resulting tail recursion are proved here.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph
open Exterior External.RegularSpectralData Analysis

def graphHeight {N d : ℕ} (G : RegularGraph N d) (z : ℂ) : ℝ :=
  ‖graphNormalizedScalar G.val z‖

def graphDeviation {N d : ℕ} (s : EdgePairState N d) (z : ℂ) : Mat :=
  graphBoundary s.val.1 s.val.2 z - finiteMean N d z (graphNormalizedScalar s.val.1 z)

def graphEntryFailure {N d : ℕ} (delta : ℝ) (z : ℂ) : Set (EdgePairState N d) :=
  {s | ¬EntryBound (graphDeviation s z) (delta * graphHeight (edgePairGraph s) z)}

def graphGoodTail {N d : ℕ} (good : Set (RegularGraph N d)) (z : ℂ) (t : ℝ) : Set (EdgePairState N d) :=
  goodTail (edgePairGraph ⁻¹' good) (fun s => graphHeight (edgePairGraph s) z) t

/-- The physical graph fiber variance implies the precise relative failure
estimate needed on every scalar-height tail. -/
theorem graphEntryFailure_goodTail_le
    {N d : ℕ} [Nonempty (RegularGraph N d)] (hN : 0 < N) (hd : 0 < d)
    (good : Set (RegularGraph N d)) (z : ℂ) (delta C T0 : ℝ)
    (hdelta : 0 < delta) (hC : 0 ≤ C) (hT0 : 1 ≤ T0)
    (hvariance : ∀ G ∈ good, T0 ≤ graphHeight G z → ∀ i j,
      (∫ s : {s : EdgePairState N d // edgePairGraph s = G},
        ‖graphDeviation (s : EdgePairState N d) z i j‖ ^ 2
        ∂finiteUniform {s : EdgePairState N d // edgePairGraph s = G}) ≤ C * (1 + graphHeight G z))
    (t : ℝ) (ht : T0 ≤ t) :
    (edgePairLaw N d).real (graphGoodTail good z t ∩ graphEntryFailure delta z) ≤
      ((32 * C / delta ^ 2) / t) * (edgePairLaw N d).real (graphGoodTail good z t) := by
  letI := edgePairState_nonempty hN hd
  have hc (G : RegularGraph N d) :
      Fintype.card {s : EdgePairState N d // edgePairGraph s = G} = (N * d) ^ 2 := by
    rw [Fintype.card_subtype]
    exact edgePairGraph_fiber_card G
  have hp := finiteUniform_fiber_relative_entry_failure edgePairGraph ((N * d) ^ 2)
    (pow_pos (Nat.mul_pos hN hd) _) hc good (fun G => graphHeight G z)
    (fun s => graphDeviation s z) delta C T0 hdelta hC hT0 hvariance t ht
  convert hp using 1 <;> congr 1 <;> ext s <;>
    simp only [graphGoodTail, goodTail, graphEntryFailure, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_setOf_eq, and_assoc]

/-- Height shift on every finite proposal, including rejected self-loops. -/
theorem graphHeight_proposalSwitch_lower {N d : ℕ} (hN : 0 < N) (s : EdgePairState N d)
    (E eta cstar : ℝ) (heta : 0 < eta) (hcstar : 0 < cstar) (hheight : cstar ≤ (N : ℝ) * eta) :
    graphHeight (edgePairGraph s) (spectralParameter E eta) - 4 / cstar ≤
      graphHeight (edgePairGraph (proposalSwitch s)) (spectralParameter E eta) := by
  have hn := norm_sub_norm_le (graphNormalizedScalar s.val.1 (spectralParameter E eta))
    (graphNormalizedScalar (proposalSwitch s).val.1 (spectralParameter E eta))
  rw [norm_sub_rev] at hn
  have hb := graphNormalizedScalar_proposalSwitch_bound hN s E eta cstar heta hcstar hheight
  change ‖graphNormalizedScalar s.val.1 (spectralParameter E eta)‖ - 4 / cstar ≤
    ‖graphNormalizedScalar (proposalSwitch s).val.1 (spectralParameter E eta)‖
  linarith

/-- The concrete finite reversible tail recursion. The rejection contribution
is explicitly `(4+2d)/N`; the only remaining error is escape from the common
graph event. Conditional variance is never conditioned on acceptance. -/
theorem exists_graph_scalar_tail_recursion (d : ℕ) (hd : 0 < d)
    (E : ℝ) (hE : |E| < d) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (N : ℕ) [Nonempty (RegularGraph N d)], 0 < N →
      ∀ eta : ℝ, 0 < eta → eta ≤ 1 → cstar ≤ (N : ℝ) * eta →
      ∀ (good : Set (RegularGraph N d)) (C : ℝ), 0 ≤ C →
      (∀ G ∈ good, T0 ≤ graphHeight G (spectralParameter E eta) → ∀ i j,
        (∫ s : {s : EdgePairState N d // edgePairGraph s = G},
          ‖graphDeviation (s : EdgePairState N d) (spectralParameter E eta) i j‖ ^ 2
          ∂finiteUniform {s : EdgePairState N d // edgePairGraph s = G}) ≤
            C * (1 + graphHeight G (spectralParameter E eta))) →
      ∀ t : ℝ, 0 < t → T0 + 4 / cstar ≤ t → 2 * (4 / cstar) ≤ t →
        (edgePairLaw N d).real (graphGoodTail good (spectralParameter E eta) t) ≤
          ((96 * C / delta ^ 2) / t) *
            (edgePairLaw N d).real (graphGoodTail good (spectralParameter E eta) (t - 4 / cstar)) +
              (4 + 2 * (d : ℝ)) / N + (regularGraphLaw N d).real goodᶜ := by
  obtain ⟨delta, hdelta, hdeltaup, T0, hT0, hobstruct⟩ :=
    exists_graph_large_scalar_obstruction d hd E hE cstar hcstar
  refine ⟨delta, hdelta, hdeltaup, T0, hT0, ?_⟩
  intro N _ hN eta heta hetaup hheight good C hC hvariance t ht hthreshold hshift
  letI := edgePairState_nonempty hN hd
  letI := finiteUniform_isProbability (EdgePairState N d)
  let P := edgePairLaw N d
  let T (s : EdgePairState N d) := graphHeight (edgePairGraph s) (spectralParameter E eta)
  let F := graphEntryFailure (N := N) (d := d) delta (spectralParameter E eta)
  have hP : IsProbabilityMeasure P := by
    change IsProbabilityMeasure (finiteUniform (EdgePairState N d))
    infer_instance
  letI := hP
  have hMP : MeasurePreserving proposalSwitch P P :=
    ⟨measurable_of_finite _, edgePairLaw_switch_invariant N d⟩
  have hob : ∀ s ∈ {s : EdgePairState N d | Accepted s}, T0 ≤ T s → s ∈ F ∨ proposalSwitch s ∈ F := by
    intro s hs hlarge
    have hn := hobstruct N hN eta heta hetaup hheight s hs hlarge
    simpa only [F, graphEntryFailure, graphDeviation, graphHeight, edgePairGraph,
      Set.mem_setOf_eq] using (not_and_or.mp hn)
  have hfail : ∀ u : ℝ, T0 ≤ u →
      P.real (goodTail (edgePairGraph ⁻¹' good) T u ∩ F) ≤
        ((32 * C / delta ^ 2) / u) * P.real (goodTail (edgePairGraph ⁻¹' good) T u) := by
    intro u hu
    exact graphEntryFailure_goodTail_le hN hd good _ delta C T0 hdelta hC hT0 hvariance u hu
  have hp := goodTail_recursion P proposalSwitch hMP (edgePairGraph ⁻¹' good)
    {s | Accepted s} F (Set.toFinite _ |>.measurableSet) (Set.toFinite _ |>.measurableSet)
    T (measurable_of_finite _) (4 / cstar) T0 (32 * C / delta ^ 2) t (by positivity)
    (by positivity) ht hthreshold hshift
    (fun s => graphHeight_proposalSwitch_lower hN s E eta cstar heta hcstar hheight) hob hfail
  have hbad : P.real (edgePairGraph ⁻¹' good)ᶜ = (regularGraphLaw N d).real goodᶜ := by
    simp only [measureReal_def]
    rw [← edgePairLaw_graph_marginal hN hd,
      Measure.map_apply (measurable_of_finite _) (Set.toFinite _ |>.measurableSet)]
    rfl
  rw [hbad] at hp
  have hrej : P.real {s : EdgePairState N d | Accepted s}ᶜ ≤ (4 + 2 * (d : ℝ)) / N :=
    edgePairLaw_rejection_probability_bound hN hd
  have hlast := hp.trans (add_le_add_right (add_le_add_left hrej _) _)
  convert hlast using 1 <;> dsimp only [graphGoodTail, P, T] <;> congr 1 <;> ring

end GeneralizedBulk.Graph
