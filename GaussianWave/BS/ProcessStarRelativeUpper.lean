import GaussianWave.BS.ProcessStarReference
import GaussianWave.BS.BallRelativeSSA
import GaussianWave.BS.GaussianBallReference

/-! The actual heat-flow star inequality, in the very same raw C0/E0
coordinates used by the all-radius entropy argument. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

theorem process_star_relative_upper_and_gaussian_equality {r m : ℕ} (hm : 0 < m)
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ChannelTreeInvariant μ) (hi : ∀ av,Integrable (fun x => x av^2) μ)
    (energy : ℝ) (hbulk : |energy|<2*Real.sqrt (m+1))
    (hE : ∀ a v,∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) a v x=0)
    (hroot : HasIdentitySecondMoments (rootChannelLaw μ))
    (C : PositiveEntropyDensity (volume : Measure ((Fin r × VertexBallInnovation (m+2) 0) → ℝ)))
    (E : PositiveEntropyDensity (volume : Measure ((Fin r × EdgeBallInnovation (m+2) 0) → ℝ)))
    (hC : C.law=jointVertexInnovationProcessLaw μ 0)
    (hE0 : E.law=jointEdgeInnovationProcessLaw μ 0) :
    let he := abs_energy_lt_degree_of_strict_bulk m energy hbulk
    let b := vertexBallRelativeEntropy (Fin r) m 0 energy he C-
      (m+2 : ℝ)/2*edgeBallRelativeEntropy (Fin r) m 0 energy he E
    b ≤ 0 ∧ (b=0 → C.law=(jointVertexInnovationReference (Fin r) m 0 energy he).law) := by
  let he := abs_energy_lt_degree_of_strict_bulk m energy hbulk
  have hb := bulk_ratio_square_bound m energy hbulk
  let hc := (bulk_rho_lower (m+2) (by omega) (energy/(m+2)) hb).1
  let chart := starDifferenceEquiv (m+2) r (by omega) (energy/(m+2)) hc
  have hf : Measure.map
      (fun y => chart (coloredPhysicalStarEquiv (m+2) r (by omega) (energy/(m+2)) hc y))
      (processStarWhiteLaw μ (energy/(m+2)))=
      Measure.map (coordinateReindex (zeroVertexInnovationIndex r m)) C.law := by
    rw [hC]
    exact processStar_difference_chart_law μ energy hc (fun a => hE a none)
  let f := (C.toFiniteEntropy.reindex (zeroVertexInnovationIndex r m)).cast hf
  have hg (i : Fin (m+2)) : processEdgeLaw μ i=
      Measure.map (coordinateReindex (zeroEdgeInnovationIndex r m)) E.law := by
    rw [hE0,zero_edge_innovation_law,processEdgeLaw_eq_zero μ hμ i]
  let g := fun i => (E.toFiniteEntropy.reindex (zeroEdgeInnovationIndex r m)).cast (hg i)
  have hRC := (jointVertexInnovationReference (Fin r) m 0 energy he).toFiniteEntropy.reindex_entropy
    (zeroVertexInnovationIndex r m)
  have hRE := (jointEdgeInnovationReference (Fin r) m 0 energy he).toFiniteEntropy.reindex_entropy
    (zeroEdgeInnovationIndex r m)
  have hRefC := ((jointVertexInnovationReference (Fin r) m 0 energy he).toFiniteEntropy.reindex
    (zeroVertexInnovationIndex r m)).entropy_eq_of_measure_eq
      (coloredPhysicalGaussianStarEntropyDensity (m+2) r (by omega) (energy/(m+2)) hc chart)
      (zero_vertex_reference_difference_chart_law r m energy he hc)
  have hRefE := ((jointEdgeInnovationReference (Fin r) m 0 energy he).toFiniteEntropy.reindex
    (zeroEdgeInnovationIndex r m)).entropy_eq_of_measure_eq
      (coloredPhysicalGaussianEdgeEntropyDensity r (energy/(m+2)) hc)
      (zero_edge_reference_physical_law r m energy he hc)
  rw [hRC,PositiveEntropyDensity.toFiniteEntropy_entropy] at hRefC
  rw [hRE,PositiveEntropyDensity.toFiniteEntropy_entropy] at hRefE
  have hfH : f.entropy=C.entropy := by
    simp only [f,FiniteEntropyDensity.cast_entropy,FiniteEntropyDensity.reindex_entropy,
      PositiveEntropyDensity.toFiniteEntropy_entropy]
  have hgH (i : Fin (m+2)) : (g i).entropy=E.entropy := by
    simp only [g,FiniteEntropyDensity.cast_entropy,FiniteEntropyDensity.reindex_entropy,
      PositiveEntropyDensity.toFiniteEntropy_entropy]
  have hbalance : f.entropy-(1/2 : ℝ)*∑ i,(g i).entropy-
      ((coloredPhysicalGaussianStarEntropyDensity (m+2) r (by omega) (energy/(m+2)) hc chart).entropy-
        (m+2 : ℝ)/2*(coloredPhysicalGaussianEdgeEntropyDensity r (energy/(m+2)) hc).entropy)=
      vertexBallRelativeEntropy (Fin r) m 0 energy he C-
        (m+2 : ℝ)/2*edgeBallRelativeEntropy (Fin r) m 0 energy he E := by
    rw [hfH,← hRefC,← hRefE]
    simp only [hgH,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    unfold vertexBallRelativeEntropy edgeBallRelativeEntropy
    push_cast
    ring
  constructor
  · have hu := process_star_entropy_upper hm μ hμ hi energy hb hE hroot chart f g
    rw [← hbalance]
    linarith
  · intro hz
    have heq : f.entropy-(1/2 : ℝ)*∑ i,(g i).entropy=
        (coloredPhysicalGaussianStarEntropyDensity (m+2) r (by omega) (energy/(m+2)) hc chart).entropy-
          (m+2 : ℝ)/2*(coloredPhysicalGaussianEdgeEntropyDensity r (energy/(m+2)) hc).entropy := by
      rw [hz] at hbalance
      linarith
    have hwhite := (process_star_entropy_equality_iff_white_gaussian hm μ hμ hi energy hb hE hroot chart f g).mp heq
    have hstar : processStarLaw μ=processStarLaw (jointGaussianTreeProcessLaw r m energy) := by
      rw [← processStarWhiteLaw_reconstruction μ energy hc (fun a => hE a none),hwhite,
        jointGaussianTreeProcessLaw_star_law r m energy he hc]
    apply MeasurableEquiv.map_measurableEquiv_injective
      (coordinateReindexMeasurableEquiv ℝ (zeroVertexInnovationIndex r m))
    change Measure.map (coordinateReindex (zeroVertexInnovationIndex r m)) C.law=
      Measure.map (coordinateReindex (zeroVertexInnovationIndex r m))
        (jointVertexInnovationReference (Fin r) m 0 energy he).law
    rw [hC,jointVertexInnovationReference_process_law,zero_vertex_innovation_law,
      zero_vertex_innovation_law,hstar]

end GaussianWave.BS
