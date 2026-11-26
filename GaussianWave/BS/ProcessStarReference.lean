import GaussianWave.BS.StarDifferenceChart
import GaussianWave.BS.ProcessGaussianReference

/-! The canonical references in the physical star upper bound are exactly
the C0/E0 raw references after their explicit coordinate permutations. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GaussianWave.BS

theorem bulk_ratio_square_bound (m : ℕ) (energy : ℝ)
    (hbulk : |energy|<2*Real.sqrt (m+1)) :
    (energy/(m+2))^2 < 4*(((m+2 : ℕ) : ℝ)-1)/((m+2 : ℕ) : ℝ)^2 := by
  have hs := (sq_lt_sq₀ (abs_nonneg energy)
    (by positivity : (0 : ℝ) ≤ 2*Real.sqrt (m+1))).2 hbulk
  rw [sq_abs,mul_pow,Real.sq_sqrt (by positivity)] at hs
  norm_num only [Nat.cast_add,Nat.cast_ofNat]
  rw [div_pow]
  apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ)<(m+2 : ℝ)^2)).2
  nlinarith

theorem jointGaussianTreeProcessLaw_star_law (r m : ℕ) (energy : ℝ)
    (he : |energy|<(m+2 : ℝ)) (hc : |energy/(m+2)|<1) :
    processStarLaw (jointGaussianTreeProcessLaw r m energy)=
      Measure.map (coloredPhysicalStarMap (m+2) r (energy/(m+2)))
        (standardVector (Fin r × Fin (m+2))) := by
  have hG := jointGaussianTreeProcessLaw_finite_wave_kernel r m energy he (treeStarSite (m+2))
  have henergy : ((m+2 : ℕ) : ℝ)*(energy/(m+2))=energy := by
    norm_num only [Nat.cast_add,Nat.cast_ofNat]
    field_simp
  have hC : channelBlockCovariance (fun _ : Fin r =>
      fun i j : Fin (m+2+1) => sphericalCovariance (m+2) energy
        ((regularWordTree (m+2)).dist (treeStarSite (m+2) i) (treeStarSite (m+2) j)))=
      coloredPhysicalStarCovariance (m+2) r (energy/(m+2)) := by
    ext ⟨a,i⟩ ⟨b,j⟩
    simp only [channelBlockCovariance,coloredPhysicalStarCovariance,channelLiftMatrix]
    rw [treeStarSite_dist,← RegularEigenData.starWaveCovariance_eq_spherical (m+2) energy (by positivity)]
    rw [henergy]
    by_cases hab : a=b
    · subst b; rfl
    · simp only [if_neg hab,if_neg (Ne.symm hab)]
  rw [hC] at hG
  have hM := linearImageGaussian_characteristic (coloredPhysicalStarMatrix (m+2) r (energy/(m+2)))
  rw [coloredPhysicalStarMatrix_gram (m+2) r (by omega) _ hc] at hM
  apply measure_eq_of_linear_characteristic
  intro t
  exact (hG t).trans (hM t).symm

theorem processStar_difference_chart_law {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) (energy : ℝ)
    (hc : |energy/(m+2)|<1)
    (hE : ∀ a,∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) a none x=0) :
    Measure.map (fun y => starDifferenceEquiv (m+2) r (by omega) (energy/(m+2)) hc
      (coloredPhysicalStarEquiv (m+2) r (by omega) (energy/(m+2)) hc y))
      (processStarWhiteLaw μ (energy/(m+2)))=
      Measure.map (coordinateReindex (zeroVertexInnovationIndex r m)) (jointVertexInnovationProcessLaw μ 0) := by
  rw [zero_vertex_innovation_law,← processStarWhiteLaw_reconstruction μ energy hc hE,
    Measure.map_map (starDifferenceMap (m+2) r).continuous_of_finiteDimensional.measurable
      (coloredPhysicalStarMap (m+2) r (energy/(m+2))).continuous_of_finiteDimensional.measurable]
  rfl

theorem zero_vertex_reference_difference_chart_law (r m : ℕ) (energy : ℝ)
    (he : |energy|<(m+2 : ℝ)) (hc : |energy/(m+2)|<1) :
    Measure.map (coordinateReindex (zeroVertexInnovationIndex r m))
      (jointVertexInnovationReference (Fin r) m 0 energy he).law =
      Measure.map (coloredPhysicalStarChartMatrix (m+2) r (by omega) (energy/(m+2)) hc
        (starDifferenceEquiv (m+2) r (by omega) (energy/(m+2)) hc)).mulVec
        (standardVector (Fin r × Fin (m+2))) := by
  rw [jointVertexInnovationReference_process_law,zero_vertex_innovation_law,
    jointGaussianTreeProcessLaw_star_law r m energy he hc,
    Measure.map_map (starDifferenceMap (m+2) r).continuous_of_finiteDimensional.measurable
      (coloredPhysicalStarMap (m+2) r (energy/(m+2))).continuous_of_finiteDimensional.measurable]
  congr 1
  funext y
  exact (coloredPhysicalStarChartMatrix_mulVec (m+2) r (by omega) (energy/(m+2)) hc
    (starDifferenceEquiv (m+2) r (by omega) (energy/(m+2)) hc) y).symm

theorem zero_edge_reference_physical_law (r m : ℕ) (energy : ℝ)
    (he : |energy|<(m+2 : ℝ)) (hc : |energy/(m+2)|<1) :
    Measure.map (coordinateReindex (zeroEdgeInnovationIndex r m))
      (jointEdgeInnovationReference (Fin r) m 0 energy he).law =
      Measure.map (coloredPhysicalEdgeMatrix r (energy/(m+2))).mulVec (standardVector (Bool × Fin r)) := by
  rw [jointEdgeInnovationReference_process_law,zero_edge_innovation_law,processEdgeLaw,
    jointGaussianTreeProcessLaw_star_law r m energy he hc,
    coloredPhysicalGaussian_edge_law (m+2) r (by omega) (energy/(m+2)) hc 0]

end GaussianWave.BS
