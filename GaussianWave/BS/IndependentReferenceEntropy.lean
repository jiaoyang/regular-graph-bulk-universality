import GaussianWave.BS.IndependentPositiveDensity
import GaussianWave.BS.GaussianBallReference
import GaussianWave.BS.IndependentChannelLaw
import GaussianWave.BS.EdgeBallDistances

/-! Actual independent-channel Gaussian reference entropy is additive,
including the empty-channel case. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GaussianWave.BS

theorem PositiveEntropyDensity.iid_entropy {Y : Type*} [MeasurableSpace Y]
    {my : Measure Y} [SigmaFinite my] (p : PositiveEntropyDensity my)
    (A : Type*) [Fintype A] : (p.iid A).entropy=(Fintype.card A : ℝ)*p.entropy := by
  have h := finiteStrongSubadditivity_independentReference_zero (A := A) my my p p
  simp only [PositiveEntropyDensity.prod_entropy,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  nlinarith

theorem gaussianFactorChartDensity_positive {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq I] [DecidableEq V] (M : Matrix V I ℝ) (O : Matrix I V ℝ)
    (hO : O.transpose*O*M=M) (hM : 0<(M.transpose*M).det) (x : I → ℝ) :
    0<(gaussianFactorChartDensity M O hO hM).density x :=
  (standardVectorEntropyDensity I).linearImage_positive (standardVectorEntropyDensity_positive I)
    (O*M) (factorChart_det_ne_zero M O hO hM) x

def vertexGaussianIntrinsicPositiveDensity (m k : ℕ) (energy : ℝ) (he : |energy|<(m+2 : ℝ)) :
    PositiveEntropyDensity (volume : Measure (VertexBallInnovation (m+2) k → ℝ)) :=
  (vertexGaussianIntrinsicDensity m k energy he).toPositive
    (gaussianFactorChartDensity_positive _ _ (vertexGaussianIsometricChart_projection m k energy he)
      (vertexOrthoFactorMatrix_gram_det_pos m k energy he))

def edgeGaussianIntrinsicPositiveDensity (m k : ℕ) (energy : ℝ) (he : |energy|<(m+2 : ℝ)) :
    PositiveEntropyDensity (volume : Measure (EdgeBallInnovation (m+2) k → ℝ)) :=
  (edgeGaussianIntrinsicDensity m k energy he).toPositive
    (gaussianFactorChartDensity_positive _ _ (edgeGaussianIsometricChart_projection m k energy he)
      (edgeOrthoFactorMatrix_gram_det_pos m k energy he))

def jointVertexGaussianIntrinsicDensity (r m k : ℕ) (energy : ℝ) (he : |energy|<(m+2 : ℝ)) :=
  (vertexGaussianIntrinsicPositiveDensity m k energy he).iid (Fin r)

def jointEdgeGaussianIntrinsicDensity (r m k : ℕ) (energy : ℝ) (he : |energy|<(m+2 : ℝ)) :=
  (edgeGaussianIntrinsicPositiveDensity m k energy he).iid (Fin r)

theorem vertexGaussianIntrinsicPositiveDensity_law (m k : ℕ) (energy : ℝ) (he : |energy| < (m+2 : ℝ)) :
    (vertexGaussianIntrinsicPositiveDensity m k energy he).law =
      Measure.map (vertexGaussianIsometricChart m k energy he).mulVec (vertexGaussianBallLaw m k energy) :=
  FiniteEntropyDensity.toPositive_law _ _

theorem edgeGaussianIntrinsicPositiveDensity_law (m k : ℕ) (energy : ℝ) (he : |energy| < (m+2 : ℝ)) :
    (edgeGaussianIntrinsicPositiveDensity m k energy he).law =
      Measure.map (edgeGaussianIsometricChart m k energy he).mulVec (edgeGaussianBallLaw m k energy) :=
  FiniteEntropyDensity.toPositive_law _ _

theorem jointVertexGaussianIntrinsicDensity_law (r m k : ℕ) (energy : ℝ) (he : |energy| < (m+2 : ℝ)) :
    (jointVertexGaussianIntrinsicDensity r m k energy he).law = Measure.map
      (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun a : Fin r =>
        (vertexGaussianIsometricChart m k energy he).mulVec
          (fun v => z (a,vertexBallEmbedding (m+2) k v)))
      (jointGaussianTreeProcessLaw r m energy) := by
  let B := fun z : RegularTreeVertex (m+2) → ℝ => fun v => z (vertexBallEmbedding (m+2) k v)
  let O := vertexGaussianIsometricChart m k energy he
  have hB : Measurable B := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hO : Measurable O.mulVec := measurable_finiteMatrixAction O
  have hscalar : Measure.map (O.mulVec ∘ B) (gaussianTreeProcessLaw m energy : Measure _) =
      Measure.map O.mulVec (vertexGaussianBallLaw m k energy) := by
    rw [← Measure.map_map hO hB,gaussianTreeProcessLaw_ball]
  rw [jointVertexGaussianIntrinsicDensity,PositiveEntropyDensity.iid_law,
    vertexGaussianIntrinsicPositiveDensity_law]
  change Measure.pi (fun _ : Fin r => Measure.map O.mulVec (vertexGaussianBallLaw m k energy)) =
    Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun a => (O.mulVec ∘ B) (fun v => z (a,v)))
      (independentChannelLaw (fun _ : Fin r => (gaussianTreeProcessLaw m energy : Measure _)))
  rw [independentChannelLaw_block_map _ _ (hO.comp hB)]
  simp only [hscalar]

theorem jointEdgeGaussianIntrinsicDensity_law (r m k : ℕ) (energy : ℝ) (he : |energy| < (m+2 : ℝ)) :
    (jointEdgeGaussianIntrinsicDensity r m k energy he).law = Measure.map
      (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun a : Fin r =>
        (edgeGaussianIsometricChart m k energy he).mulVec (fun v => z (a,edgeBallEmbedding m k v)))
      (jointGaussianTreeProcessLaw r m energy) := by
  let B := fun z : RegularTreeVertex (m+2) → ℝ => fun v => z (edgeBallEmbedding m k v)
  let O := edgeGaussianIsometricChart m k energy he
  have hB : Measurable B := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hO : Measurable O.mulVec := measurable_finiteMatrixAction O
  have hscalar : Measure.map (O.mulVec ∘ B) (gaussianTreeProcessLaw m energy : Measure _) =
      Measure.map O.mulVec (edgeGaussianBallLaw m k energy) := by
    rw [← Measure.map_map hO hB,gaussianTreeProcessLaw_edge m k energy he]
  rw [jointEdgeGaussianIntrinsicDensity,PositiveEntropyDensity.iid_law,
    edgeGaussianIntrinsicPositiveDensity_law]
  change Measure.pi (fun _ : Fin r => Measure.map O.mulVec (edgeGaussianBallLaw m k energy)) =
    Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun a => (O.mulVec ∘ B) (fun v => z (a,v)))
      (independentChannelLaw (fun _ : Fin r => (gaussianTreeProcessLaw m energy : Measure _)))
  rw [independentChannelLaw_block_map _ _ (hO.comp hB)]
  simp only [hscalar]

theorem joint_gaussian_ball_reference_entropy_tendsto_zero
    (r m : ℕ) (hm : 0 < m) (energy : ℝ) (hbulk : |energy| < 2*Real.sqrt (m+1)) :
    Tendsto (fun k =>
      (jointVertexGaussianIntrinsicDensity r m k energy (abs_energy_lt_degree_of_strict_bulk m energy hbulk)).entropy -
        (m+2 : ℝ)/2 *
          (jointEdgeGaussianIntrinsicDensity r m k energy (abs_energy_lt_degree_of_strict_bulk m energy hbulk)).entropy)
      atTop (𝓝 0) := by
  have h := (gaussian_ball_reference_entropy_tendsto_zero_energy m hm energy hbulk).const_mul (r : ℝ)
  simp only [mul_zero] at h
  convert h using 1
  ext k
  simp only [jointVertexGaussianIntrinsicDensity,jointEdgeGaussianIntrinsicDensity,
    PositiveEntropyDensity.iid_entropy,Fintype.card_fin,
    vertexGaussianIntrinsicEntropy,edgeGaussianIntrinsicEntropy]
  change (r : ℝ)*(vertexGaussianIntrinsicDensity m k energy _).entropy -
    (m+2 : ℝ)/2*((r : ℝ)*(edgeGaussianIntrinsicDensity m k energy _).entropy) = _
  ring

end GaussianWave.BS
