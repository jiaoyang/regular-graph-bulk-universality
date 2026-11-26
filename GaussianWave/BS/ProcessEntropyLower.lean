import GaussianWave.BS.ProcessBallMarginals
import GaussianWave.BS.JointIntrinsicRows
import GaussianWave.BS.Lower.ProcessWindowLaws

/-! The actual all-channel finite recoloring theorem implies the actual
intrinsic C/E entropy lower bound for an eigenprocess. All chart ranks,+support and dimensions are derived from the concrete ball geometry. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def vertexSiteFirstProcessLaw {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) :=
  Measure.map (Lower.siteFirstCoordinates r) (jointVertexProcessBallLaw μ k)

def edgeSiteFirstProcessLaw {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) :=
  Measure.map (Lower.siteFirstCoordinates r) (jointEdgeProcessBallLaw μ k)

instance vertexSiteFirstProcessLaw_probability {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (vertexSiteFirstProcessLaw μ k) :=
  isProbabilityMeasure_map (Lower.measurable_siteFirstCoordinates r).aemeasurable

instance edgeSiteFirstProcessLaw_probability {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (edgeSiteFirstProcessLaw μ k) :=
  isProbabilityMeasure_map (Lower.measurable_siteFirstCoordinates r).aemeasurable

theorem integrable_vertexSiteFirstProcessLaw_squareRadius {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (k : ℕ) :
    Integrable squareRadius (vertexSiteFirstProcessLaw μ k) := by
  rw [vertexSiteFirstProcessLaw, jointVertexProcessBallLaw,
    Measure.map_map (Lower.measurable_siteFirstCoordinates r) (measurable_jointTreeWindow _)]
  exact integrable_finiteWindow_sum_sq μ hi (fun vc : VertexBallVertex (m + 2) k × Fin r =>
    (vc.2, vertexBallEmbedding (m + 2) k vc.1))

theorem integrable_edgeSiteFirstProcessLaw_squareRadius {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (k : ℕ) :
    Integrable squareRadius (edgeSiteFirstProcessLaw μ k) := by
  rw [edgeSiteFirstProcessLaw, jointEdgeProcessBallLaw,
    Measure.map_map (Lower.measurable_siteFirstCoordinates r) (measurable_jointTreeWindow _)]
  exact integrable_finiteWindow_sum_sq μ hi (fun vc : EdgeBallVertex (m + 2) k × Fin r =>
    (vc.2, edgeBallEmbedding m k vc.1))

theorem vertexSiteFirst_intrinsic_support {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0) :
    ∀ᵐ y ∂vertexSiteFirstProcessLaw μ k,
      (siteFirstIntrinsicRows r (vertexGaussianIsometricChart m k energy he)).transpose.mulVec
        ((siteFirstIntrinsicRows r (vertexGaussianIsometricChart m k energy he)).mulVec y) = y := by
  apply (ae_map_iff (Lower.measurable_siteFirstCoordinates r).aemeasurable
    (measurableSet_eq_fun (measurable_finiteMatrixAction _ |>.comp (measurable_finiteMatrixAction _)) measurable_id)).2
  filter_upwards [jointVertexProcessBallLaw_ae_eigenrelation μ k energy
    (ne_of_lt ((le_abs_self energy).trans_lt he)) hE] with x hx
  apply siteFirstIntrinsicRows_support
  intro c
  exact vertexGaussianIsometricChart_on_space m k energy he
    ⟨fun v => x (c, v), (mem_vertexBallEigenSpace_iff m k energy
      (ne_of_lt ((le_abs_self energy).trans_lt he)) _).mpr (hx c)⟩

theorem edgeSiteFirst_intrinsic_support {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0) :
    ∀ᵐ y ∂edgeSiteFirstProcessLaw μ k,
      (siteFirstIntrinsicRows r (edgeGaussianIsometricChart m k energy he)).transpose.mulVec
        ((siteFirstIntrinsicRows r (edgeGaussianIsometricChart m k energy he)).mulVec y) = y := by
  apply (ae_map_iff (Lower.measurable_siteFirstCoordinates r).aemeasurable
    (measurableSet_eq_fun (measurable_finiteMatrixAction _ |>.comp (measurable_finiteMatrixAction _)) measurable_id)).2
  filter_upwards [jointEdgeProcessBallLaw_ae_eigenrelation μ k energy hE] with x hx
  apply siteFirstIntrinsicRows_support
  intro c
  exact edgeGaussianIsometricChart_on_space m k energy he
    ⟨fun v => x (c, v), (mem_edgeBallEigenSpace_iff m k energy _).mpr (hx c)⟩

theorem vertexProcessIntrinsicDensity_law {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0)
    (f : PositiveEntropyDensity (volume : Measure ((Fin r × VertexBallInnovation (m + 2) k) → ℝ)))
    (hf : f.law = jointVertexInnovationProcessLaw μ k) :
    (f.linearEquiv (coloredVertexInnovationToIntrinsic (Fin r) m k energy he)).law =
      Measure.map (siteFirstIntrinsicRows r (vertexGaussianIsometricChart m k energy he)).mulVec
        (vertexSiteFirstProcessLaw μ k) := by
  have hχ : Measurable (coloredVertexInnovationToIntrinsic (Fin r) m k energy he : _ → _) :=
    (coloredVertexInnovationToIntrinsic (Fin r) m k energy he).toLinearMap.continuous_of_finiteDimensional.measurable
  rw [PositiveEntropyDensity.linearEquiv_law, hf, jointVertexInnovationProcessLaw,
    vertexSiteFirstProcessLaw, Measure.map_map hχ
      (jointVertexBallExtract (Fin r) m k).continuous_of_finiteDimensional.measurable,
    Measure.map_map (measurable_finiteMatrixAction _) (Lower.measurable_siteFirstCoordinates r)]
  apply Measure.map_congr
  filter_upwards [jointVertexProcessBallLaw_ae_eigenrelation μ k energy
    (ne_of_lt ((le_abs_self energy).trans_lt he)) hE] with x hx
  funext ⟨c, i⟩
  change vertexInnovationToIntrinsic m k energy he (vertexBallExtract m k (fun v => x (c, v))) i = _
  rw [vertexInnovationToIntrinsic_apply, vertexBallBuild_extract m k energy
    (ne_of_lt ((le_abs_self energy).trans_lt he)) _ (hx c)]
  exact (congrFun (siteFirstIntrinsicRows_siteFirst r (vertexGaussianIsometricChart m k energy he) x) (c, i)).symm

theorem edgeProcessIntrinsicDensity_law {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0)
    (f : PositiveEntropyDensity (volume : Measure ((Fin r × EdgeBallInnovation (m + 2) k) → ℝ)))
    (hf : f.law = jointEdgeInnovationProcessLaw μ k) :
    (f.linearEquiv (coloredEdgeInnovationToIntrinsic (Fin r) m k energy he)).law =
      Measure.map (siteFirstIntrinsicRows r (edgeGaussianIsometricChart m k energy he)).mulVec
        (edgeSiteFirstProcessLaw μ k) := by
  have hχ : Measurable (coloredEdgeInnovationToIntrinsic (Fin r) m k energy he : _ → _) :=
    (coloredEdgeInnovationToIntrinsic (Fin r) m k energy he).toLinearMap.continuous_of_finiteDimensional.measurable
  rw [PositiveEntropyDensity.linearEquiv_law, hf, jointEdgeInnovationProcessLaw,
    edgeSiteFirstProcessLaw, Measure.map_map hχ
      (jointEdgeBallExtract (Fin r) m k).continuous_of_finiteDimensional.measurable,
    Measure.map_map (measurable_finiteMatrixAction _) (Lower.measurable_siteFirstCoordinates r)]
  apply Measure.map_congr
  filter_upwards [jointEdgeProcessBallLaw_ae_eigenrelation μ k energy hE] with x hx
  funext ⟨c, i⟩
  change edgeInnovationToIntrinsic m k energy he (edgeBallExtract m k (fun v => x (c, v))) i = _
  rw [edgeInnovationToIntrinsic_apply, edgeBallBuild_extract m k energy _ (hx c)]
  exact (congrFun (siteFirstIntrinsicRows_siteFirst r (edgeGaussianIsometricChart m k energy he) x) (c, i)).symm

theorem process_intrinsic_entropy_lower {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av, Integrable (fun x => x av ^ 2) μ) (k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0)
    (hfinite : Lower.HasFiniteRecoloringEntropyLower (vertexSiteFirstProcessLaw μ k)
      (edgeSiteFirstProcessLaw μ k) (Lower.rootProcessWindow m μ) ((m + 2 : ℝ) / 2))
    (C : PositiveEntropyDensity (volume : Measure ((Fin r × VertexBallInnovation (m + 2) k) → ℝ)))
    (E : PositiveEntropyDensity (volume : Measure ((Fin r × EdgeBallInnovation (m + 2) k) → ℝ)))
    (hC : C.law = jointVertexInnovationProcessLaw μ k) (hEE : E.law = jointEdgeInnovationProcessLaw μ k) :
    0 ≤ (C.linearEquiv (coloredVertexInnovationToIntrinsic (Fin r) m k energy he)).entropy -
      (m + 2 : ℝ) / 2 * (E.linearEquiv (coloredEdgeInnovationToIntrinsic (Fin r) m k energy he)).entropy := by
  let fC := ((C.linearEquiv (coloredVertexInnovationToIntrinsic (Fin r) m k energy he)).toFiniteEntropy).cast
    (vertexProcessIntrinsicDensity_law μ k energy he hE C hC).symm
  let fE := ((E.linearEquiv (coloredEdgeInnovationToIntrinsic (Fin r) m k energy he)).toFiniteEntropy).cast
    (edgeProcessIntrinsicDensity_law μ k energy he hE E hEE).symm
  have hdim : (Fintype.card (Fin r × VertexBallInnovation (m + 2) k) : ℝ) -
      (m + 2 : ℝ) / 2 * Fintype.card (Fin r × EdgeBallInnovation (m + 2) k) = 0 := by
    have hn := ball_innovation_card_balance (m + 2) k (by omega)
    have hr : (2 : ℝ) * Fintype.card (VertexBallInnovation (m + 2) k) =
        (m + 2 : ℝ) * Fintype.card (EdgeBallInnovation (m + 2) k) := by exact_mod_cast hn
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    nlinarith
  exact Lower.intrinsic_entropy_nonneg_of_finite_recoloring
    (vertexSiteFirstProcessLaw μ k) (edgeSiteFirstProcessLaw μ k) (Lower.rootProcessWindow m μ)
    (integrable_vertexSiteFirstProcessLaw_squareRadius μ hi k)
    (integrable_edgeSiteFirstProcessLaw_squareRadius μ hi k) ((m + 2 : ℝ) / 2)
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using ball_ambient_real_card_balance (m + 2) k) hfinite
    (siteFirstIntrinsicRows r (vertexGaussianIsometricChart m k energy he))
    (siteFirstIntrinsicRows_orthonormal _ _ (vertexGaussianIsometricChart_rows m k energy he))
    (siteFirstIntrinsicRows r (edgeGaussianIsometricChart m k energy he))
    (siteFirstIntrinsicRows_orthonormal _ _ (edgeGaussianIsometricChart_rows m k energy he))
    (vertexSiteFirst_intrinsic_support μ k energy he hE) (edgeSiteFirst_intrinsic_support μ k energy he hE)
    hdim fC fE

end GaussianWave.BS
