import GaussianWave.BS.Lower.RecoloringColorTransport
import GaussianWave.BS.Lower.ProcessWindowLaws
import GaussianWave.BS.ChannelProcessTransform

/-! Exact finite-window color transport for actual channel linear maps.
In particular whitening preserves the all-radius finite-recoloring lower
bound by composing the continuous finite color kernels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS.Lower

/-- Channel linear maps commute with actual site-first finite windows. -/
theorem siteFirst_processWindow_channelProcessMap {r s d : ℕ} {V : Type*} [Fintype V]
    (P : Measure ((Fin r × RegularTreeVertex d) → ℝ)) (A : Matrix (Fin s) (Fin r) ℝ)
    (site : V → RegularTreeVertex d) :
    Measure.map (siteFirstCoordinates s) (Measure.map (processWindowProjection site)
      (Measure.map (channelProcessMap A) P)) =
    Measure.map (sitewiseColorMap A.mulVec) (Measure.map (siteFirstCoordinates r)
      (Measure.map (processWindowProjection site) P)) := by
  have hA := (continuous_channelProcessMap (d := d) A).measurable
  have hT := (continuous_sitewiseColorMap (V := V) A.mulVec
    (show Continuous A.mulVec from continuous_const.matrix_mulVec continuous_id)).measurable
  rw [Measure.map_map (measurable_siteFirstCoordinates s) (measurable_processWindowProjection site),
    Measure.map_map ((measurable_siteFirstCoordinates s).comp (measurable_processWindowProjection site)) hA,
    Measure.map_map hT (measurable_siteFirstCoordinates r),
    Measure.map_map (hT.comp (measurable_siteFirstCoordinates r)) (measurable_processWindowProjection site)]
  rfl

/-- The actual root-color marginal obeys the same literal pushforward. -/
theorem rootProcessWindow_channelProcessMap {m r s : ℕ}
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) (A : Matrix (Fin s) (Fin r) ℝ) :
    rootProcessWindow m (Measure.map (channelProcessMap A) P) =
      Measure.map A.mulVec (rootProcessWindow m P) := by
  rw [rootProcessWindow,rootProcessWindow,Measure.map_map
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)) (continuous_channelProcessMap A).measurable,
    Measure.map_map (measurable_finiteMatrixAction A)
      (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))]
  rfl

/-- No transformed entropy bound is assumed: every target finite kernel is
composed with the actual channel matrix on the source color space. -/
theorem finite_recoloring_entropy_lower_channelProcessMap {m r s : ℕ}
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) (k : ℕ) (w : ℝ)
    (h : HasFiniteRecoloringEntropyLower
      (Measure.map (siteFirstCoordinates r) (vertexProcessWindow m k P))
      (Measure.map (siteFirstCoordinates r) (edgeProcessWindow m k P)) (rootProcessWindow m P) w)
    (A : Matrix (Fin s) (Fin r) ℝ) :
    HasFiniteRecoloringEntropyLower
      (Measure.map (siteFirstCoordinates s) (vertexProcessWindow m k (Measure.map (channelProcessMap A) P)))
      (Measure.map (siteFirstCoordinates s) (edgeProcessWindow m k (Measure.map (channelProcessMap A) P)))
      (rootProcessWindow m (Measure.map (channelProcessMap A) P)) w := by
  have ht := HasFiniteRecoloringEntropyLower.map_continuous_color
    (Measure.map (siteFirstCoordinates r) (vertexProcessWindow m k P))
    (Measure.map (siteFirstCoordinates r) (edgeProcessWindow m k P)) (rootProcessWindow m P)
    w h A.mulVec (show Continuous A.mulVec from continuous_const.matrix_mulVec continuous_id)
  simpa only [vertexProcessWindow,edgeProcessWindow,siteFirst_processWindow_channelProcessMap,
    rootProcessWindow_channelProcessMap] using ht

end GaussianWave.BS.Lower
