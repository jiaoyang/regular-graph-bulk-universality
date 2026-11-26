import GaussianWave.BS.IndependentChannelLaw

/-! The Gaussian-wave block-factor approximation for any finite number
of independent channels, using actual product process laws throughout. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS

def jointRadialGaussianBlockLaw (r d : ℕ) (x : ℝ) (k : ℕ) :
    Measure ((Fin r × RegularTreeVertex d) → ℝ) :=
  independentChannelLaw (fun _ : Fin r => radialGaussianBlockLaw d x k)

instance jointRadialGaussianBlockLaw_probability (r d : ℕ) (x : ℝ) (k : ℕ) :
    IsProbabilityMeasure (jointRadialGaussianBlockLaw r d x k) := independentChannelLaw_probability _

theorem jointRadialGaussianBlockLaw_finite_covariance
    (r d : ℕ) (x : ℝ) (k : ℕ) {J : Type*} [Fintype J]
    (site : J → RegularTreeVertex d) :
    HasGaussianCovariance (Measure.map
      (fun z : (Fin r × RegularTreeVertex d) → ℝ => fun aj : Fin r × J => z (aj.1,site aj.2))
      (jointRadialGaussianBlockLaw r d x k))
      (channelBlockCovariance (fun _ : Fin r => radialBlockCovarianceMatrix d x k site)) := by
  rw [jointRadialGaussianBlockLaw,independentChannelLaw_window]
  letI : IsProbabilityMeasure (Measure.map (fun z : RegularTreeVertex d → ℝ => fun j => z (site j))
      (radialGaussianBlockLaw d x k)) :=
    isProbabilityMeasure_map (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).aemeasurable
  exact independentChannelLaw_gaussian _ _ (fun _ => radialGaussianBlockLaw_finite_covariance d x k site)

/-- Actual finite-window convergence of the joint iid block rules to the
actual joint Gaussian-tree reference. No Gaussian limit is supplied. -/
theorem jointRadialGaussianBlockLaw_weakConverges_to_tree_reference
    (r m : ℕ) (hm : 0 < m) (x : ℝ) (hx : |x|<1)
    {J : Type*} [Fintype J] [DecidableEq J] (site : J → RegularTreeVertex (m+2)) :
    WeakLawConverges
      (fun k => Measure.map
        (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun aj : Fin r × J => z (aj.1,site aj.2))
        (jointRadialGaussianBlockLaw r (m+2) x k))
      (Measure.map
        (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun aj : Fin r × J => z (aj.1,site aj.2))
        (jointGaussianTreeProcessLaw r m (radialEnergy m x))) := by
  let W := fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
    fun aj : Fin r × J => z (aj.1,site aj.2)
  have hW : Measurable W := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  let C := fun k => channelBlockCovariance (fun _ : Fin r => radialBlockCovarianceMatrix (m+2) x k site)
  let D := channelBlockCovariance (fun _ : Fin r => radialFiniteWaveCovariance (m+2) (radialEnergy m x) site)
  have hC (k) : (C k).PosSemidef := channelBlockCovariance_posSemidef _
    (fun _ => radialBlockCovarianceMatrix_posSemidef (m+2) x k site)
  have he : 2*Real.sqrt (((m+2 : ℕ) : ℝ)-1)*x = radialEnergy m x := by
    unfold radialEnergy
    norm_num only [Nat.cast_add,Nat.cast_ofNat]
    congr 2
    ring
  have hscalar : (radialFiniteWaveCovariance (m+2) (radialEnergy m x) site).PosSemidef := by
    simpa only [he] using radialFiniteWaveCovariance_posSemidef (m+2) (by omega) x hx site
  have hD : D.PosSemidef := channelBlockCovariance_posSemidef _ (fun _ => hscalar)
  letI (k : ℕ) : IsProbabilityMeasure (Measure.map W (jointRadialGaussianBlockLaw r (m+2) x k)) :=
    isProbabilityMeasure_map hW.aemeasurable
  letI : IsProbabilityMeasure (Measure.map W (jointGaussianTreeProcessLaw r m (radialEnergy m x))) :=
    isProbabilityMeasure_map hW.aemeasurable
  have hsource (k) : Measure.map W (jointRadialGaussianBlockLaw r (m+2) x k) =
      gaussianCovarianceLaw (C k) (hC k) := by
    apply eq_gaussianCovarianceLaw
    exact jointRadialGaussianBlockLaw_finite_covariance r (m+2) x k site
  have htarget : Measure.map W (jointGaussianTreeProcessLaw r m (radialEnergy m x)) =
      gaussianCovarianceLaw D hD := by
    apply eq_gaussianCovarianceLaw
    exact jointGaussianTreeProcessLaw_finite_wave_kernel r m _ (abs_radialEnergy_lt_degree m hx) site
  change WeakLawConverges (fun k => Measure.map W _) (Measure.map W _)
  simp_rw [hsource,htarget]
  apply gaussianCovarianceLaw_weakConverges C hC D hD
  intro a b
  by_cases hab : a.1=b.1
  · simp only [C,D,channelBlockCovariance,if_pos hab,radialBlockCovarianceMatrix,radialFiniteWaveCovariance]
    have h := radialBlockCovariance_tendsto_spherical (m+2) (by omega) x hx (site a.2) (site b.2)
    simpa only [he] using h
  · simp only [C,D,channelBlockCovariance,if_neg hab]
    exact tendsto_const_nhds

end GaussianWave.BS
