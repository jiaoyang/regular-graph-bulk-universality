import GeneralizedBulk.Spectral.TreePotentialParametric
import GeneralizedBulk.Spectral.KestenMcKayPushforward

/-! The literal Kesten–McKay regularized potential equals the explicit tree
primitive at the small-root spectral parameter. -/
noncomputable section
namespace GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Spectral

theorem regularizedPotential_treeSpectralPoint (d : ℝ) (hd : 3 ≤ d) (g : ℂ) (hg : g ≠ 0)
    (hu : ‖treeLogParameter d g‖ < 1) (hz : 0 < (treeSpectralPoint d g).im) :
    regularizedPotential d (treeSpectralPoint d g).re (treeSpectralPoint d g).im =
      -Real.log ‖g‖ - (d - 2) / 2 * Real.log ‖1 - g ^ 2‖ := by
  unfold regularizedPotential
  rw [integral_rawDensity_change_variables d hd _
    (continuous_iff_continuousAt.mpr (fun x =>
      (regularizedLog_hasDerivAt _ _ hz x).continuousAt)).continuousOn]
  simp_rw [regularizedLog_eq_logNorm]
  exact integral_logNorm_treeSpectralPoint d hd g hg hu

end GeneralizedBulk.KestenMcKay
