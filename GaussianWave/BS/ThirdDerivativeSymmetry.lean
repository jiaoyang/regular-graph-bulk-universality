import GaussianWave.BS.HeatHigherRegularity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Symmetry of the actual third Fréchet derivative of a C3 log density. -/
noncomputable section
open MeasureTheory
open scoped Topology ContDiff

namespace GaussianWave.BS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def thirdDifferential (L : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (fderiv ℝ L)) x

/-- Schwarz symmetry applied to the C2 first derivative. -/
theorem thirdDifferential_swap_first (L : E → ℝ) (hL : ContDiff ℝ 3 L)
    (x u v w : E) :
    thirdDifferential L x u v w = thirdDifferential L x v u w := by
  have hD : ContDiff ℝ 2 (fderiv ℝ L) := hL.fderiv_right (by norm_num)
  have hs := (hD.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num) u v
  exact congrArg (fun A : E →L[ℝ] ℝ => A w) hs

/-- The last two slots commute by differentiating the pointwise symmetric
Hessian. This proves the symmetry for finite C3 regularity, without an
analyticity assumption. -/
theorem thirdDifferential_swap_last (L : E → ℝ) (hL : ContDiff ℝ 3 L)
    (x u v w : E) :
    thirdDifferential L x u v w = thirdDifferential L x u w v := by
  have hD : ContDiff ℝ 2 (fderiv ℝ L) := hL.fderiv_right (by norm_num)
  have hDD : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ L)) := hD.fderiv_right (by norm_num)
  have heq : (fun y => fderiv ℝ (fderiv ℝ L) y v w) =
      (fun y => fderiv ℝ (fderiv ℝ L) y w v) := by
    funext y
    exact hL.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; decide) v w
  have hd := ((hDD.differentiable (by norm_num) x).hasFDerivAt).hasLineDerivAt u
  have hl := (hd.clm_apply (hasDerivAt_const 0 v)).clm_apply (hasDerivAt_const 0 w)
  have hr := (hd.clm_apply (hasDerivAt_const 0 w)).clm_apply (hasDerivAt_const 0 v)
  simp only [zero_smul, add_zero, ContinuousLinearMap.zero_apply, zero_add] at hl hr
  have heqline : (fun s : ℝ => fderiv ℝ (fderiv ℝ L) (x + s • u) v w) =
      (fun s : ℝ => fderiv ℝ (fderiv ℝ L) (x + s • u) w v) := by
    exact congrArg (fun F : E → ℝ => fun s : ℝ => F (x + s • u)) heq
  rw [heqline] at hl
  simpa only [thirdDifferential, map_zero, add_zero] using hl.unique hr

theorem log_heatDensity_thirdDifferential_symmetric
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (x u v w : I → ℝ) :
    thirdDifferential (fun y => Real.log (heatDensity μ t y)) x u v w =
        thirdDifferential (fun y => Real.log (heatDensity μ t y)) x v u w ∧
      thirdDifferential (fun y => Real.log (heatDensity μ t y)) x u v w =
        thirdDifferential (fun y => Real.log (heatDensity μ t y)) x u w v := by
  exact ⟨thirdDifferential_swap_first _ (contDiff_three_log_heatDensity μ ht) x u v w,
    thirdDifferential_swap_last _ (contDiff_three_log_heatDensity μ ht) x u v w⟩

end GaussianWave.BS
