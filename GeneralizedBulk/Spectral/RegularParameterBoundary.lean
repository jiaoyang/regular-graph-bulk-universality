import GeneralizedBulk.Spectral.TreeGreenStar

/-! The generalized switching parameters specialize exactly to the actual
regular-tree bulk centering and microscopic Kesten--McKay scale. -/
noncomputable section
namespace GeneralizedBulk.KestenMcKay

theorem regular_center_eq_diagonalBoundary_re (d E : ℝ) (hd : 3 ≤ d)
    (hbulk : E^2 < 4*(d-1)) :
    (Parameters.regular d E hd hbulk).center=(diagonalBoundary d E).re := by
  rw [Parameters.regular_center]
  rfl

theorem regular_scale_eq_diagonalBoundary_im (d E : ℝ) (hd : 3 ≤ d)
    (hbulk : E^2 < 4*(d-1)) :
    (Parameters.regular d E hd hbulk).scale=(diagonalBoundary d E).im := by
  rw [Parameters.regular_scale]
  rfl

theorem regular_scale_eq_pi_density (d E : ℝ) (hd : 3 ≤ d) (hbulk : E^2 < 4*(d-1)) :
    (Parameters.regular d E hd hbulk).scale=Real.pi*rawDensity d E :=
  (regular_scale_eq_diagonalBoundary_im d E hd hbulk).trans (diagonalBoundary_im_density d E hd hbulk)

theorem regular_boundary_calibration (d E : ℝ) (hd : 3 ≤ d) (hbulk : E^2 < 4*(d-1)) :
    ((Parameters.regular d E hd hbulk).center : ℂ)+
      ((Parameters.regular d E hd hbulk).scale : ℂ)*Complex.I=diagonalBoundary d E := by
  rw [regular_center_eq_diagonalBoundary_re,regular_scale_eq_diagonalBoundary_im]
  exact Complex.re_add_im _

end GeneralizedBulk.KestenMcKay
