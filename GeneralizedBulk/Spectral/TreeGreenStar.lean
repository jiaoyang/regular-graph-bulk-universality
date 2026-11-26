import GeneralizedBulk.Spectral.TreeGreenBoundary
import GeneralizedBulk.Spectral.KestenMcKayDensity
import GeneralizedBulk.Graph.StarCovariance

/-! Exact tree Green boundary covariance on a rooted regular star. -/
noncomputable section
namespace GeneralizedBulk.KestenMcKay

 theorem diagonalBoundary_im_pos (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    0 < (diagonalBoundary d E).im := by
  exact div_pos (mul_pos (by linarith) (Real.sqrt_pos.mpr (by dsimp [discriminant]; linarith)))
    (mul_pos (by norm_num) (bulk_denominator_pos d E hd hbulk))

 theorem diagonalBoundary_im_density (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    (diagonalBoundary d E).im = Real.pi * rawDensity d E := by
  dsimp [diagonalBoundary, rawDensity, discriminant]
  field_simp [Real.pi_ne_zero, (bulk_denominator_pos d E hd hbulk).ne']
  <;> ring

 private theorem real_mul_im (r : ℝ) (z : ℂ) : ((r : ℂ) * z).im = r * z.im := by
  simp [Complex.mul_im]

 theorem neighborBoundary_im (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    (-(diagonalBoundary d E * cavityBoundary d E)).im =
      (diagonalBoundary d E).im * (E / d) := by
  have hh := congrArg Complex.im (diagonalBoundary_root_recursion d E hd hbulk)
  rw [mul_assoc] at hh
  simp only [Complex.add_im, real_mul_im, Complex.neg_im, Complex.one_im] at hh
  rw [Complex.neg_im, ← mul_div_assoc]
  have hd0 : d ≠ 0 := by linarith
  apply (eq_div_iff hd0).mpr
  nlinarith [hh]

 theorem secondNeighborBoundary_im (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    (diagonalBoundary d E * cavityBoundary d E ^ 2).im =
      (diagonalBoundary d E).im * ((E ^ 2 - d) / (d * (d - 1))) := by
  have hpoly : ((d - 1 : ℝ) : ℂ) * (diagonalBoundary d E * cavityBoundary d E ^ 2) +
      (E : ℂ) * (diagonalBoundary d E * cavityBoundary d E) + diagonalBoundary d E = 0 := by
    calc
      _ = diagonalBoundary d E * ((d - 1 : ℂ) * cavityBoundary d E ^ 2 + (E : ℂ) * cavityBoundary d E + 1) := by push_cast; ring
      _ = 0 := by rw [cavityBoundary_quadratic d E hd hbulk, mul_zero]
  have hi := congrArg Complex.im hpoly
  simp only [Complex.add_im, real_mul_im, Complex.zero_im] at hi
  have hn := neighborBoundary_im d E hd hbulk
  rw [Complex.neg_im, ← mul_div_assoc] at hn
  have hd0 : d ≠ 0 := by linarith
  have hq : d - 1 ≠ 0 := by linarith
  rw [← mul_div_assoc]
  apply (eq_div_iff (mul_ne_zero hd0 hq)).mpr
  field_simp [hd0] at hn
  simp only [Complex.mul_im] at hi ⊢
  linear_combination d * hi + E * hn

 def boundaryStar (d : ℕ) (E : ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  let m := diagonalBoundary d E
  let g := cavityBoundary d E
  fun j l => Fin.cases (Fin.cases m (fun _ => -(m * g)) l)
    (fun a => Fin.cases (-(m * g)) (fun b => if a = b then m else m * g ^ 2) l) j

 theorem boundaryStar_im (d : ℕ) (hd : 3 ≤ (d : ℝ)) (E : ℝ)
    (hbulk : E ^ 2 < 4 * ((d : ℝ) - 1)) (j l : Fin (d + 1)) :
    (boundaryStar d E j l).im = (diagonalBoundary d E).im *
      External.RegularSpectralData.starWaveCovariance d E j l := by
  refine Fin.cases ?_ (fun a => ?_) j
  · refine Fin.cases ?_ (fun b => ?_) l
    · simp [boundaryStar, External.RegularSpectralData.starWaveCovariance]
    · simpa [boundaryStar, External.RegularSpectralData.starWaveCovariance] using neighborBoundary_im d E hd hbulk
  · refine Fin.cases ?_ (fun b => ?_) l
    · simpa [boundaryStar, External.RegularSpectralData.starWaveCovariance] using neighborBoundary_im d E hd hbulk
    · by_cases hab : a = b
      · simp [boundaryStar, External.RegularSpectralData.starWaveCovariance, hab]
      · simpa [boundaryStar, External.RegularSpectralData.starWaveCovariance, hab] using secondNeighborBoundary_im d E hd hbulk

end GeneralizedBulk.KestenMcKay
