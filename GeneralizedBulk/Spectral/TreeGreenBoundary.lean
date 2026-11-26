import GeneralizedBulk.Parameters

/-! Exact algebraic boundary values of the regular-tree cavity and diagonal
Green functions. These identities will feed the logarithmic-potential and
local covariance calculations. -/
noncomputable section
namespace GeneralizedBulk.KestenMcKay

 def discriminant (d E : ℝ) : ℝ := 4 * (d - 1) - E ^ 2

 def cavityBoundary (d E : ℝ) : ℂ :=
  ⟨-E / (2 * (d - 1)), Real.sqrt (discriminant d E) / (2 * (d - 1))⟩

 def diagonalBoundary (d E : ℝ) : ℂ :=
  ⟨-((d - 2) * E) / (2 * (d ^ 2 - E ^ 2)),
    d * Real.sqrt (discriminant d E) / (2 * (d ^ 2 - E ^ 2))⟩

 theorem bulk_denominator_pos (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    0 < d ^ 2 - E ^ 2 := by nlinarith [sq_nonneg (d - 3)]

 theorem cavityBoundary_quadratic (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    (d - 1 : ℂ) * cavityBoundary d E ^ 2 + (E : ℂ) * cavityBoundary d E + 1 = 0 := by
  have hq : d - 1 ≠ 0 := by linarith
  have hs : Real.sqrt (discriminant d E) ^ 2 = 4 * (d - 1) - E ^ 2 :=
    Real.sq_sqrt (by dsimp [discriminant]; linarith)
  have hs3 : Real.sqrt (discriminant d E) ^ 3 = Real.sqrt (discriminant d E) * (4 * (d - 1) - E ^ 2) := by
    rw [pow_succ, hs]
    ring
  rw [pow_two]
  apply Complex.ext
  · simp only [cavityBoundary, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.zero_re]
    field_simp [hq]
    ring_nf
    simp only [hs, hs3]
    ring
  · simp only [cavityBoundary, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_im, Complex.zero_im]
    field_simp [hq]
    <;> ring

 theorem cavityBoundary_normSq (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    Complex.normSq (cavityBoundary d E) = (d - 1)⁻¹ := by
  have hq : d - 1 ≠ 0 := by linarith
  have hs : Real.sqrt (discriminant d E) ^ 2 = 4 * (d - 1) - E ^ 2 :=
    Real.sq_sqrt (by dsimp [discriminant]; linarith)
  have hs3 : Real.sqrt (discriminant d E) ^ 3 = Real.sqrt (discriminant d E) * (4 * (d - 1) - E ^ 2) := by
    rw [pow_succ, hs]
    ring
  simp only [Complex.normSq_apply, cavityBoundary]
  field_simp [hq]
  ring_nf
  simp only [hs]
  ring

 theorem diagonalBoundary_cavity_relation (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    diagonalBoundary d E * (1 - cavityBoundary d E ^ 2) = cavityBoundary d E := by
  have hq : d - 1 ≠ 0 := by linarith
  have hden := (bulk_denominator_pos d E hd hbulk).ne'
  have hs : Real.sqrt (discriminant d E) ^ 2 = 4 * (d - 1) - E ^ 2 :=
    Real.sq_sqrt (by dsimp [discriminant]; linarith)
  have hs3 : Real.sqrt (discriminant d E) ^ 3 = Real.sqrt (discriminant d E) * (4 * (d - 1) - E ^ 2) := by
    rw [pow_succ, hs]
    ring
  rw [pow_two]
  apply Complex.ext
  · simp only [diagonalBoundary, cavityBoundary, Complex.mul_re, Complex.sub_re,
      Complex.sub_im,   Complex.one_re, Complex.one_im]
    field_simp [hq, hden]
    ring_nf
    simp only [hs, hs3]
    ring
  · simp only [diagonalBoundary, cavityBoundary, Complex.mul_im, Complex.sub_re,
      Complex.sub_im,   Complex.one_re, Complex.one_im]
    field_simp [hq, hden]
    ring_nf
    simp only [hs, hs3]
    ring

theorem one_sub_cavityBoundary_sq_normSq (d E : ℝ) (hd : 3 ≤ d)
    (hbulk : E ^ 2 < 4 * (d - 1)) :
    Complex.normSq (1 - cavityBoundary d E ^ 2) = (d ^ 2 - E ^ 2) / (d - 1) ^ 2 := by
  have hq : d - 1 ≠ 0 := by linarith
  have hs : Real.sqrt (discriminant d E) ^ 2 = 4 * (d - 1) - E ^ 2 :=
    Real.sq_sqrt (by dsimp [discriminant]; linarith)
  have hs4 : Real.sqrt (discriminant d E) ^ 4 = (4 * (d - 1) - E ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hs]
  rw [pow_two]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, cavityBoundary, Complex.mul_re, Complex.mul_im]
  field_simp [hq]
  ring_nf
  simp only [hs, hs4]
  ring

/-- The real part of the tree analytic primitive has the manuscript's
closed bulk value. Identification with the density integral is separate. -/
theorem treePotential_boundary_value (d E : ℝ) (hd : 3 ≤ d)
    (hbulk : E ^ 2 < 4 * (d - 1)) :
    -(1 / 2 : ℝ) * Real.log (Complex.normSq (cavityBoundary d E)) -
      (d - 2) / 4 * Real.log (Complex.normSq (1 - cavityBoundary d E ^ 2)) =
      (d - 1) / 2 * Real.log (d - 1) - (d - 2) / 4 * Real.log (d ^ 2 - E ^ 2) := by
  have hq : d - 1 ≠ 0 := by linarith
  have hden := (bulk_denominator_pos d E hd hbulk).ne'
  rw [cavityBoundary_normSq d E hd hbulk, one_sub_cavityBoundary_sq_normSq d E hd hbulk,
    Real.log_inv, Real.log_div hden (pow_ne_zero 2 hq), Real.log_pow]
  ring

/-- The displayed diagonal and cavity boundary values obey the actual root
resolvent recursion. -/
theorem diagonalBoundary_root_recursion (d E : ℝ) (hd : 3 ≤ d)
    (hbulk : E ^ 2 < 4 * (d - 1)) :
    (E : ℂ) * diagonalBoundary d E + (d : ℂ) * diagonalBoundary d E * cavityBoundary d E = -1 := by
  have hq : d - 1 ≠ 0 := by linarith
  have hden := (bulk_denominator_pos d E hd hbulk).ne'
  have hs : Real.sqrt (discriminant d E) ^ 2 = 4 * (d - 1) - E ^ 2 :=
    Real.sq_sqrt (by dsimp [discriminant]; linarith)
  apply Complex.ext
  · simp only [diagonalBoundary, cavityBoundary, Complex.add_re, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.one_re]
    field_simp [hq, hden]
    ring_nf
    simp only [hs]
    ring
  · simp only [diagonalBoundary, cavityBoundary, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im, Complex.one_im]
    field_simp [hq, hden]
    <;> ring

end GeneralizedBulk.KestenMcKay
