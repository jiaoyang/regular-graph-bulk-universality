import GeneralizedBulk.Gaussian.StarWhiteningGram
import GeneralizedBulk.Spectral.KestenMcKayBulkPotential

/-! Exact determinants of the genuine star reference covariance and its
root-neighbor edge marginal. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.Gaussian
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.External.RegularSpectralData

def scalarWhiteningEigenvalue (d : ℕ) (E : ℝ) : ℝ := ((d : ℝ) + E ^ 2) / d

def transverseWhiteningEigenvalue (d : ℕ) (E : ℝ) : ℝ :=
  ((d : ℝ) ^ 2 - E ^ 2) / ((d : ℝ) * ((d : ℝ) - 1))

def whiteWhiteningEigenvalue (d : ℕ) (E : ℝ) : WhiteCoordinate d → ℝ :=
  Sum.elim (fun _ => scalarWhiteningEigenvalue d E) (fun _ => transverseWhiteningEigenvalue d E)

theorem adaptedStarCoefficients_transpose_gram (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    (adaptedStarCoefficients d hd E).transpose * adaptedStarCoefficients d hd E =
      Matrix.diagonal (whiteWhiteningEigenvalue d E) := by
  have hcoef (j : Fin (d + 1)) (a : WhiteCoordinate d) : adaptedStarCoefficients d hd E j a =
      @inner ℝ (WhiteStar d) _ (starRow d hd E j) (scalarAdaptedWhiteBasis d a) := by
    rw [adaptedStarCoefficients, OrthonormalBasis.repr_apply_apply, real_inner_comm]
  have hreal (a b : Fin (Module.finrank ℝ ℝ)) :
      stdOrthonormalBasis ℝ ℝ a * stdOrthonormalBasis ℝ ℝ b = if a = b then 1 else 0 := by
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
      orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ ℝ).orthonormal a b
  have htrans (a b : Fin (Module.finrank ℝ (Transverse d))) :
      @inner ℝ (Transverse d) _ (stdOrthonormalBasis ℝ (Transverse d) a)
        (stdOrthonormalBasis ℝ (Transverse d) b) = if a = b then 1 else 0 :=
    orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ (Transverse d)).orthonormal a b
  ext a b
  change (∑ j, adaptedStarCoefficients d hd E j a * adaptedStarCoefficients d hd E j b) = _
  simp_rw [hcoef]
  rw [starRow_bilinear d hd E hE]
  cases a with
  | inl a =>
    cases b with
    | inl b => simp [scalarAdaptedWhiteBasis, OrthonormalBasis.prod_apply, whiteWhiteningEigenvalue,
        scalarWhiteningEigenvalue, Matrix.diagonal, mul_assoc, hreal, mul_ite]
    | inr b => simp [scalarAdaptedWhiteBasis, OrthonormalBasis.prod_apply, whiteWhiteningEigenvalue, Matrix.diagonal]
  | inr a =>
    cases b with
    | inl b => simp [scalarAdaptedWhiteBasis, OrthonormalBasis.prod_apply, whiteWhiteningEigenvalue, Matrix.diagonal]
    | inr b => simp [scalarAdaptedWhiteBasis, OrthonormalBasis.prod_apply, whiteWhiteningEigenvalue,
        transverseWhiteningEigenvalue, Matrix.diagonal, htrans]

theorem adaptedStarCoefficients_normal_orthogonal (d : ℕ) (hd : 2 ≤ d) (E : ℝ)
    (a : WhiteCoordinate d) :
    (∑ j, adaptedStarCoefficients d hd E j a * normalizedStarNormal d E j) = 0 := by
  simp only [adaptedStarCoefficients, OrthonormalBasis.repr_apply_apply, normalizedStarNormal]
  calc
    _ = (∑ j, entropyStarNormal E j * @inner ℝ (WhiteStar d) _
        (starRow d hd E j) (scalarAdaptedWhiteBasis d a)) / Real.sqrt ((d : ℝ) + E ^ 2) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      rw [real_inner_comm]
      ring
    _ = 0 := by rw [starRow_normal_pairing_zero, zero_div]

def extendedWhiteningEigenvalue (d : ℕ) (E : ℝ) : ExtendedWhiteCoordinate d → ℝ :=
  Sum.elim (whiteWhiteningEigenvalue d E) (fun _ => 1)

theorem extendedStarCoefficients_transpose_gram (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    (extendedStarCoefficients d hd E).transpose * extendedStarCoefficients d hd E =
      Matrix.diagonal (extendedWhiteningEigenvalue d E) := by
  ext a b
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hh := congrFun (congrFun (adaptedStarCoefficients_transpose_gram d hd E hE) a) b
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, extendedStarCoefficients,
        Sum.elim_inl, extendedWhiteningEigenvalue, Matrix.diagonal_apply, Sum.inl.injEq] using hh
    | inr b =>
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, extendedStarCoefficients,
        Sum.elim_inl, Sum.elim_inr, extendedWhiteningEigenvalue, Matrix.diagonal,
        Sum.inl_ne_inr, ↓reduceIte] using adaptedStarCoefficients_normal_orthogonal d hd E a
  | inr a =>
    cases b with
    | inl b =>
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, extendedStarCoefficients,
        Sum.elim_inl, Sum.elim_inr, extendedWhiteningEigenvalue, Matrix.diagonal,
        Sum.inr_ne_inl, ↓reduceIte, mul_comm] using adaptedStarCoefficients_normal_orthogonal d hd E b
    | inr b =>
      have hh := normalizedStarNormal_sq_sum d (by omega) E
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, extendedStarCoefficients,
        Sum.elim_inr, extendedWhiteningEigenvalue, Matrix.diagonal, Subsingleton.elim a b,
        ↓reduceIte, ← sq] using hh

theorem extendedStarFactor_transpose_gram (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    (extendedStarFactor d hd E).transpose * extendedStarFactor d hd E =
      Matrix.diagonal (fun a => extendedWhiteningEigenvalue d E (extendedCoordinateEquiv d (by omega) a)) := by
  ext a b
  change (∑ j, extendedStarCoefficients d hd E j (extendedCoordinateEquiv d (by omega) a) *
    extendedStarCoefficients d hd E j (extendedCoordinateEquiv d (by omega) b)) = _
  have hh := congrFun (congrFun (extendedStarCoefficients_transpose_gram d hd E hE)
    (extendedCoordinateEquiv d (by omega) a)) (extendedCoordinateEquiv d (by omega) b)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply,
    (extendedCoordinateEquiv d (by omega)).injective.eq_iff] using hh

theorem starWave_add_normal_det (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    (starWaveCovariance d E + starNormalProjection d E).det =
      scalarWhiteningEigenvalue d E * transverseWhiteningEigenvalue d E ^ (d - 1) := by
  rw [← extendedStarFactor_covariance d hd E hE]
  have hg := congrArg Matrix.det (extendedStarFactor_transpose_gram d hd E hE)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at hg
  rw [Matrix.det_mul, Matrix.det_transpose, hg,
    Equiv.prod_comp (extendedCoordinateEquiv d (by omega)) (extendedWhiteningEigenvalue d E)]
  simp only [extendedWhiteningEigenvalue, ExtendedWhiteCoordinate, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, WhiteCoordinate, whiteWhiteningEigenvalue,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Module.finrank_self, pow_one,
    finrank_transverse d (by omega), one_pow, mul_one]

def edgeStarIndex (d : ℕ) (hd : 1 ≤ d) : Fin 2 → Fin (d + 1) :=
  Fin.cases 0 (fun _ => Fin.succ ⟨0, by omega⟩)

def edgeWaveCovariance (d : ℕ) (E : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, E / d; E / d, 1]

theorem edgeWaveCovariance_eq_restriction (d : ℕ) (hd : 1 ≤ d) (E : ℝ) :
    edgeWaveCovariance d E =
      (starWaveCovariance d E).submatrix (edgeStarIndex d hd) (edgeStarIndex d hd) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [edgeWaveCovariance, edgeStarIndex, starWaveCovariance, Matrix.submatrix, Fin.cases] <;> rfl

theorem edgeWaveCovariance_det (d : ℕ) (E : ℝ) (hd : d ≠ 0) :
    (edgeWaveCovariance d E).det = ((d : ℝ)^2 - E^2) / (d : ℝ)^2 := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  rw [edgeWaveCovariance, Matrix.det_fin_two]
  field_simp
  <;> ring

theorem scalarWhiteningEigenvalue_pos (d : ℕ) (hd : 0 < d) (E : ℝ) :
    0 < scalarWhiteningEigenvalue d E := by
  unfold scalarWhiteningEigenvalue
  exact div_pos (add_pos_of_pos_of_nonneg (Nat.cast_pos.mpr hd) (sq_nonneg E)) (Nat.cast_pos.mpr hd)

theorem transverseWhiteningEigenvalue_pos (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    0 < transverseWhiteningEigenvalue d E := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hd1 : 0 < (d : ℝ)-1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have he : E^2 < (d : ℝ)^2 := sq_lt_sq.mpr (by simpa [abs_of_pos hd0] using hE)
  exact div_pos (sub_pos.mpr he) (mul_pos hd0 hd1)

theorem starWave_add_normal_logdet (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    Real.log ((starWaveCovariance d E + starNormalProjection d E).det) =
      Real.log (scalarWhiteningEigenvalue d E) +
        (d - 1 : ℕ) * Real.log (transverseWhiteningEigenvalue d E) := by
  rw [starWave_add_normal_det d hd E hE,
    Real.log_mul (scalarWhiteningEigenvalue_pos d (by omega) E).ne'
      (pow_ne_zero _ (transverseWhiteningEigenvalue_pos d hd E hE).ne'), Real.log_pow]

theorem gaussianStarFunctional (d : ℕ) (hd : 3 ≤ d) (E : ℝ) (hE : |E| < 2 * Real.sqrt ((d : ℝ)-1)) :
    Real.log ((starWaveCovariance d E + starNormalProjection d E).det) / 2 -
      (d : ℝ) / 4 * Real.log ((edgeWaveCovariance d E).det) =
      Real.log ((d : ℝ) + E^2) / 2 - GeneralizedBulk.KestenMcKay.bulkPotential d E := by
  have hd2 : 2 ≤ d := by omega
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hd1 : 0 < (d : ℝ)-1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hr : 2 * Real.sqrt ((d : ℝ)-1) < d := by
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hs := Real.sq_sqrt hd1.le
    have hpos : 0 < ((d : ℝ)-2)^2 := sq_pos_of_pos (by linarith)
    nlinarith [Real.sqrt_nonneg ((d : ℝ)-1)]
  have hEd : |E| < d := lt_trans hE hr
  have hdisc : 0 < (d : ℝ)^2-E^2 := by
    have he : E^2 < (d : ℝ)^2 := sq_lt_sq.mpr (by simpa [abs_of_pos hd0] using hEd)
    linarith
  have hsum : 0 < (d : ℝ)+E^2 := add_pos_of_pos_of_nonneg hd0 (sq_nonneg E)
  rw [starWave_add_normal_logdet d hd2 E hEd, edgeWaveCovariance_det d E (by omega)]
  unfold scalarWhiteningEigenvalue transverseWhiteningEigenvalue GeneralizedBulk.KestenMcKay.bulkPotential
  rw [Real.log_div hsum.ne' hd0.ne', Real.log_div hdisc.ne' (mul_pos hd0 hd1).ne',
    Real.log_mul hd0.ne' hd1.ne', Real.log_div hdisc.ne' (pow_ne_zero _ hd0.ne'), Real.log_pow]
  rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  ring

end GeneralizedBulk.Gaussian
