import GeneralizedBulk.Gaussian.StarCovariancePositive
import GeneralizedBulk.Entropy.ScalarCoordinates

/-! Actual whitening coordinates extended by the literal unit star normal.
The reference covariance is nonsingular and the factor uses the same scalar
coordinates as the empirical normalized signal. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.Gaussian
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.External.RegularSpectralData

theorem finrank_transverse (d : ℕ) (hd : 0 < d) : Module.finrank ℝ (Transverse d) = d - 1 := by
  have hs : Function.Surjective (coordinateSum d) := by
    intro x
    refine ⟨EuclideanSpace.single ⟨0, hd⟩ x, ?_⟩
    simp [coordinateSum, EuclideanSpace.single_apply]
  have hr : Module.finrank ℝ (LinearMap.range (coordinateSum d)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hs]
    simp
  have hn := (coordinateSum d).finrank_range_add_finrank_ker
  rw [hr] at hn
  have ha : Module.finrank ℝ (Ambient d) = d := by simp [Ambient]
  rw [ha] at hn
  change 1 + Module.finrank ℝ (Transverse d) = d at hn
  omega

theorem finrank_whiteStar (d : ℕ) (hd : 0 < d) : Module.finrank ℝ (WhiteStar d) = d := by
  have hh := (WithLp.linearEquiv 2 ℝ (ℝ × Transverse d)).finrank_eq
  rw [Module.finrank_prod, Module.finrank_self, finrank_transverse d hd] at hh
  change Module.finrank ℝ (WhiteStar d) = _ at hh
  omega

theorem card_whiteCoordinate (d : ℕ) (hd : 0 < d) : Fintype.card (WhiteCoordinate d) = d := by
  simp only [WhiteCoordinate, Fintype.card_sum, Fintype.card_fin, Module.finrank_self,
    finrank_transverse d hd]
  omega

def adaptedStarCoefficients (d : ℕ) (hd : 2 ≤ d) (E : ℝ) :
    Matrix (Fin (d + 1)) (WhiteCoordinate d) ℝ :=
  fun j a => (scalarAdaptedWhiteBasis d).repr (starRow d hd E j) a

theorem adaptedStarCoefficients_gram (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    adaptedStarCoefficients d hd E * (adaptedStarCoefficients d hd E).transpose = starWaveCovariance d E := by
  ext j l
  change (∑ a, (scalarAdaptedWhiteBasis d).repr (starRow d hd E j) a *
    (scalarAdaptedWhiteBasis d).repr (starRow d hd E l) a) = _
  calc
    _ = @inner ℝ (EuclideanSpace ℝ (WhiteCoordinate d)) _
        ((scalarAdaptedWhiteBasis d).repr (starRow d hd E j))
        ((scalarAdaptedWhiteBasis d).repr (starRow d hd E l)) := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = @inner ℝ (WhiteStar d) _ (starRow d hd E j) (starRow d hd E l) :=
      (scalarAdaptedWhiteBasis d).repr.inner_map_map _ _
    _ = _ := starRow_gram d hd E hE j l

abbrev ExtendedWhiteCoordinate (d : ℕ) := WhiteCoordinate d ⊕ Unit

def extendedStarCoefficients (d : ℕ) (hd : 2 ≤ d) (E : ℝ) :
    Matrix (Fin (d + 1)) (ExtendedWhiteCoordinate d) ℝ :=
  fun j a => Sum.elim (adaptedStarCoefficients d hd E j) (fun _ => normalizedStarNormal d E j) a

theorem extendedStarCoefficients_gram (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    extendedStarCoefficients d hd E * (extendedStarCoefficients d hd E).transpose =
      starWaveCovariance d E + starNormalProjection d E := by
  ext j l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, extendedStarCoefficients,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique,
    Matrix.add_apply, starNormalProjection, Covariance.unitNormalProjection]
  have hh := congrFun (congrFun (adaptedStarCoefficients_gram d hd E hE) j) l
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type] using
    congrArg (fun z : ℝ => z + normalizedStarNormal d E j * normalizedStarNormal d E l) hh

theorem adaptedStarCoefficients_action (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (x : WhiteStar d) (j : Fin (d + 1)) :
    (adaptedStarCoefficients d hd E *ᵥ (fun a => (scalarAdaptedWhiteBasis d).repr x a)) j =
      @inner ℝ (WhiteStar d) _ (starRow d hd E j) x := by
  have hh := (scalarAdaptedWhiteBasis d).repr.inner_map_map (starRow d hd E j) x
  simpa only [adaptedStarCoefficients, Matrix.mulVec, dotProduct, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, mul_comm] using hh

theorem extendedStarCoefficients_action (d : ℕ) (hd : 2 ≤ d) (E : ℝ)
    (x : WhiteCoordinate d → ℝ) (z : ℝ) (j : Fin (d + 1)) :
    (extendedStarCoefficients d hd E *ᵥ Sum.elim x (fun _ : Unit => z)) j =
      (adaptedStarCoefficients d hd E *ᵥ x) j + normalizedStarNormal d E j * z := by
  simp only [Matrix.mulVec, dotProduct, extendedStarCoefficients, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique]

def extendedCoordinateEquiv (d : ℕ) (hd : 0 < d) : Fin (d + 1) ≃ ExtendedWhiteCoordinate d :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_fin, ExtendedWhiteCoordinate, Fintype.card_sum,
    card_whiteCoordinate d hd, Fintype.card_unique])

def extendedStarFactor (d : ℕ) (hd : 2 ≤ d) (E : ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun j a => extendedStarCoefficients d hd E j (extendedCoordinateEquiv d (by omega) a)

theorem extendedStarFactor_covariance (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    extendedStarFactor d hd E * (extendedStarFactor d hd E).transpose =
      starWaveCovariance d E + starNormalProjection d E := by
  ext j l
  have hh := congrFun (congrFun (extendedStarCoefficients_gram d hd E hE) j) l
  change (∑ a, extendedStarCoefficients d hd E j (extendedCoordinateEquiv d (by omega) a) *
    extendedStarCoefficients d hd E l (extendedCoordinateEquiv d (by omega) a)) = _
  rw [Equiv.sum_comp (extendedCoordinateEquiv d (by omega))
    (fun a => extendedStarCoefficients d hd E j a * extendedStarCoefficients d hd E l a)]
  exact hh

theorem extendedStarFactor_det_ne_zero (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    (extendedStarFactor d hd E).det ≠ 0 := by
  have hh := (starWave_add_normal_posDef d hd E hE).det_pos
  rw [← extendedStarFactor_covariance d hd E hE, Matrix.det_mul, Matrix.det_transpose] at hh
  intro hz
  simp only [hz, zero_mul, lt_self_iff_false] at hh

end GeneralizedBulk.Gaussian
