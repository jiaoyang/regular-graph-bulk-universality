import GeneralizedBulk.Gaussian.ExtendedWhitening

/-! The actual colored extended whitening factor, with tangent coordinates
exactly `ScalarCoordinate d k` and independent normal coordinates `Fin k`. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.Gaussian
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.External.RegularSpectralData

abbrev ExtendedColoredCoordinate (d k : ℕ) := ScalarCoordinate d k ⊕ Fin k

def coloredExtendedCoordinateEquiv (d k : ℕ) :
    ExtendedColoredCoordinate d k ≃ Fin k × ExtendedWhiteCoordinate d where
  toFun := Sum.elim (fun ai : ScalarCoordinate d k => (ai.1, Sum.inl ai.2)) (fun a : Fin k => (a, Sum.inr ()))
  invFun := fun ai : Fin k × ExtendedWhiteCoordinate d =>
    Sum.elim (fun i : WhiteCoordinate d => Sum.inl ⟨ai.1, i⟩) (fun _ : Unit => Sum.inr ai.1) ai.2
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with ⟨a, t⟩
    cases t with
    | inl i => rfl
    | inr u => cases u; rfl

def coloredExtendedCoefficients (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ) :
    Matrix (Fin k × Fin (d + 1)) (ExtendedColoredCoordinate d k) ℝ := fun aj b =>
  let ai := coloredExtendedCoordinateEquiv d k b
  if aj.1 = ai.1 then extendedStarCoefficients d hd (energy aj.1) aj.2 ai.2 else 0

@[simp] theorem coloredExtendedCoefficients_inl (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (aj : Fin k × Fin (d + 1)) (ai : ScalarCoordinate d k) :
    coloredExtendedCoefficients d k hd energy aj (Sum.inl ai) =
      if aj.1 = ai.1 then adaptedStarCoefficients d hd (energy aj.1) aj.2 ai.2 else 0 := rfl

@[simp] theorem coloredExtendedCoefficients_inr (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (aj : Fin k × Fin (d + 1)) (a : Fin k) :
    coloredExtendedCoefficients d k hd energy aj (Sum.inr a) =
      if aj.1 = a then normalizedStarNormal d (energy aj.1) aj.2 else 0 := rfl

def coloredReferenceCovariance (d k : ℕ) (energy : Fin k → ℝ) :
    Matrix (Fin k × Fin (d + 1)) (Fin k × Fin (d + 1)) ℝ := fun aj bl =>
  if aj.1 = bl.1 then (starWaveCovariance d (energy aj.1) + starNormalProjection d (energy aj.1)) aj.2 bl.2 else 0

/-- The full colored reference covariance is the actual Gram matrix of the
extended whitening coefficients. -/
theorem coloredExtendedCoefficients_gram (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) :
    coloredExtendedCoefficients d k hd energy * (coloredExtendedCoefficients d k hd energy).transpose =
      coloredReferenceCovariance d k energy := by
  ext aj bl
  change (∑ b, coloredExtendedCoefficients d k hd energy aj b * coloredExtendedCoefficients d k hd energy bl b) = _
  unfold coloredExtendedCoefficients
  rw [Equiv.sum_comp (coloredExtendedCoordinateEquiv d k)
    (fun ai => (if aj.1 = ai.1 then extendedStarCoefficients d hd (energy aj.1) aj.2 ai.2 else 0) *
      (if bl.1 = ai.1 then extendedStarCoefficients d hd (energy bl.1) bl.2 ai.2 else 0))]
  rw [Fintype.sum_prod_type]
  by_cases hab : aj.1 = bl.1
  · simp only [coloredReferenceCovariance, hab, ↓reduceIte]
    have hh := congrFun (congrFun (extendedStarCoefficients_gram d hd (energy bl.1) (hE bl.1)) aj.2) bl.2
    simpa [hab, mul_ite, ite_mul, Finset.sum_ite_irrel, Matrix.mul_apply, Matrix.transpose_apply] using hh
  · have hne (a : Fin k) : ¬(aj.1 = a ∧ bl.1 = a) := by
      rintro ⟨ha, hb⟩; exact hab (ha.trans hb.symm)
    simp only [coloredReferenceCovariance, if_neg hab]
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hja : aj.1 = a <;> by_cases hba : bl.1 = a <;> simp_all

/-- A square version on the physical star coordinates. The column permutation
is fixed independently of all energies and empirical signals. -/
def coloredExtendedInputEquiv (d k : ℕ) (hd : 0 < d) :
    (Fin k × Fin (d + 1)) ≃ ExtendedColoredCoordinate d k :=
  ((Equiv.refl (Fin k)).prodCongr (extendedCoordinateEquiv d hd)).trans
    (coloredExtendedCoordinateEquiv d k).symm

def coloredExtendedFactor (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ) :
    Matrix (Fin k × Fin (d + 1)) (Fin k × Fin (d + 1)) ℝ :=
  (coloredExtendedCoefficients d k hd energy).submatrix id (coloredExtendedInputEquiv d k (by omega))

theorem coloredExtendedFactor_covariance (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) :
    coloredExtendedFactor d k hd energy * (coloredExtendedFactor d k hd energy).transpose =
      coloredReferenceCovariance d k energy := by
  unfold coloredExtendedFactor
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
    coloredExtendedCoefficients_gram d k hd energy hE]

theorem coloredExtendedFactor_blockDiagonal (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ) :
    coloredExtendedFactor d k hd energy =
      (Matrix.blockDiagonal (fun a => extendedStarFactor d hd (energy a))).submatrix
        (Equiv.prodComm (Fin k) (Fin (d + 1))) (Equiv.prodComm (Fin k) (Fin (d + 1))) := by
  ext aj bl
  simp only [coloredExtendedFactor, Matrix.submatrix_apply, coloredExtendedCoefficients,
    coloredExtendedInputEquiv, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodCongr_apply,
    Equiv.refl_apply, Matrix.blockDiagonal_apply, Equiv.prodComm_apply, extendedStarFactor,
    Prod.map, Prod.swap, id_eq]

/-- Nonsingularity is proved from the actual one-color factors and the literal
block diagonal determinant. -/
theorem coloredExtendedFactor_det_ne_zero (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) : (coloredExtendedFactor d k hd energy).det ≠ 0 := by
  rw [coloredExtendedFactor_blockDiagonal, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun a _ => extendedStarFactor_det_ne_zero d hd (energy a) (hE a))

theorem coloredExtendedCoefficients_action (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (x : ScalarCoordinate d k → ℝ) (z : Fin k → ℝ) (aj : Fin k × Fin (d + 1)) :
    (coloredExtendedCoefficients d k hd energy *ᵥ Sum.elim x z) aj =
      (adaptedStarCoefficients d hd (energy aj.1) *ᵥ (fun i => x ⟨aj.1, i⟩)) aj.2 +
        normalizedStarNormal d (energy aj.1) aj.2 * z aj.1 := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_sigma,
    coloredExtendedCoefficients_inl, coloredExtendedCoefficients_inr, ite_mul, Finset.sum_ite_irrel]

/-- The extended factor sends actual scalar-adapted coordinates back to the
physical star, and adds precisely the independent unit-normal coordinate. -/
theorem coloredExtendedCoefficients_scalarCoordinates (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (x : ColoredStar d k) (z : Fin k → ℝ) (aj : Fin k × Fin (d + 1)) :
    (coloredExtendedCoefficients d k hd energy *ᵥ Sum.elim (scalarCoordinates d k x) z) aj =
      @inner ℝ (WhiteStar d) _ (starRow d hd (energy aj.1) aj.2) (x aj.1) +
        normalizedStarNormal d (energy aj.1) aj.2 * z aj.1 := by
  rw [coloredExtendedCoefficients_action]
  simp only [scalarCoordinates_apply]
  rw [adaptedStarCoefficients_action]

end GeneralizedBulk.Gaussian
