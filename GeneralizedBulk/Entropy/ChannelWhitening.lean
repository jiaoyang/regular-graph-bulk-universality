import GeneralizedBulk.Entropy.ChannelFrames

/-! The concrete whitening map is an isomorphism onto the physical star constraint. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel

abbrev Physical (d : ℕ) := EuclideanSpace ℝ (Option (Fin d))

def starConstraintMap (d : ℕ) (c : ℝ) : Physical d →ₗ[ℝ] ℝ where
  toFun x := (∑ i : Fin d, x (some i)) - ((d : ℝ) * c) * x none
  map_add' x y := by simp [Finset.sum_add_distrib]; ring
  map_smul' a x := by simp [← Finset.mul_sum]; ring

def physicalStar (d : ℕ) (c : ℝ) : Submodule ℝ (Physical d) := LinearMap.ker (starConstraintMap d c)

@[simp] theorem physicalStar_constraint (d : ℕ) (c : ℝ) (x : physicalStar d c) :
    (∑ i : Fin d, (x : Physical d) (some i)) = ((d : ℝ) * c) * (x : Physical d) none :=
  sub_eq_zero.mp x.property

def whiteningInto (d : ℕ) (hd : 2 ≤ d) (c rho : ℝ) : WhiteStar d →ₗ[ℝ] physicalStar d c :=
  (physicalLinearMap d hd c rho).codRestrict (physicalStar d c) (fun y => by
    change (∑ i : Fin d, physicalLinearMap d hd c rho y (some i)) -
      ((d : ℝ) * c) * physicalLinearMap d hd c rho y none = 0
    rw [physical_star_constraint, sub_self])

theorem simplex_inner_coordinate (d : ℕ) (hd : 2 ≤ d) (i : Fin d) (y : Transverse d) :
    @inner ℝ (Transverse d) _ (simplex d hd i) y = simplexScale d * (y : Ambient d) i := by
  change @inner ℝ (Ambient d) _ (simplexScale d • centeredCoordinate d i) y = _
  rw [inner_smul_left, inner_centeredCoordinate_left, transverse_sum]
  simp

/-- The inverse uses the centered physical leaf coordinates, divided by their
actual transverse Gaussian standard deviation. -/
def inverseWhitening (d : ℕ) (c rho : ℝ) (x : physicalStar d c) : WhiteStar d :=
  (WithLp.equiv 2 _).symm ((x : Physical d) none,
    ⟨(WithLp.equiv 2 _).symm (fun i =>
      ((x : Physical d) (some i) - c * (x : Physical d) none) / (rho * simplexScale d)), by
      change (∑ i : Fin d, ((x : Physical d) (some i) - c * (x : Physical d) none) /
        (rho * simplexScale d)) = 0
      rw [← Finset.sum_div, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        physicalStar_constraint]
      have hz : ((d : ℝ) * c) * (x : Physical d) none -
          (d : ℝ) * (c * (x : Physical d) none) = 0 := by ring
      rw [hz, zero_div]⟩)

theorem inverseWhitening_left (d : ℕ) (hd : 2 ≤ d) (c rho : ℝ) (hrho : rho ≠ 0)
    (y : WhiteStar d) : inverseWhitening d c rho (whiteningInto d hd c rho y) = y := by
  have hs : simplexScale d ≠ 0 := ne_of_gt (simplexScale_pos d hd)
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    ext i
    change (c * y.fst + rho * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd - c * y.fst) /
      (rho * simplexScale d) = (y.snd : Ambient d) i
    rw [simplex_inner_coordinate]
    field_simp
    ring

theorem inverseWhitening_right (d : ℕ) (hd : 2 ≤ d) (c rho : ℝ) (hrho : rho ≠ 0)
    (x : physicalStar d c) : whiteningInto d hd c rho (inverseWhitening d c rho x) = x := by
  have hs : simplexScale d ≠ 0 := ne_of_gt (simplexScale_pos d hd)
  apply Subtype.ext
  ext idx
  cases idx with
  | none => rfl
  | some i =>
    change c * (x : Physical d) none + rho * @inner ℝ (Transverse d) _ (simplex d hd i)
      (inverseWhitening d c rho x).snd = (x : Physical d) (some i)
    rw [simplex_inner_coordinate]
    change c * (x : Physical d) none + rho * (simplexScale d *
      (((x : Physical d) (some i) - c * (x : Physical d) none) / (rho * simplexScale d))) = _
    field_simp
    ring

/-- Actual linear equivalence to the singular physical Gaussian star space. -/
def whiteningEquiv (d : ℕ) (hd : 2 ≤ d) (c rho : ℝ) (hrho : rho ≠ 0) :
    WhiteStar d ≃ₗ[ℝ] physicalStar d c :=
  { whiteningInto d hd c rho with
    invFun := inverseWhitening d c rho
    left_inv := inverseWhitening_left d hd c rho hrho
    right_inv := inverseWhitening_right d hd c rho hrho }

/-- Both whitening eigenvalues are positive whenever the transverse variance
is nonzero; bulk parameters satisfy this by their explicit formula. -/
theorem whitening_eigenvalues_pos (d : ℕ) (hd : 2 ≤ d) (c rho : ℝ) (hrho : rho ≠ 0) :
    0 < 1 + (d : ℝ) * c ^ 2 ∧ 0 < (d : ℝ) * rho ^ 2 / ((d : ℝ) - 1) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  constructor
  · positivity
  · exact div_pos (mul_pos (by linarith) (sq_pos_of_ne_zero hrho)) (by linarith)

/-- Exact quantitative lower and upper bounds for the concrete whitening map. -/
theorem whitening_norm_sq_bounds (d : ℕ) (hd : 2 ≤ d) (c rho : ℝ) (y : WhiteStar d) :
    min (1 + (d : ℝ) * c ^ 2) ((d : ℝ) * rho ^ 2 / ((d : ℝ) - 1)) * ‖y‖ ^ 2 ≤
      ‖physicalLinearMap d hd c rho y‖ ^ 2 ∧
    ‖physicalLinearMap d hd c rho y‖ ^ 2 ≤
      max (1 + (d : ℝ) * c ^ 2) ((d : ℝ) * rho ^ 2 / ((d : ℝ) - 1)) * ‖y‖ ^ 2 := by
  rw [physicalLinearMap_norm_sq, whiteStar_norm_sq]
  constructor
  · calc
      _ = min (1 + (d : ℝ) * c ^ 2) ((d : ℝ) * rho ^ 2 / ((d : ℝ) - 1)) * y.fst ^ 2 +
          min (1 + (d : ℝ) * c ^ 2) ((d : ℝ) * rho ^ 2 / ((d : ℝ) - 1)) * ‖y.snd‖ ^ 2 := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
  · calc
      _ ≤ max (1 + (d : ℝ) * c ^ 2) ((d : ℝ) * rho ^ 2 / ((d : ℝ) - 1)) * y.fst ^ 2 +
          max (1 + (d : ℝ) * c ^ 2) ((d : ℝ) * rho ^ 2 / ((d : ℝ) - 1)) * ‖y.snd‖ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
      _ = _ := by ring

end GeneralizedBulk.Entropy.Channel
