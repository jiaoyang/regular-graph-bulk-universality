import GaussianWave.BS.UpperGeometry
import GaussianWave.BS.GaussianReference

/-!
# Explicit scalar BS star frame

The white star has d actual Euclidean coordinates. The constant root unit
vector and the normalized centered coordinate vectors give orthonormal
root/simplex pairs. Rotating each pair by the BS coefficients produces the
actual two-row observation matrices. Their weighted tight-frame identity is
proved from these coordinates, rather than supplied as a frame premise.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

/-- The root unit vector in the actual d-dimensional white-coordinate space. -/
def starRootDirection (d : ℕ) : Fin d → ℝ := fun _ => 1 / Real.sqrt d

/-- Root coordinate of a white star. -/
def starRootForm {d : ℕ} (x : Fin d → ℝ) : ℝ := (∑ j, x j) / Real.sqrt d

/-- Centered leaf coordinates in the root-orthogonal hyperplane. -/
def starCenteredCoordinate {d : ℕ} (x : Fin d → ℝ) (i : Fin d) : ℝ :=
  x i - (∑ j, x j) / d

/-- The i-th ordinary coordinate vector. -/
def starCoordinateVector {d : ℕ} (i : Fin d) : Fin d → ℝ :=
  fun j => if j = i then 1 else 0

/-- The i-th unit regular-simplex direction. -/
def starSimplexDirection (d : ℕ) (i : Fin d) : Fin d → ℝ :=
  fun j => transverseScale d * starCenteredCoordinate (starCoordinateVector i) j

lemma sum_starCoordinateVector {d : ℕ} (i : Fin d) :
    (∑ j, starCoordinateVector i j) = 1 := by
  simp [starCoordinateVector]

lemma squareRadius_starCoordinateVector {d : ℕ} (i : Fin d) :
    squareRadius (starCoordinateVector i) = 1 := by
  simp [squareRadius, starCoordinateVector]

lemma starSimplexDirection_entry {d : ℕ} (i j : Fin d) :
    starSimplexDirection d i j = transverseScale d *
      ((if j = i then 1 else 0) - 1 / (d : ℝ)) := by
  simp [starSimplexDirection, starCenteredCoordinate, sum_starCoordinateVector,
    starCoordinateVector]

lemma sum_starCenteredCoordinate {d : ℕ} (hd : 0 < d) (x : Fin d → ℝ) :
    (∑ i, starCenteredCoordinate x i) = 0 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [starCenteredCoordinate, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Orthogonal decomposition into the actual root line and centered leaf
hyperplane. No inner-product-space model or isometry is assumed. -/
theorem starRoot_centered_energy {d : ℕ} (hd : 0 < d) (x : Fin d → ℝ) :
    starRootForm x ^ 2 + ∑ i, starCenteredCoordinate x i ^ 2 = squareRadius x := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt hdp.le
  have hs0 : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hdp).ne'
  have hz : (∑ i, starCenteredCoordinate x i ^ 2) =
      squareRadius x - 2 * ((∑ j, x j) / d) * (∑ i, x i) +
        (d : ℝ) * ((∑ j, x j) / d) ^ 2 := by
    calc
      _ = ∑ i, (x i ^ 2 - (2 * ((∑ j, x j) / d)) * x i +
          ((∑ j, x j) / d) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [starCenteredCoordinate]
        ring
      _ = _ := by
        simp only [squareRadius, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  rw [hz]
  dsimp [starRootForm]
  rw [div_pow, hs]
  field_simp
  ring

lemma starRootDirection_norm_sq (d : ℕ) (hd : 0 < d) :
    (∑ j, starRootDirection d j ^ 2) = 1 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [starRootDirection, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, div_pow, one_pow, Real.sq_sqrt hdp.le]
  field_simp

lemma sum_starSimplexDirection (d : ℕ) (hd : 0 < d) (i : Fin d) :
    (∑ j, starSimplexDirection d i j) = 0 := by
  simp only [starSimplexDirection, ← Finset.mul_sum,
    sum_starCenteredCoordinate hd, mul_zero]

lemma starRootDirection_dot_simplex (d : ℕ) (hd : 0 < d) (i : Fin d) :
    (∑ j, starRootDirection d j * starSimplexDirection d i j) = 0 := by
  simp only [starRootDirection, ← Finset.mul_sum, sum_starSimplexDirection d hd i, mul_zero]

lemma starSimplexDirection_norm_sq (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    (∑ j, starSimplexDirection d i j ^ 2) = 1 := by
  have hdp : 0 < d := by omega
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hdp.ne'
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have henergy := starRoot_centered_energy hdp (starCoordinateVector i)
  have hroot : starRootForm (starCoordinateVector i) ^ 2 = 1 / (d : ℝ) := by
    dsimp [starRootForm]
    rw [sum_starCoordinateVector, div_pow, one_pow, Real.sq_sqrt (by positivity)]
  rw [hroot, squareRadius_starCoordinateVector] at henergy
  calc
    _ = transverseScale d ^ 2 * ∑ j,
        starCenteredCoordinate (starCoordinateVector i) j ^ 2 := by
      simp only [starSimplexDirection, mul_pow, Finset.mul_sum]
    _ = ((d : ℝ) / ((d : ℝ) - 1)) * (1 - 1 / (d : ℝ)) := by
      rw [transverseScale_sq d hd]
      congr 1
      linarith
    _ = 1 := by field_simp

/-- Actual two-row orthonormal observation of the i-th edge.
False denotes A and true denotes B. -/
def starEdgeProjection (d : ℕ) (c : ℝ) (i : Fin d) : Matrix Bool (Fin d) ℝ :=
  fun b j => if b then beta c * starRootDirection d j + alpha c * starSimplexDirection d i j
    else alpha c * starRootDirection d j - beta c * starSimplexDirection d i j

private lemma sum_linearCombination_mul {J : Type*} [Fintype J]
    (w e : J → ℝ) (a b a' b' : ℝ) :
    (∑ j, (a * w j + b * e j) * (a' * w j + b' * e j)) =
      (a * a') * (∑ j, w j ^ 2) + (a * b' + b * a') * (∑ j, w j * e j) +
        (b * b') * (∑ j, e j ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The literal observation matrices have orthonormal rows. -/
theorem starEdgeProjection_mul_transpose (d : ℕ) (hd : 2 ≤ d)
    (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    starEdgeProjection d c i * (starEdgeProjection d c i).transpose = 1 := by
  have hdpos : 0 < d := by omega
  have hlin (a b a' b' : ℝ) :
      (∑ j, (a * starRootDirection d j + b * starSimplexDirection d i j) *
        (a' * starRootDirection d j + b' * starSimplexDirection d i j)) =
        a * a' + b * b' := by
    rw [sum_linearCombination_mul, starRootDirection_norm_sq d hdpos,
      starRootDirection_dot_simplex d hdpos i, starSimplexDirection_norm_sq d hd i]
    ring
  have hs := alpha_sq_add_beta_sq c hc
  ext b b'
  cases b <;> cases b' <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, starEdgeProjection,
      Bool.false_eq_true, ↓reduceIte, Matrix.one_apply, Bool.true_eq_false,
      Bool.false_eq_true, if_true, if_false]
  · have hh := hlin (alpha c) (-beta c) (alpha c) (-beta c)
    simp only [neg_mul, ← sub_eq_add_neg] at hh
    convert hh using 1; nlinarith [hs]
  · have hh := hlin (alpha c) (-beta c) (beta c) (alpha c)
    simp only [neg_mul, ← sub_eq_add_neg] at hh
    convert hh using 1; ring
  · have hh := hlin (beta c) (alpha c) (alpha c) (-beta c)
    simp only [neg_mul, mul_neg, ← sub_eq_add_neg] at hh
    convert hh using 1; ring
  · have hh := hlin (beta c) (alpha c) (beta c) (alpha c)
    convert hh using 1; nlinarith [hs]

lemma starRootDirection_apply {d : ℕ} (x : Fin d → ℝ) :
    (∑ j, starRootDirection d j * x j) = starRootForm x := by
  simp only [starRootDirection, starRootForm, div_eq_mul_inv, one_mul, ← Finset.mul_sum]
  ring

lemma starSimplexDirection_apply {d : ℕ} (x : Fin d → ℝ) (i : Fin d) :
    (∑ j, starSimplexDirection d i j * x j) =
      transverseScale d * starCenteredCoordinate x i := by
  simp_rw [starSimplexDirection_entry]
  calc
    _ = transverseScale d *
        ((∑ j, (if j = i then 1 else 0) * x j) - (1 / (d : ℝ)) * ∑ j, x j) := by
      simp only [mul_sub, sub_mul, Finset.sum_sub_distrib,
        mul_assoc, ← Finset.mul_sum]
    _ = _ := by simp [starCenteredCoordinate, ite_mul, div_eq_mul_inv, mul_comm]

lemma starEdgeProjection_apply_false {d : ℕ} (c : ℝ) (i : Fin d) (x : Fin d → ℝ) :
    (starEdgeProjection d c i).mulVec x false =
      scoreA c (starRootForm x) (transverseScale d * starCenteredCoordinate x i) := by
  simp only [Matrix.mulVec, dotProduct, starEdgeProjection, Bool.false_eq_true, ↓reduceIte,
    sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum,
    starRootDirection_apply, starSimplexDirection_apply, scoreA, smul_eq_mul]

lemma starEdgeProjection_apply_true {d : ℕ} (c : ℝ) (i : Fin d) (x : Fin d → ℝ) :
    (starEdgeProjection d c i).mulVec x true =
      scoreB c (starRootForm x) (transverseScale d * starCenteredCoordinate x i) := by
  simp only [Matrix.mulVec, dotProduct, starEdgeProjection, ↓reduceIte,
    add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
    starRootDirection_apply, starSimplexDirection_apply, scoreB, smul_eq_mul]

/-- The concrete BS weighted tight frame in the actual white-coordinate
space. In particular this identity can be applied pointwise to a score vector. -/
theorem starEdgeProjection_weighted_energy (d : ℕ) (hd : 2 ≤ d)
    (c : ℝ) (hc : |c| < 1) (x : Fin d → ℝ) :
    (∑ i, (weightA d c * ((starEdgeProjection d c i).mulVec x false) ^ 2 +
      weightB d c * ((starEdgeProjection d c i).mulVec x true) ^ 2)) = squareRadius x := by
  have hdpos : 0 < d := by omega
  have he := scalar_frame_energy d hd c hc (starRootForm x)
    (starCenteredCoordinate x) (sum_starCenteredCoordinate hdpos x)
  simp only [Real.norm_eq_abs, sq_abs, smul_eq_mul] at he
  simp_rw [starEdgeProjection_apply_false, starEdgeProjection_apply_true]
  exact he.trans (starRoot_centered_energy hdpos x)

end GaussianWave.BS
