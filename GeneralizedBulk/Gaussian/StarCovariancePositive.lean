import GeneralizedBulk.Gaussian.StarNormalProjection

/-! Adding the literal unit-normal covariance makes the Gaussian-wave star nonsingular. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Gaussian
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.External.RegularSpectralData GeneralizedBulk.Covariance

theorem norm_starRow_sum_sq (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) (x : Fin (d+1) → ℝ) :
    ‖∑ j, x j • starRow d hd E j‖ ^ 2 = dotProduct x ((starWaveCovariance d E).mulVec x) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right, starRow_gram d hd E hE,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem unitNormalProjection_quadratic {I : Type*} [Fintype I] (n x : I → ℝ) :
    dotProduct x ((unitNormalProjection n).mulVec x) = (∑ i, n i * x i) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, unitNormalProjection, Finset.mul_sum]
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem eq_zero_of_starRow_sum_and_normal_zero (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d)
    (x : Fin (d+1) → ℝ) (hrow : (∑ j, x j • starRow d hd E j) = 0)
    (hnormal : (∑ j, normalizedStarNormal d E j * x j) = 0) : x = 0 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hs : Real.sqrt ((d : ℝ) + E ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
    (add_pos_of_pos_of_nonneg (by exact_mod_cast (by omega : 0 < d)) (sq_nonneg E)))
  have hn : (∑ j, entropyStarNormal E j * x j) = 0 := by
    simp only [normalizedStarNormal, div_mul_eq_mul_div, ← Finset.sum_div] at hnormal
    exact (div_eq_zero_iff.mp hnormal).resolve_right hs
  rw [Fin.sum_univ_succ] at hn
  simp only [entropyStarNormal, Fin.cases_zero, Fin.cases_succ, one_mul] at hn
  let xp : Physical d := (WithLp.equiv 2 _).symm (fun j => Option.casesOn j (x 0) (fun i => x i.succ))
  have hxconstraint : xp ∈ physicalStar d (E / d) := by
    change (∑ i : Fin d, x i.succ) - ((d : ℝ) * (E / d)) * x 0 = 0
    have he : (d : ℝ) * (E / d) = E := by field_simp
    rw [he]
    linarith
  let yp := inverseWhitening d (E / d) (starRho d E) ⟨xp,hxconstraint⟩
  have hcoords (j : Fin (d+1)) : @inner ℝ (WhiteStar d) _ (starRow d hd E j) yp = x j := by
    have hh := starRow_inner_inverseWhitening d hd E hE ⟨xp,hxconstraint⟩ j
    change @inner ℝ (WhiteStar d) _ (starRow d hd E j) yp =
      Fin.cases (x 0) (fun i => x i.succ) j at hh
    exact hh.trans (Fin.cases rfl (fun i => rfl) j)
  have hh := congrArg (fun u : WhiteStar d => @inner ℝ (WhiteStar d) _ u yp) hrow
  simp only [sum_inner, real_inner_smul_left, inner_zero_left, hcoords] at hh
  have hx : ∑ j, x j ^ 2 = 0 := by simpa only [pow_two] using hh
  funext j
  have hj : x j ^ 2 ≤ 0 := by
    rw [← hx]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ j)
  exact sq_eq_zero_iff.mp (le_antisymm hj (sq_nonneg _))

theorem starWave_add_normal_posDef (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    (starWaveCovariance d E + starNormalProjection d E).PosDef := by
  have hsym : (starWaveCovariance d E + starNormalProjection d E).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_add,
      starWaveCovariance_transpose d hd E hE, starNormalProjection_transpose]
  refine ⟨hsym, fun x hx => ?_⟩
  have he : dotProduct (star x) ((starWaveCovariance d E + starNormalProjection d E).mulVec x) =
      ‖∑ j, x j • starRow d hd E j‖ ^ 2 + (∑ j, normalizedStarNormal d E j * x j) ^ 2 := by
    simp only [star_trivial, Matrix.add_mulVec, dotProduct_add, ← norm_starRow_sum_sq d hd E hE x,
      starNormalProjection, unitNormalProjection_quadratic]
  rw [he]
  by_contra h
  have hz : ‖∑ j, x j • starRow d hd E j‖ = 0 := by nlinarith [sq_nonneg (∑ j, normalizedStarNormal d E j * x j)]
  have hn : (∑ j, normalizedStarNormal d E j * x j) = 0 := by nlinarith [sq_nonneg ‖∑ j, x j • starRow d hd E j‖]
  exact hx (eq_zero_of_starRow_sum_and_normal_zero d hd E hE x (norm_eq_zero.mp hz) hn)

end GeneralizedBulk.Gaussian
