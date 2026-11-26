import GaussianWave.BS.StarFrame

/-!
# The common-energy BS frame with finitely many channels

Each edge observation retains both endpoint directions in every channel.
The construction is geometric and imposes no probabilistic independence.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

/-- Block-diagonal lift of the scalar BS edge projection. The ambient index
is channel × star-coordinate; the observed index is endpoint × channel. -/
def coloredStarEdgeProjection (d r : ℕ) (c : ℝ) (i : Fin d) :
    Matrix (Bool × Fin r) (Fin r × Fin d) ℝ :=
  fun p q => if q.1 = p.2 then starEdgeProjection d c i p.1 q.2 else 0

@[simp] theorem coloredStarEdgeProjection_mulVec
    (d r : ℕ) (c : ℝ) (i : Fin d) (x : (Fin r × Fin d) → ℝ) (b : Bool) (a : Fin r) :
    (coloredStarEdgeProjection d r c i).mulVec x (b, a) =
      (starEdgeProjection d c i).mulVec (fun j => x (a, j)) b := by
  simp [coloredStarEdgeProjection, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, ite_mul]

/-- The entire 2r-dimensional edge observation has orthonormal rows. -/
theorem coloredStarEdgeProjection_mul_transpose
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    coloredStarEdgeProjection d r c i * (coloredStarEdgeProjection d r c i).transpose = 1 := by
  ext p q
  rcases p with ⟨b, a⟩
  rcases q with ⟨b', a'⟩
  have h := congrArg (fun M : Matrix Bool Bool ℝ => M b b')
    (starEdgeProjection_mul_transpose d hd c hc i)
  by_cases haa : a = a'
  · subst a'
    simpa [coloredStarEdgeProjection, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_prod_type, Matrix.one_apply, Prod.mk.injEq, ite_mul] using h
  · simp [coloredStarEdgeProjection, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_prod_type, Matrix.one_apply, Prod.mk.injEq, ite_mul, mul_ite,
      haa, Ne.symm haa]

/-- The same scalar weights give the full multichannel tight-frame identity.
All channels may be correlated under an arbitrary input probability law. -/
theorem coloredStarEdgeProjection_weighted_energy
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (x : (Fin r × Fin d) → ℝ) :
    (∑ i, ∑ a,
      (weightA d c * ((coloredStarEdgeProjection d r c i).mulVec x (false, a)) ^ 2 +
        weightB d c * ((coloredStarEdgeProjection d r c i).mulVec x (true, a)) ^ 2)) =
          squareRadius x := by
  simp_rw [coloredStarEdgeProjection_mulVec]
  rw [Finset.sum_comm]
  simp_rw [starEdgeProjection_weighted_energy d hd c hc]
  simp [squareRadius, Fintype.sum_prod_type]

end GaussianWave.BS
