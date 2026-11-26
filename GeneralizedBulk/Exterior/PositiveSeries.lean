import GeneralizedBulk.Exterior.Positivity

/-!
# Positive imaginary parts from convergent marked series

A convergent sum of positive semidefinite matrices is positive semidefinite.
A strictly positive finite prefix therefore gives strict positivity of the
whole series. Gaussian probability enters only in proving the prefix spans.
-/
noncomputable section
open scoped BigOperators Topology ComplexOrder
open Filter
namespace GeneralizedBulk.Exterior

/-- Positive semidefiniteness is closed under limits along any nontrivial
filter, including the finite-subset net defining an unordered series. -/
theorem posSemidef_of_tendsto_filter {I : Type*} {l : Filter I} [NeBot l]
    {A : I → Mat} {B : Mat}
    (hA : ∀ᶠ i in l, (A i).PosSemidef) (hB : Tendsto A l (𝓝 B)) : B.PosSemidef := by
  constructor
  · have hc : Tendsto (fun i => (A i).conjTranspose) l (𝓝 B.conjTranspose) :=
      continuous_id.matrix_conjTranspose.continuousAt.tendsto.comp hB
    have heq : (fun i => (A i).conjTranspose) =ᶠ[l] A := hA.mono (fun _ hi => hi.isHermitian.eq)
    exact tendsto_nhds_unique (hc.congr' heq) hB
  · intro x
    have hc : Continuous (fun M : Mat => dotProduct (star x) (M.mulVec x)) :=
      continuous_const.matrix_dotProduct (continuous_id.matrix_mulVec continuous_const)
    have hl : Tendsto (fun i => dotProduct (star x) ((A i).mulVec x)) l
        (𝓝 (dotProduct (star x) (B.mulVec x))) := hc.continuousAt.tendsto.comp hB
    exact (isClosed_Ici : IsClosed (Set.Ici (0 : ℂ))).mem_of_tendsto hl (hA.mono (fun _ hi => hi.2 x))

/-- Positive semidefiniteness is preserved by matrix limits. -/
theorem posSemidef_of_tendsto {A : ℕ → Mat} {B : Mat}
    (hA : ∀ n, (A n).PosSemidef) (hB : Tendsto A atTop (𝓝 B)) : B.PosSemidef := by
  constructor
  · have hconj : Tendsto (fun n => (A n).conjTranspose) atTop (𝓝 B.conjTranspose) :=
      continuous_id.matrix_conjTranspose.continuousAt.tendsto.comp hB
    have heq : (fun n => (A n).conjTranspose) = A := by
      funext n
      exact (hA n).isHermitian.eq
    rw [heq] at hconj
    exact tendsto_nhds_unique hconj hB
  · intro x
    have hc : Continuous (fun M : Mat => dotProduct (star x) (M.mulVec x)) :=
      continuous_const.matrix_dotProduct (continuous_id.matrix_mulVec continuous_const)
    have hlim : Tendsto (fun n : ℕ => dotProduct (star x) ((A n).mulVec x)) atTop
        (𝓝 (dotProduct (star x) (B.mulVec x))) := hc.continuousAt.tendsto.comp hB
    exact (isClosed_Ici : IsClosed (Set.Ici (0 : ℂ))).mem_of_tendsto hlim
      (Eventually.of_forall (fun n => (hA n).2 x))

theorem posSemidef_finset_sum {ι : Type*} (s : Finset ι) (A : ι → Mat)
    (hA : ∀ i ∈ s, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero : (0 : Mat).PosSemidef)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hA a (by simp)).add (ih (fun i hi => hA i (by simp [hi])))

theorem posSemidef_tsum {I : Type*} (A : I → Mat) (hA : ∀ i, (A i).PosSemidef)
    (hs : Summable A) : (∑' i, A i).PosSemidef := by
  exact posSemidef_of_tendsto_filter
    (Eventually.of_forall (fun s : Finset I => posSemidef_finset_sum s A (fun i _ => hA i))) hs.hasSum

/-- A positive finite block dominates the positive tail of a summable series. -/
theorem posDef_tsum_of_prefix (A : ℕ → Mat) (hA : ∀ n, (A n).PosSemidef)
    (hs : Summable A) (N : ℕ) (hp : (∑ n ∈ Finset.range N, A n).PosDef) :
    (∑' n, A n).PosDef := by
  have htail : Summable (fun n => A (n + N)) := (summable_nat_add_iff N).2 hs
  have ht := posSemidef_tsum (fun n => A (n + N)) (fun n => hA (n + N)) htail
  have hsum : (∑ n ∈ Finset.range N, A n) + (∑' n, A (n + N)) = ∑' n, A n :=
    hs.sum_add_tsum_nat_add N
  rw [← hsum]
  exact hp.add_posSemidef ht

/-- Any strictly positive finite subcollection dominates the positive tail.
This version works for the intrinsic particle-occurrence label type. -/
theorem posDef_tsum_of_finset {I : Type*} (A : I → Mat) (hA : ∀ i, (A i).PosSemidef)
    (hs : Summable A) (s : Finset I) (hp : (∑ i ∈ s, A i).PosDef) :
    (∑' i, A i).PosDef := by
  classical
  have ht := posSemidef_tsum (fun i : {i // i ∉ s} => A i) (fun i => hA i) (hs.subtype _)
  have heq := hs.sum_add_tsum_subtype_compl s
  rw [← heq]
  exact hp.add_posSemidef ht

/-- A weighted four-mark block is strictly positive when its mark matrix is
invertible and every scalar coefficient is positive. -/
theorem positive_weighted_gram (Y : Mat) (hY : IsUnit Y)
    (weight : Fin 4 → ℝ) (hw : ∀ i, 0 < weight i) :
    (Y * Matrix.diagonal (fun i => (weight i : ℂ)) * Y.conjTranspose).PosDef := by
  have hd : (Matrix.diagonal (fun i => (weight i : ℂ))).PosDef :=
    Matrix.PosDef.diagonal (fun i => Complex.zero_lt_real.mpr (hw i))
  apply hd.mul_mul_conjTranspose_same
  exact Matrix.vecMul_injective_iff_isUnit.mpr hY

/-- Rank-one positive matrix of one complex endpoint vector. -/
def outerMatrix (y : Fin 4 → ℂ) : Mat := fun i j => y i * star (y j)

/-- A nonnegative weighted rank-one matrix is positive semidefinite. -/
theorem weighted_outer_posSemidef (y : Fin 4 → ℂ) (a : ℝ) (ha : 0 ≤ a) :
    ((a : ℂ) • outerMatrix y).PosSemidef := by
  let B : Matrix (Fin 4) (Fin 1) ℂ := fun i _ => y i
  have hd : (Matrix.diagonal (fun _ : Fin 1 => (a : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun _ => Complex.zero_le_real.mpr ha)
  have h := hd.mul_mul_conjTranspose_same B
  convert h using 1
  ext i j
  simp [B, outerMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal,
    Fin.sum_univ_one, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The weighted Gram block is exactly the sum of the four rank-one marks. -/
theorem weighted_gram_eq_sum (Y : Mat) (a : Fin 4 → ℂ) :
    Y * Matrix.diagonal a * Y.conjTranspose =
      ∑ k : Fin 4, a k • outerMatrix (fun i => Y i k) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, outerMatrix, smul_eq_mul]
  change (∑ k, (Y * Matrix.diagonal a) i k * star (Y j k)) =
    ∑ k, a k * (Y i k * star (Y j k))
  simp_rw [Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro k _
  ring

end GeneralizedBulk.Exterior
