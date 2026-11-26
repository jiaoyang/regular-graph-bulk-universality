import GaussianWave.BS.GaussianExceptionalEnergy

/-!
# Quadratic forms determine the actual Gaussian factor Gram matrix
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

theorem finiteCovarianceQuadratic_single {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (i : I) : finiteCovarianceQuadratic C (Pi.single i 1) = C i i := by
  simp [finiteCovarianceQuadratic, Pi.single_apply]

theorem finiteCovarianceQuadratic_single_add {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (i j : I) :
    finiteCovarianceQuadratic C (Pi.single i 1 + Pi.single j 1) = C i i + C i j + C j i + C j j := by
  simp only [finiteCovarianceQuadratic, Pi.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib, Pi.single_apply, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem matrix_eq_of_quadratic {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℝ) (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i)
    (h : ∀ z, finiteCovarianceQuadratic A z = finiteCovarianceQuadratic B z) : A = B := by
  have hd (i : I) : A i i = B i i := by
    simpa only [finiteCovarianceQuadratic_single] using h (Pi.single i 1)
  ext i j
  have hij := h (Pi.single i 1 + Pi.single j 1)
  rw [finiteCovarianceQuadratic_single_add, finiteCovarianceQuadratic_single_add,
    hd, hd, hA j i, hB j i] at hij
  linarith

theorem finiteCovarianceQuadratic_column_gram {I V : Type*} [Fintype I] [Fintype V]
    (M : Matrix V I ℝ) (z : I → ℝ) :
    finiteCovarianceQuadratic (M.transpose * M) z = ∑ v, M.mulVec z v ^ 2 := by
  simpa only [Matrix.transpose_transpose, Matrix.vecMul_transpose] using
    finiteCovarianceQuadratic_gram M.transpose z

theorem finiteCovarianceQuadratic_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    (w z : I → ℝ) : finiteCovarianceQuadratic (Matrix.diagonal w) z = ∑ i, w i * z i ^ 2 := by
  simp only [finiteCovarianceQuadratic, Matrix.diagonal_apply, mul_ite, ite_mul,
    mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finiteCovarianceQuadratic_blocks_diagonal {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (R : Matrix I I ℝ) (w : J → ℝ) (z : I ⊕ J → ℝ) :
    finiteCovarianceQuadratic (Matrix.fromBlocks R 0 0 (Matrix.diagonal w)) z =
      finiteCovarianceQuadratic R (fun i => z (Sum.inl i)) + ∑ j, w j * z (Sum.inr j) ^ 2 := by
  simp only [finiteCovarianceQuadratic, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.diagonal_apply, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

def vertexRootGram (m k : ℕ) (energy : ℝ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  fun i j => (if i = j then vertexContrastGain m k energy else 0) +
    (vertexRadialGain m k energy - vertexContrastGain m k energy) / (m + 2)

def edgeRootGram (m k : ℕ) (energy : ℝ) : Matrix Bool Bool ℝ :=
  fun a b => if a = b then edgeDiagonalGain m k energy else edgeOffDiagonalGain m k energy

def vertexFactorGram (m k : ℕ) (energy : ℝ) :
    Matrix (VertexBallInnovation (m + 2) k) (VertexBallInnovation (m + 2) k) ℝ :=
  Matrix.fromBlocks (vertexRootGram m k energy) 0 0
    (Matrix.diagonal (fun aj : Fin (m + 2) × BranchInnovation (m + 1) k => branchNoiseWeight m energy k aj.2))

def edgeFactorGram (m k : ℕ) (energy : ℝ) :
    Matrix (EdgeBallInnovation (m + 2) k) (EdgeBallInnovation (m + 2) k) ℝ :=
  Matrix.fromBlocks (edgeRootGram m k energy) 0 0
    (Matrix.diagonal (fun bj : Bool × BranchInnovation (m + 1) k => branchNoiseWeight m energy k bj.2))

theorem vertexRootGram_quadratic (m k : ℕ) (energy : ℝ) (z : Fin (m + 2) → ℝ) :
    finiteCovarianceQuadratic (vertexRootGram m k energy) z =
      vertexRadialGain m k energy * starRootForm z ^ 2 +
        vertexContrastGain m k energy * ∑ i, starCenteredCoordinate z i ^ 2 := by
  have henergy := starRoot_centered_energy (by omega : 0 < m + 2) z
  have hroot : starRootForm z ^ 2 = (∑ i, z i) ^ 2 / (m + 2 : ℝ) := by
    unfold starRootForm
    rw [div_pow, Real.sq_sqrt (by positivity)]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
  have he (i j : Fin (m + 2)) : z i * vertexRootGram m k energy i j * z j =
      (if i = j then vertexContrastGain m k energy * z i ^ 2 else 0) +
        ((vertexRadialGain m k energy - vertexContrastGain m k energy) / (m + 2)) * z i * z j := by
    unfold vertexRootGram
    split_ifs with hij
    · subst j; ring
    · ring
  unfold finiteCovarianceQuadratic
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hroot] at henergy ⊢
  unfold squareRadius at henergy
  have hd : (m : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hd] at henergy ⊢
  linear_combination -(vertexContrastGain m k energy) * henergy

theorem edgeRootGram_quadratic (m k : ℕ) (energy : ℝ) (z : Bool → ℝ) :
    finiteCovarianceQuadratic (edgeRootGram m k energy) z =
      edgeDiagonalGain m k energy * (z false ^ 2 + z true ^ 2) +
        2 * edgeOffDiagonalGain m k energy * z false * z true := by
  simp only [finiteCovarianceQuadratic, Fintype.sum_bool, edgeRootGram, if_true,
    Bool.false_eq_true, Bool.true_eq_false, if_false]
  ring

def vertexOrthoFactorMatrix (m k : ℕ) (energy : ℝ) :
    Matrix (VertexBallVertex (m + 2) k) (VertexBallInnovation (m + 2) k) ℝ :=
  LinearMap.toMatrix' (vertexOrthoGaussianMap m k energy)

def edgeOrthoFactorMatrix (m k : ℕ) (energy : ℝ) :
    Matrix (EdgeBallVertex (m + 2) k) (EdgeBallInnovation (m + 2) k) ℝ :=
  LinearMap.toMatrix' (edgeOrthoGaussianMap m k energy)

theorem gram_entries_symmetric {I V : Type*} [Fintype V] (M : Matrix V I ℝ) (i j : I) :
    (M.transpose * M) i j = (M.transpose * M) j i := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem vertexFactorGram_symmetric (m k : ℕ) (energy : ℝ)
    (i j : VertexBallInnovation (m + 2) k) : vertexFactorGram m k energy i j = vertexFactorGram m k energy j i := by
  cases i with
  | inl a =>
      cases j with
      | inl b => simp [vertexFactorGram, vertexRootGram, eq_comm]
      | inr bj => rfl
  | inr ai =>
      cases j with
      | inl b => rfl
      | inr bj =>
          by_cases h : ai = bj
          · subst bj; rfl
          · simp [vertexFactorGram, Matrix.diagonal_apply, h, Ne.symm h]

theorem edgeFactorGram_symmetric (m k : ℕ) (energy : ℝ)
    (i j : EdgeBallInnovation (m + 2) k) : edgeFactorGram m k energy i j = edgeFactorGram m k energy j i := by
  cases i with
  | inl a =>
      cases j with
      | inl b => simp [edgeFactorGram, edgeRootGram, eq_comm]
      | inr bj => rfl
  | inr ai =>
      cases j with
      | inl b => rfl
      | inr bj =>
          by_cases h : ai = bj
          · subst bj; rfl
          · simp [edgeFactorGram, Matrix.diagonal_apply, h, Ne.symm h]

theorem vertexOrthoFactorMatrix_column_gram (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    (vertexOrthoFactorMatrix m k energy).transpose * vertexOrthoFactorMatrix m k energy =
      vertexFactorGram m k energy := by
  apply matrix_eq_of_quadratic _ _ (gram_entries_symmetric _) (vertexFactorGram_symmetric m k energy)
  intro z
  rw [finiteCovarianceQuadratic_column_gram]
  simp_rw [show (vertexOrthoFactorMatrix m k energy).mulVec z = vertexOrthoGaussianMap m k energy z from
    toMatrix_mulVec_apply _ z]
  rw [vertexOrthoGaussianMap_energy m k energy he]
  unfold vertexFactorGram
  rw [finiteCovarianceQuadratic_blocks_diagonal, vertexRootGram_quadratic]
  simp only [Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact branchOrthoNoiseEnergy_eq_weighted_sum m k energy _

theorem edgeOrthoFactorMatrix_column_gram (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    (edgeOrthoFactorMatrix m k energy).transpose * edgeOrthoFactorMatrix m k energy =
      edgeFactorGram m k energy := by
  apply matrix_eq_of_quadratic _ _ (gram_entries_symmetric _) (edgeFactorGram_symmetric m k energy)
  intro z
  rw [finiteCovarianceQuadratic_column_gram]
  simp_rw [show (edgeOrthoFactorMatrix m k energy).mulVec z = edgeOrthoGaussianMap m k energy z from
    toMatrix_mulVec_apply _ z]
  rw [edgeOrthoGaussianMap_energy m k energy he]
  unfold edgeFactorGram
  rw [finiteCovarianceQuadratic_blocks_diagonal, edgeRootGram_quadratic]
  simp only [Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact branchOrthoNoiseEnergy_eq_weighted_sum m k energy _

theorem vertexFactorGram_det (m k : ℕ) (energy : ℝ) :
    (vertexFactorGram m k energy).det = (vertexRootGram m k energy).det *
      branchNoiseDeterminant m k energy ^ (m + 2) := by
  unfold vertexFactorGram
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]
  simp only [Fintype.prod_prod_type, branchNoiseDeterminant, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rfl

theorem edgeFactorGram_det (m k : ℕ) (energy : ℝ) :
    (edgeFactorGram m k energy).det = (edgeRootGram m k energy).det *
      branchNoiseDeterminant m k energy ^ 2 := by
  unfold edgeFactorGram
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]
  simp only [Fintype.prod_prod_type, branchNoiseDeterminant, Finset.prod_const,
    Finset.card_univ, Fintype.card_bool]
  rfl

theorem edgeRootGram_det (m k : ℕ) (energy : ℝ) :
    (edgeRootGram m k energy).det = edgePlusGain m k energy * edgeMinusGain m k energy := by
  rw [← Matrix.det_reindex_self finTwoEquiv.symm (edgeRootGram m k energy), Matrix.det_fin_two]
  norm_num [Matrix.reindex, Matrix.submatrix, edgeRootGram, finTwoEquiv]
  rw [← edgeDiagonalGain_add_offDiagonalGain, ← edgeDiagonalGain_sub_offDiagonalGain]
  ring

theorem vertexContrastGain_pos (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    0 < vertexContrastGain m k energy := by
  apply mul_pos
  · exact siblingVariance_pos (m + 2) (by omega) energy (by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using he)
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (branchEnergy_root_coefficient_ge_one m k energy he)

theorem vertexRootGram_det (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    (vertexRootGram m k energy).det =
      vertexRadialGain m k energy * vertexContrastGain m k energy ^ (m + 1) := by
  let s1 := vertexRadialGain m k energy
  let s2 := vertexContrastGain m k energy
  have hs2 : s2 ≠ 0 := (vertexContrastGain_pos m k energy he).ne'
  have hd : (m : ℝ) + 2 ≠ 0 := by positivity
  let u : Fin (m + 2) → ℝ := fun _ => (s1 - s2) / ((m + 2) * s2)
  let v : Fin (m + 2) → ℝ := fun _ => 1
  have hmat : vertexRootGram m k energy =
      s2 • (1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit v) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Fintype.sum_unique]
    change (if i = j then s2 else 0) + (s1 - s2) / (m + 2) =
      s2 * ((if i = j then 1 else 0) + (s1 - s2) / ((m + 2) * s2) * 1)
    split_ifs <;> field_simp [hd, hs2] <;> ring
  rw [hmat, Matrix.det_smul, Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit)]
  simp only [Fintype.card_fin, dotProduct, u, v, one_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
  change s2 ^ (m + 2) * (1 + (m + 2 : ℝ) * ((s1 - s2) / ((m + 2) * s2))) = s1 * s2 ^ (m + 1)
  rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
  field_simp [hd, hs2]
  ring

theorem vertexOrthoFactorMatrix_gram_det (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    ((vertexOrthoFactorMatrix m k energy).transpose * vertexOrthoFactorMatrix m k energy).det =
      vertexRadialGain m k energy * vertexContrastGain m k energy ^ (m + 1) *
        branchNoiseDeterminant m k energy ^ (m + 2) := by
  rw [vertexOrthoFactorMatrix_column_gram m k energy he, vertexFactorGram_det,
    vertexRootGram_det m k energy he]

theorem edgeOrthoFactorMatrix_gram_det (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    ((edgeOrthoFactorMatrix m k energy).transpose * edgeOrthoFactorMatrix m k energy).det =
      edgePlusGain m k energy * edgeMinusGain m k energy * branchNoiseDeterminant m k energy ^ 2 := by
  rw [edgeOrthoFactorMatrix_column_gram m k energy he, edgeFactorGram_det, edgeRootGram_det]

end GaussianWave.BS
