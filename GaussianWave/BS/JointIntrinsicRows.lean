import GaussianWave.BS.BallIntrinsicRelativeEntropy
import GaussianWave.BS.ColoredPhysicalStarMap
import GaussianWave.BS.Lower.IntrinsicEntropyTransfer
import GaussianWave.BS.Lower.FinitePaletteTransport

/-! Actual whole-channel orthonormal intrinsic charts in the site-first
coordinates of the finite-recoloring entropy theorem. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

theorem coordinateRestrictionMatrix_transpose_equiv {I J : Type*} [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) : (coordinateRestrictionMatrix e).transpose = coordinateRestrictionMatrix e.symm := by
  ext j i
  simp only [coordinateRestrictionMatrix, Matrix.transpose_apply]
  congr 1
  exact propext ⟨fun h => by simpa only [h, e.symm_apply_apply],
    fun h => by simpa only [h, e.apply_symm_apply]⟩

def siteFirstIntrinsicRows {I V : Type*} [Fintype V] [DecidableEq V] (r : ℕ) (O : Matrix I V ℝ) :
    Matrix (Fin r × I) (V × Fin r) ℝ :=
  channelLiftMatrix r O * coordinateRestrictionMatrix (Equiv.prodComm (Fin r) V)

theorem siteFirstIntrinsicRows_orthonormal {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq I] [DecidableEq V] (r : ℕ) (O : Matrix I V ℝ) (hO : O * O.transpose = 1) :
    siteFirstIntrinsicRows r O * (siteFirstIntrinsicRows r O).transpose = 1 := by
  let P := coordinateRestrictionMatrix (Equiv.prodComm (Fin r) V)
  have hP : P * P.transpose = 1 := coordinateRestrictionMatrix_orthonormal _ (Equiv.prodComm _ _).injective
  unfold siteFirstIntrinsicRows
  rw [Matrix.transpose_mul]
  calc
    _ = channelLiftMatrix r O * (P * P.transpose) * (channelLiftMatrix r O).transpose := by
      simp only [Matrix.mul_assoc, P]
    _ = 1 := by rw [hP, Matrix.mul_one, channelLiftMatrix_transpose,
      channelLiftMatrix_mul, hO, channelLiftMatrix_one]

theorem siteFirstIntrinsicRows_mulVec {I V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (O : Matrix I V ℝ) (x : (V × Fin r) → ℝ) (c : Fin r) (i : I) :
    (siteFirstIntrinsicRows r O).mulVec x (c, i) = O.mulVec (fun v => x (v, c)) i := by
  rw [siteFirstIntrinsicRows, ← Matrix.mulVec_mulVec, coordinateRestrictionMatrix_mulVec,
    channelLiftMatrix_mulVec]
  rfl

theorem siteFirstIntrinsicRows_support {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq I] [DecidableEq V] (r : ℕ) (O : Matrix I V ℝ)
    (x : (V × Fin r) → ℝ)
    (hx : ∀ c, O.transpose.mulVec (O.mulVec (fun v => x (v, c))) = fun v => x (v, c)) :
    (siteFirstIntrinsicRows r O).transpose.mulVec ((siteFirstIntrinsicRows r O).mulVec x) = x := by
  let P := coordinateRestrictionMatrix (Equiv.prodComm (Fin r) V)
  have hPtP : P.transpose * P = 1 := by
    dsimp only [P]
    rw [coordinateRestrictionMatrix_transpose_equiv]
    have h := coordinateRestrictionMatrix_orthonormal
      (Equiv.prodComm V (Fin r)) (Equiv.prodComm _ _).injective
    rw [coordinateRestrictionMatrix_transpose_equiv] at h
    exact h
  have hL : (channelLiftMatrix r O).transpose.mulVec
      ((channelLiftMatrix r O).mulVec (P.mulVec x)) = P.mulVec x := by
    ext ⟨c, v⟩
    rw [channelLiftMatrix_transpose, channelLiftMatrix_mulVec]
    simp_rw [channelLiftMatrix_mulVec]
    rw [coordinateRestrictionMatrix_mulVec]
    exact congrFun (hx c) v
  unfold siteFirstIntrinsicRows
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change P.transpose.mulVec ((channelLiftMatrix r O).transpose.mulVec
    ((channelLiftMatrix r O).mulVec (P.mulVec x))) = x
  rw [hL, Matrix.mulVec_mulVec, hPtP, Matrix.one_mulVec]

theorem siteFirstIntrinsicRows_siteFirst {I V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (O : Matrix I V ℝ) (x : (Fin r × V) → ℝ) :
    (siteFirstIntrinsicRows r O).mulVec (Lower.siteFirstCoordinates r x) =
      fun ci => O.mulVec (fun v => x (ci.1, v)) ci.2 := by
  funext ⟨c, i⟩
  exact siteFirstIntrinsicRows_mulVec r O _ c i

end GaussianWave.BS
