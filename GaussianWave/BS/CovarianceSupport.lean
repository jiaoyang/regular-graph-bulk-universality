import Mathlib

/-!
# A full-column factorization on the actual support of a PSD covariance

The support coordinates are precisely the nonzero Hermitian eigenspaces.
The resulting rectangular factor has a proved left inverse, and its number
of columns is exactly the matrix rank. No probabilistic or Gaussian premise
is used. In particular the zero matrix has an empty support coordinate set.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Actual nonzero spectral directions of a positive semidefinite matrix. -/
def CovarianceSupportIndex (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :=
  {i : κ // hC.1.eigenvalues i ≠ 0}

instance covarianceSupportIndex_fintype (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :
    Fintype (CovarianceSupportIndex C hC) := by
  classical
  exact inferInstanceAs (Fintype {i : κ // hC.1.eigenvalues i ≠ 0})

instance covarianceSupportIndex_decidableEq (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :
    DecidableEq (CovarianceSupportIndex C hC) := Classical.decEq _

lemma covarianceSupportIndex_card (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :
    Fintype.card (CovarianceSupportIndex C hC) = C.rank :=
  hC.1.rank_eq_card_non_zero_eigs.symm

lemma covarianceSupport_eigenvalue_pos (C : Matrix κ κ ℝ) (hC : C.PosSemidef)
    (j : CovarianceSupportIndex C hC) : 0 < hC.1.eigenvalues j.val :=
  lt_of_le_of_ne (hC.eigenvalues_nonneg j.val) (Ne.symm j.property)

/-- Spectral factor restricted to the actual covariance support. -/
def covarianceSupportL (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :
    Matrix κ (CovarianceSupportIndex C hC) ℝ :=
  fun a j => hC.1.eigenvectorUnitary a j.val * Real.sqrt (hC.1.eigenvalues j.val)

/-- Genuine left inverse; division is only by positive spectral square roots. -/
def covarianceSupportB (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :
    Matrix (CovarianceSupportIndex C hC) κ ℝ :=
  fun j a => (Real.sqrt (hC.1.eigenvalues j.val))⁻¹ * hC.1.eigenvectorUnitary a j.val

private lemma covariance_spectral_entry (C : Matrix κ κ ℝ) (hC : C.PosSemidef) (a b : κ) :
    C a b = ∑ i, hC.1.eigenvectorUnitary a i * hC.1.eigenvalues i *
      hC.1.eigenvectorUnitary b i := by
  have h := congrArg (fun M : Matrix κ κ ℝ => M a b) hC.1.spectral_theorem
  simpa [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply] using h

private lemma covariance_eigenvector_columns (C : Matrix κ κ ℝ) (hC : C.PosSemidef) (i j : κ) :
    (∑ a, hC.1.eigenvectorUnitary a i * hC.1.eigenvectorUnitary a j) =
      if i = j then 1 else 0 := by
  have hu : (hC.1.eigenvectorUnitary : Matrix κ κ ℝ).transpose *
      (hC.1.eigenvectorUnitary : Matrix κ κ ℝ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      unitary.coe_star_mul_self hC.1.eigenvectorUnitary
  have h := congrArg (fun M : Matrix κ κ ℝ => M i j) hu
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

/-- The actual support factor reproduces the entire covariance matrix,
including singular and zero covariances. -/
theorem covarianceSupportL_mul_transpose (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :
    covarianceSupportL C hC * (covarianceSupportL C hC).transpose = C := by
  classical
  ext a b
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (fun i : κ => hC.1.eigenvalues i ≠ 0)
    (fun i => hC.1.eigenvectorUnitary a i * hC.1.eigenvalues i * hC.1.eigenvectorUnitary b i)
  have hz : (∑ i : {i : κ // ¬hC.1.eigenvalues i ≠ 0},
      hC.1.eigenvectorUnitary a i.val * hC.1.eigenvalues i.val *
        hC.1.eigenvectorUnitary b i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : hC.1.eigenvalues i.val = 0 := not_ne_iff.mp i.property
    rw [hi, mul_zero, zero_mul]
  rw [hz, add_zero] at hsum
  rw [covariance_spectral_entry C hC a b, ← hsum]
  change (∑ j : CovarianceSupportIndex C hC,
    (hC.1.eigenvectorUnitary a j.val * Real.sqrt (hC.1.eigenvalues j.val)) *
      (hC.1.eigenvectorUnitary b j.val * Real.sqrt (hC.1.eigenvalues j.val))) = _
  apply Finset.sum_congr rfl
  intro j _
  have hs := Real.sq_sqrt (hC.eigenvalues_nonneg j.val)
  linear_combination (hC.1.eigenvectorUnitary a j.val * hC.1.eigenvectorUnitary b j.val) * hs

/-- The support factor has a genuine matrix left inverse. -/
theorem covarianceSupportB_mul_L (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :
    covarianceSupportB C hC * covarianceSupportL C hC = 1 := by
  classical
  ext i j
  have hsi : Real.sqrt (hC.1.eigenvalues i.val) ≠ 0 :=
    (Real.sqrt_pos.mpr (covarianceSupport_eigenvalue_pos C hC i)).ne'
  have heq : (∑ a, ((Real.sqrt (hC.1.eigenvalues i.val))⁻¹ * hC.1.eigenvectorUnitary a i.val) *
      (hC.1.eigenvectorUnitary a j.val * Real.sqrt (hC.1.eigenvalues j.val))) =
      ((Real.sqrt (hC.1.eigenvalues i.val))⁻¹ * Real.sqrt (hC.1.eigenvalues j.val)) *
        (∑ a, hC.1.eigenvectorUnitary a i.val * hC.1.eigenvectorUnitary a j.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  change (∑ a, ((Real.sqrt (hC.1.eigenvalues i.val))⁻¹ * hC.1.eigenvectorUnitary a i.val) *
      (hC.1.eigenvectorUnitary a j.val * Real.sqrt (hC.1.eigenvalues j.val))) = _
  rw [heq, covariance_eigenvector_columns C hC i.val j.val]
  by_cases hij : i = j
  · subst j
    simp [hsi]
  · have hvals : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    simp [hij, hvals, Matrix.one_apply]

/-- The finite support index is canonically reindexed to exactly rank C
coordinates for use with finite channel vectors. -/
def covarianceSupportEquiv (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :
    Fin C.rank ≃ CovarianceSupportIndex C hC :=
  (Fintype.equivFinOfCardEq (covarianceSupportIndex_card C hC)).symm

def covarianceRankL (C : Matrix κ κ ℝ) (hC : C.PosSemidef) : Matrix κ (Fin C.rank) ℝ :=
  fun a j => covarianceSupportL C hC a (covarianceSupportEquiv C hC j)

def covarianceRankB (C : Matrix κ κ ℝ) (hC : C.PosSemidef) : Matrix (Fin C.rank) κ ℝ :=
  fun j a => covarianceSupportB C hC (covarianceSupportEquiv C hC j) a

theorem covarianceRankL_mul_transpose (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :
    covarianceRankL C hC * (covarianceRankL C hC).transpose = C := by
  ext a b
  change (∑ j : Fin C.rank, covarianceSupportL C hC a (covarianceSupportEquiv C hC j) *
    covarianceSupportL C hC b (covarianceSupportEquiv C hC j)) = C a b
  calc
    _ = ∑ j : CovarianceSupportIndex C hC, covarianceSupportL C hC a j *
        covarianceSupportL C hC b j :=
      Equiv.sum_comp (covarianceSupportEquiv C hC) (fun j => covarianceSupportL C hC a j * covarianceSupportL C hC b j)
    _ = _ := congrArg (fun M : Matrix κ κ ℝ => M a b) (covarianceSupportL_mul_transpose C hC)

theorem covarianceRankB_mul_L (C : Matrix κ κ ℝ) (hC : C.PosSemidef) :
    covarianceRankB C hC * covarianceRankL C hC = 1 := by
  ext i j
  have h := congrArg (fun M : Matrix (CovarianceSupportIndex C hC) (CovarianceSupportIndex C hC) ℝ =>
    M (covarianceSupportEquiv C hC i) (covarianceSupportEquiv C hC j)) (covarianceSupportB_mul_L C hC)
  simpa only [Matrix.mul_apply, covarianceRankB, covarianceRankL, Matrix.one_apply,
    (covarianceSupportEquiv C hC).injective.eq_iff] using h

/-- Full-column support factorization with exactly rank C columns. -/
structure CovarianceSupportFactor (C : Matrix κ κ ℝ) where
  L : Matrix κ (Fin C.rank) ℝ
  B : Matrix (Fin C.rank) κ ℝ
  covariance_eq : C = L * L.transpose
  left_inverse : B * L = 1

/-- Every actual real PSD covariance has the proved support factorization. -/
def covarianceSupportFactor (C : Matrix κ κ ℝ) (hC : C.PosSemidef) : CovarianceSupportFactor C where
  L := covarianceRankL C hC
  B := covarianceRankB C hC
  covariance_eq := (covarianceRankL_mul_transpose C hC).symm
  left_inverse := covarianceRankB_mul_L C hC

theorem covarianceSupportIndex_card_zero_of_eq_zero (C : Matrix κ κ ℝ) (hC : C.PosSemidef)
    (hzero : C = 0) : Fintype.card (CovarianceSupportIndex C hC) = 0 := by
  rw [covarianceSupportIndex_card, hzero, Matrix.rank_zero]

end GaussianWave.BS
