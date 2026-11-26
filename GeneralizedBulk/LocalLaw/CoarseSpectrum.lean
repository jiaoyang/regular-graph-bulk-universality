import GeneralizedBulk.LocalLaw.SourceScaling
import SpectralConsequences.SortedHermitianSpectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots

noncomputable section
open scoped Classical BigOperators
open Matrix Polynomial

namespace GeneralizedBulk.LocalLawBridge

private theorem diagonalization_charpoly {m : ℕ}
    (H U V : Matrix (Fin m) (Fin m) ℂ) (f : Fin m → ℂ)
    (huv : U * V = 1) (hH : H = U * Matrix.diagonal f * V) :
    H.charpoly = ∏ i, (Polynomial.X - Polynomial.C (f i)) := by
  let P := U.map Polynomial.C
  let Q := V.map Polynomial.C
  have hpq : P * Q = 1 := by
    rw [← Matrix.map_mul, huv]
    simp [P, Q]
  have hc : H.charmatrix = P * (Matrix.diagonal (fun i => Polynomial.X - Polynomial.C (f i))) * Q := by
    have hdiag : Matrix.diagonal (fun i => Polynomial.X - Polynomial.C (f i)) =
        (Polynomial.X : ℂ[X]) • (1 : Matrix (Fin m) (Fin m) ℂ[X]) - (Matrix.diagonal f).map Polynomial.C := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
    rw [hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hpq]
    have hm : P * (Matrix.diagonal f).map Polynomial.C * Q = H.map Polynomial.C := by
      simp only [P, Q, ← Matrix.map_mul, hH]
    rw [hm]
    change Matrix.scalar (Fin m) (Polynomial.X : ℂ[X]) - H.map Polynomial.C = _
    rw [show Matrix.scalar (Fin m) (Polynomial.X : ℂ[X]) =
      (Polynomial.X : ℂ[X]) • (1 : Matrix (Fin m) (Fin m) ℂ[X]) from by
        apply Matrix.ext
        intro i j
        by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.one_apply, h]]
  rw [Matrix.charpoly, hc, Matrix.det_mul, Matrix.det_mul]
  have hdet : P.det * Q.det = 1 := by simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hpq
  rw [mul_right_comm, hdet, one_mul, Matrix.det_diagonal]

private theorem roots_diagonalization {m : ℕ}
    (H U V : Matrix (Fin m) (Fin m) ℂ) (f : Fin m → ℂ)
    (huv : U * V = 1) (hH : H = U * Matrix.diagonal f * V) :
    H.charpoly.roots = ((List.ofFn f : List ℂ) : Multiset ℂ) := by
  rw [diagonalization_charpoly H U V f huv hH]
  have hp : (∏ i : Fin m, (Polynomial.X - Polynomial.C (f i))) =
      (((List.ofFn f : List ℂ) : Multiset ℂ).map (fun x => Polynomial.X - Polynomial.C x)).prod := by
    simp only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn, Function.comp_def]
  rw [hp, Polynomial.roots_multiset_prod_X_sub_C]

end GeneralizedBulk.LocalLawBridge

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.LocalLawBridge SpectralConsequences
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem localLawGraph_H_diagonalization (n : ℕ) (ω : Ω) :
    (D.localLawGraph n ω).H = D.eigenvectorMatrix n ω *
      Matrix.diagonal (fun i => ((D.eigenvalue n ω i / Real.sqrt ((d : ℝ)-1) : ℝ) : ℂ)) *
      (D.eigenvectorMatrix n ω).transpose := by
  have hd : Matrix.diagonal (fun i => ((D.eigenvalue n ω i / Real.sqrt ((d : ℝ)-1) : ℝ) : ℂ)) =
      ((Real.sqrt ((d : ℝ)-1) : ℂ)⁻¹) • D.eigenvalueMatrix n ω := by
    ext i j
    by_cases h : i = j <;> simp [eigenvalueMatrix, Matrix.diagonal_apply, h, div_eq_mul_inv, mul_comm]
  rw [hd, Matrix.mul_smul, Matrix.smul_mul, ← D.adjacency_spectral_decomposition n ω,
    D.localLawGraph_H]

theorem localLaw_sortedEigenvalues_eq (hd : 3 ≤ d) (n : ℕ) (ω : Ω) :
    SpectralConsequences.sortedEigenvalues (D.localLawGraph n ω).H_hermitian =
      fun i => D.eigenvalue n ω i / Real.sqrt ((d : ℝ)-1) := by
  let g := D.localLawGraph n ω
  let f : Fin (N n) → ℝ := fun i => D.eigenvalue n ω i / Real.sqrt ((d : ℝ)-1)
  let U := (g.H_hermitian.eigenvectorUnitary : Matrix (Fin (N n)) (Fin (N n)) ℂ)
  have hsource := GeneralizedBulk.LocalLawBridge.roots_diagonalization g.H U (star U)
    (fun i => (g.H_hermitian.eigenvalues i : ℂ))
    (unitary.coe_mul_star_self _) g.H_hermitian.spectral_theorem
  have hraw := GeneralizedBulk.LocalLawBridge.roots_diagonalization g.H
    (D.eigenvectorMatrix n ω) (D.eigenvectorMatrix n ω).transpose
    (fun i => (f i : ℂ)) (D.eigenvectorMatrix_mul_transpose n ω)
    (D.localLawGraph_H_diagonalization n ω)
  have hcomplex : ((List.ofFn (fun i => (g.H_hermitian.eigenvalues i : ℂ)) : List ℂ) : Multiset ℂ) =
      ((List.ofFn (fun i => (f i : ℂ)) : List ℂ) : Multiset ℂ) := hsource.symm.trans hraw
  have hreal : ((List.ofFn g.H_hermitian.eigenvalues : List ℝ) : Multiset ℝ) =
      ((List.ofFn f : List ℝ) : Multiset ℝ) := by
    apply Multiset.map_injective Complex.ofReal_injective
    simpa only [Multiset.map_coe, List.map_ofFn, Function.comp_def] using hcomplex
  have hperm : List.Perm (List.ofFn (sortedEigenvalues g.H_hermitian)) (List.ofFn f) := by
    apply (g.H_hermitian.eigenvalues |> (sortedEigenvaluePermutation g.H_hermitian).ofFn_comp_perm).trans
    exact Quotient.exact hreal
  have hanti : Antitone f := by
    have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
    intro i j hij
    exact div_le_div_of_nonneg_right (D.ordered n ω i j hij) (Real.sqrt_nonneg _)
  exact List.ofFn_injective (List.eq_of_perm_of_sorted hperm
    (sortedEigenvalues_antitone g.H_hermitian).ofFn_sorted hanti.ofFn_sorted)

end GeneralizedBulk.External.RegularSpectralData
