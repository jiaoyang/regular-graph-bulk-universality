import GeneralizedBulk.Graph.ProposalFiberVariance
import GeneralizedBulk.ExternalGeometry
import GeneralizedBulk.Graph.EigenvalueBound

/-!
# Finite spectral polynomial functional calculus and compression error

The polynomial is the genuine finite sum of powers of the graph adjacency.
The spectral formula and entrywise uniform-approximation estimate are proved
from the orthonormal eigenbasis, without a functional-calculus assumption.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def polynomialMatrix (Q : Polynomial ℝ) : Matrix (Fin (N n)) (Fin (N n)) ℂ :=
  ∑ k ∈ Q.support, (Q.coeff k : ℂ) • ((D.adjacency n ω).map Complex.ofReal) ^ k

def spectralMultiplier (f : ℝ → ℂ) : Matrix (Fin (N n)) (Fin (N n)) ℂ :=
  fun v w => D.spectralCompression n ω Finset.univ (fun k => f (D.eigenvalue n ω k)) v w

/-- Powers of the literal adjacency matrix have the actual diagonal spectral
representation. -/
theorem adjacency_power_eq_spectral (k : ℕ) :
    ((D.adjacency n ω).map Complex.ofReal) ^ k =
      D.eigenvectorMatrix n ω * Matrix.diagonal (fun i => (D.eigenvalue n ω i : ℂ) ^ k) *
        (D.eigenvectorMatrix n ω).transpose := by
  induction k with
  | zero =>
      simp only [pow_zero]
      change 1 = D.eigenvectorMatrix n ω * 1 * (D.eigenvectorMatrix n ω).transpose
      rw [mul_one, D.eigenvectorMatrix_mul_transpose n ω]
  | succ k ih =>
      rw [pow_succ, ih, D.adjacency_spectral_decomposition n ω]
      change _ = D.eigenvectorMatrix n ω * Matrix.diagonal (fun i => (D.eigenvalue n ω i : ℂ) ^ (k + 1)) *
        (D.eigenvectorMatrix n ω).transpose
      have hd : Matrix.diagonal (fun i => (D.eigenvalue n ω i : ℂ) ^ k) * D.eigenvalueMatrix n ω =
          Matrix.diagonal (fun i => (D.eigenvalue n ω i : ℂ) ^ (k + 1)) := by
        simp only [eigenvalueMatrix, Matrix.diagonal_mul_diagonal, pow_succ, Pi.mul_apply]
      calc
        _ = D.eigenvectorMatrix n ω * Matrix.diagonal (fun i => (D.eigenvalue n ω i : ℂ) ^ k) *
            ((D.eigenvectorMatrix n ω).transpose * D.eigenvectorMatrix n ω) *
              D.eigenvalueMatrix n ω * (D.eigenvectorMatrix n ω).transpose := by
          simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [D.eigenvectorMatrix_transpose_mul n ω, mul_one]
          simpa only [Matrix.mul_assoc] using congrArg
            (fun M => D.eigenvectorMatrix n ω * M * (D.eigenvectorMatrix n ω).transpose) hd

theorem adjacency_power_entry (k : ℕ) (v w : Fin (N n)) :
    (((D.adjacency n ω).map Complex.ofReal) ^ k) v w =
      ∑ i, (D.eigenvalue n ω i : ℂ) ^ k * (D.eigenvector n ω i v : ℂ) *
        (D.eigenvector n ω i w : ℂ) := by
  rw [D.adjacency_power_eq_spectral n ω k, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, eigenvectorMatrix, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Polynomial evaluation of the actual adjacency equals its finite spectral
multiplier, with coefficients and eigenvalues still real before casting. -/
theorem polynomialMatrix_eq_spectralMultiplier (Q : Polynomial ℝ) :
    D.polynomialMatrix n ω Q = D.spectralMultiplier n ω (fun x => ((Q.eval x : ℝ) : ℂ)) := by
  have heval (x : ℝ) : ((Q.eval x : ℝ) : ℂ) =
      ∑ k ∈ Q.support, (Q.coeff k : ℂ) * (x : ℂ) ^ k := by
    rw [Polynomial.eval_eq_sum]
    simp only [Polynomial.sum, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
  ext v w
  simp only [polynomialMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [D.adjacency_power_entry n ω, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [spectralMultiplier, spectralCompression, heval, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Uniform scalar approximation gives an entrywise approximation of the
actual graph spectral multiplier, with no dimension loss. -/
theorem spectralMultiplier_sub_polynomial_entry_norm_le
    (f : ℝ → ℂ) (Q : Polynomial ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (happrox : ∀ k : Fin (N n), ‖f (D.eigenvalue n ω k) - ((Q.eval (D.eigenvalue n ω k) : ℝ) : ℂ)‖ ≤ delta)
    (v w : Fin (N n)) :
    ‖D.spectralMultiplier n ω f v w - D.polynomialMatrix n ω Q v w‖ ≤ delta := by
  rw [D.polynomialMatrix_eq_spectralMultiplier n ω Q]
  have heq : D.spectralMultiplier n ω f v w -
      D.spectralMultiplier n ω (fun x => ((Q.eval x : ℝ) : ℂ)) v w =
      D.spectralCompression n ω Finset.univ
        (fun k => f (D.eigenvalue n ω k) - ((Q.eval (D.eigenvalue n ω k) : ℝ) : ℂ)) v w := by
    dsimp [spectralMultiplier, spectralCompression]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [heq]
  exact D.spectralCompression_norm_le n ω Finset.univ _ delta hdelta (fun k _ => happrox k) v w

/-- The actual polynomial entry counts walks with its actual real
coefficients. All locality arguments can therefore be performed on walks. -/
theorem polynomialMatrix_entry_walks (Q : Polynomial ℝ) (v w : Fin (N n)) :
    D.polynomialMatrix n ω Q v w =
      ∑ k ∈ Q.support, (Q.coeff k : ℂ) *
        (Fintype.card {p : (D.simpleGraph n ω).Walk v w | p.length = k} : ℂ) := by
  simp only [polynomialMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← D.simpleGraph_adjacency_complex n ω]
  rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk]

/-- Weierstrass approximation on the genuine spectral interval gives one
polynomial whose entrywise compression error is uniform over all graph
sizes, graph samples and endpoint choices. -/
theorem exists_uniform_polynomial_compression
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-(d : ℝ)) (d : ℝ)))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Q : Polynomial ℝ, ∀ n : ℕ, ∀ ω : Ω, ∀ v w : Fin (N n),
      ‖D.spectralMultiplier n ω (fun x => (f x : ℂ)) v w - D.polynomialMatrix n ω Q v w‖ ≤ epsilon := by
  obtain ⟨Q,hQ⟩ := exists_polynomial_near_of_continuousOn (-(d : ℝ)) (d : ℝ) f hf epsilon hepsilon
  refine ⟨Q, fun n ω v w => ?_⟩
  apply D.spectralMultiplier_sub_polynomial_entry_norm_le n ω _ Q epsilon hepsilon.le _ v w
  intro k
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  exact (hQ _ (D.eigenvalue_mem_spectralInterval n ω k)).le

end GeneralizedBulk.External.RegularSpectralData
