import GaussianWave.BS.SpectralGraphAdapter
import GaussianWave.BS.FiniteCoverSampling
import GaussianWave.BS.FiniteAtomicLaws

/-! Exact identification of the spectral-data star sampler with the actual
uniform finite-tree-cover sampler, including neighbor-order permutations. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph

/-- The C0 ball coordinates, ordered as root followed by d neighbors. -/
def starBallSite (m : ℕ) : Fin (m+2+1) → VertexBallVertex (m+2) 0 :=
  Fin.cases (Sum.inl ()) (fun j => Sum.inr (j,()))

end GaussianWave.BS
namespace GaussianWave.RegularEigenData
open BS BS.Reused.Graph BS.Reused.Graph.Configuration
variable {N m c : ℕ} (D : RegularEigenData (m+2) N c)

/-- The spectral and canonical graph port orders differ by this actual
bijection of their finite random sources. -/
def spectralStarCoverSeedEquiv :
    (Fin N × Equiv.Perm (Fin (m+2))) ≃ VertexCoverSeed N m 0 where
  toFun z := (z.1,D.canonicalNeighborRelabel z.1*z.2,fun _ => ())
  invFun z := (z.1,(D.canonicalNeighborRelabel z.1)⁻¹*z.2.1)
  left_inv := by rintro ⟨v,σ⟩; simp
  right_inv := by
    rintro ⟨v,τ,orders⟩
    simp only [mul_inv_cancel_left]
    congr

/-- The concrete mark identity under the actual source bijection. -/
theorem spectralStarCover_sample {r : ℕ} (q : Fin r → Fin N → ℝ)
    (z : Fin N × Equiv.Perm (Fin (m+2))) (aj : Fin r × Fin (m+2+1)) :
    Real.sqrt N*q aj.1
      (vertexGraphCover D.regularGraph 0 (D.spectralStarCoverSeedEquiv z) (starBallSite m aj.2)) =
      D.starSample q z aj := by
  rcases aj with ⟨a,j⟩
  induction j using Fin.cases with
  | zero => rfl
  | succ j =>
    change Real.sqrt N*q a (graphNeighbor D.regularGraph z.1
      ((D.canonicalNeighborRelabel z.1*z.2) j)) =
      Real.sqrt N*q a (D.neighbor z.1 (z.2 j))
    rw [Equiv.Perm.mul_apply,D.graphNeighbor_relabel]

/-- Equality of the literal probability laws, with no sampling consistency
or Gaussianity premise. -/
theorem starLaw_eq_cover_zero {r : ℕ} (q : Fin r → Fin N → ℝ) :
    D.starLaw q = Measure.map
      (fun z : (Fin r × VertexBallVertex (m+2) 0) → ℝ =>
        fun aj : Fin r × Fin (m+2+1) => z (aj.1,starBallSite m aj.2))
      (finiteVertexCoverLaw D.regularGraph 0 (fun a v => Real.sqrt N*q a v)) := by
  let mark := fun seed : VertexCoverSeed N m 0 => fun aj : Fin r × Fin (m+2+1) =>
    Real.sqrt N*q aj.1 (vertexGraphCover D.regularGraph 0 seed (starBallSite m aj.2))
  have he : mark ∘ D.spectralStarCoverSeedEquiv = D.starSample q := by
    funext seed aj
    exact D.spectralStarCover_sample q seed aj
  have hs := uniformAtomicLaw_reindex D.spectralStarCoverSeedEquiv mark
  rw [he] at hs
  change uniformAtomicLaw (D.starSample q) = _
  change _ = Measure.map _ (uniformAtomicLaw
    (fun seed : VertexCoverSeed N m 0 => fun av : Fin r × VertexBallVertex (m+2) 0 =>
      Real.sqrt N*q av.1 (vertexGraphCover D.regularGraph 0 seed av.2)))
  rw [uniformAtomicLaw_map _ _ (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))]
  exact hs

/-- Every normalized eigenvector has actual empirical root second moment
one; no moment-normalization hypothesis is required. -/
theorem normalized_eigenvector_root_second (i : Fin c) :
    (N : ℝ)⁻¹*∑ v,(Real.sqrt N*D.eigenvector i v)^2=1 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.size_pos)
  have horth := D.orthonormal i i
  simp only [if_pos rfl] at horth
  simp_rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [← Finset.mul_sum,inv_mul_cancel_left₀ hN]
  simpa only [pow_two] using horth

end GaussianWave.RegularEigenData
