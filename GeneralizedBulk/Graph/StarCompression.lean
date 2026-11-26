import GeneralizedBulk.Graph.StarRescale
import GeneralizedBulk.Graph.ResolventCovarianceBounds
import GeneralizedBulk.Matrix.CoordinateCompression

/-! Distinct star coordinates give genuine nondegenerate Gaussian marginal laws. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Covariance
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem neighbor_ne_root (o : Fin (N n)) (j : Fin d) : D.neighbor n ω o j ≠ o := by
  intro h
  have hh := (D.neighbor_exact n ω o (D.neighbor n ω o j)).mpr ⟨j,rfl⟩
  rw [h, D.diagonal_zero] at hh
  norm_num at hh

theorem entropyStarVertex_injective (o : Fin (N n)) : Function.Injective (D.entropyStarVertex n ω o) := by
  intro i j
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun b => ?_) j
    · intro h
      rfl
    · intro h
      exact False.elim (D.neighbor_ne_root n ω o b h.symm)
  · refine Fin.cases ?_ (fun b => ?_) j
    · intro h
      exact False.elim (D.neighbor_ne_root n ω o a h)
    · intro h
      exact congrArg Fin.succ (D.neighbor_injective n ω o h)

theorem localEntropyStarCovariance_bounds (o : Fin (N n)) (E eta sigma : ℝ)
    (heta : 0 < eta) (hsigma : 0 < sigma) (x : Fin (d+1) → ℝ) :
    ((eta / sigma) / (((d : ℝ)+|E|)^2+eta^2)) * (∑ i, x i ^ 2) ≤
      dotProduct x ((D.localEntropyStarCovariance n ω o E eta sigma).mulVec x) ∧
    dotProduct x ((D.localEntropyStarCovariance n ω o E eta sigma).mulVec x) ≤
      (1 / (sigma*eta)) * ∑ i, x i ^ 2 :=
  coordinate_compression_bounds _ _ (D.entropyStarVertex_injective n ω o) _ _
    (D.resolventCovariance_quadratic_bounds n ω E eta sigma heta hsigma) x

theorem localEntropyStarCovariance_posDef (o : Fin (N n)) (E eta sigma : ℝ)
    (heta : 0 < eta) (hsigma : 0 < sigma) : (D.localEntropyStarCovariance n ω o E eta sigma).PosDef := by
  apply coordinate_compression_posDef (D.resolventCovariance n ω E eta sigma)
    (D.resolventCovariance_posDef n ω E eta sigma heta hsigma).isHermitian
    (D.entropyStarVertex n ω o) (D.entropyStarVertex_injective n ω o)
    ((eta / sigma) / (((d : ℝ)+|E|)^2+eta^2)) (by positivity)
  intro x
  exact (D.resolventCovariance_quadratic_bounds n ω E eta sigma heta hsigma x).1

theorem localEntropyStarCovariance_factor (o : Fin (N n)) (E eta sigma : ℝ)
    (heta : 0 < eta) (hsigma : 0 < sigma) :
    ∃ M : Matrix (Fin (d+1)) (Fin (d+1)) ℝ,
      M*M.transpose=D.localEntropyStarCovariance n ω o E eta sigma ∧ M.det ≠ 0 :=
  exists_nonsingular_covariance_factor _ (D.localEntropyStarCovariance_posDef n ω o E eta sigma heta hsigma)

theorem localEntropyStarCovariance_rectangular_gram (o : Fin (N n)) (E eta sigma : ℝ)
    (heta : 0 < eta) (hsigma : 0 < sigma) :
    let B := (D.resolventCovarianceFactor n ω E eta sigma).submatrix (D.entropyStarVertex n ω o) id
    B*B.transpose=D.localEntropyStarCovariance n ω o E eta sigma := by
  ext i j
  exact congrFun (congrFun (D.resolventCovariance_factor n ω E eta sigma heta hsigma)
    (D.entropyStarVertex n ω o i)) (D.entropyStarVertex n ω o j)

end GeneralizedBulk.External.RegularSpectralData
