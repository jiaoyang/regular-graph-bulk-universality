import GeneralizedBulk.Entropy.TensorKernel

/-! Fixed orthonormal coordinates adapted to scalar and transverse star colors. -/
noncomputable section
open scoped BigOperators

namespace GeneralizedBulk.Entropy.Channel

abbrev WhiteCoordinate (d : ℕ) :=
  Fin (Module.finrank ℝ ℝ) ⊕ Fin (Module.finrank ℝ (Transverse d))
abbrev ScalarCoordinate (d k : ℕ) := (a : Fin k) × WhiteCoordinate d

def scalarAdaptedWhiteBasis (d : ℕ) : OrthonormalBasis (WhiteCoordinate d) ℝ (WhiteStar d) :=
  (stdOrthonormalBasis ℝ ℝ).prod (stdOrthonormalBasis ℝ (Transverse d))

def scalarAdaptedBasis (d k : ℕ) :
    OrthonormalBasis (ScalarCoordinate d k) ℝ (ColoredStar d k) :=
  Pi.orthonormalBasis (fun _ : Fin k => scalarAdaptedWhiteBasis d)

def scalarCoordinates (d k : ℕ) : ColoredStar d k ≃L[ℝ] (ScalarCoordinate d k → ℝ) :=
  (scalarAdaptedBasis d k).repr.toContinuousLinearEquiv.trans
    (WithLp.linearEquiv 2 ℝ (ScalarCoordinate d k → ℝ)).toContinuousLinearEquiv

@[simp] theorem scalarCoordinates_apply (d k : ℕ) (x : ColoredStar d k)
    (j : ScalarCoordinate d k) :
    scalarCoordinates d k x j = (scalarAdaptedWhiteBasis d).repr (x j.1) j.2 := rfl

def scalarObserved (d k : ℕ) : Finset (ScalarCoordinate d k) := by
  classical
  exact Finset.univ.filter (fun j => j.2.isLeft)

@[simp] theorem mem_scalarObserved (d k : ℕ) (j : ScalarCoordinate d k) :
    j ∈ scalarObserved d k ↔ j.2.isLeft := by
  classical
  simp [scalarObserved]

/-- Scalar projection is exactly coordinate deletion in this fixed basis.
The basis is independent of all spectral/bulk parameters. -/
theorem scalarCoordinates_scalarPart (d k : ℕ) (x : ColoredStar d k) :
    scalarCoordinates d k (scalarPart d k x) =
      fun j => if j ∈ scalarObserved d k then scalarCoordinates d k x j else 0 := by
  classical
  funext j
  rcases j with ⟨a, j⟩
  cases j with
  | inl r =>
    simp [scalarCoordinates_apply, scalarAdaptedWhiteBasis, OrthonormalBasis.repr_apply_apply,
      OrthonormalBasis.prod_apply, WithLp.prod_inner_apply, scalarPart]
  | inr r =>
    simp [scalarCoordinates_apply, scalarAdaptedWhiteBasis, OrthonormalBasis.repr_apply_apply,
      OrthonormalBasis.prod_apply, WithLp.prod_inner_apply, scalarPart]

/-- Every deleted coordinate direction is a genuine transverse vector. -/
theorem scalarPart_scalarCoordinates_symm_basis (d k : ℕ) (j : ScalarCoordinate d k)
    (hj : j ∉ scalarObserved d k) :
    scalarPart d k ((scalarCoordinates d k).symm (Pi.single j 1)) = 0 := by
  classical
  apply (scalarCoordinates d k).injective
  rw [scalarCoordinates_scalarPart]
  rw [(scalarCoordinates d k).apply_symm_apply, (scalarCoordinates d k).map_zero]
  funext i
  by_cases hi : i ∈ scalarObserved d k
  · have hij : i ≠ j := by intro h; exact hj (h ▸ hi)
    simp [hi, Pi.single_apply, hij]
  · simp [hi]

theorem transversePart_scalarCoordinates_symm_basis (d k : ℕ) (j : ScalarCoordinate d k)
    (hj : j ∉ scalarObserved d k) :
    transversePart d k ((scalarCoordinates d k).symm (Pi.single j 1)) =
      (scalarCoordinates d k).symm (Pi.single j 1) := by
  have h := scalarPart_add_transversePart d k ((scalarCoordinates d k).symm (Pi.single j 1))
  rw [scalarPart_scalarCoordinates_symm_basis d k j hj, zero_add] at h
  exact h

end GeneralizedBulk.Entropy.Channel
