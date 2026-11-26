import GeneralizedBulk.Graph.SchurExterior

/-!
# Exterior coordinates for an arbitrary injectively selected finite boundary

The block decomposition is constructed from the actual selected vertices and
their complement. The Schur scalar identity therefore concerns the literal
finite resolvent restriction and the actual outside principal minor.
-/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Graph

variable {V m : Type*} [Fintype V] [Fintype m] [DecidableEq V] [DecidableEq m]

abbrev Outside (e : m → V) := {v : V // v ∉ Set.range e}

local instance outsideFintype (e : m → V) : Fintype (Outside e) := Fintype.ofFinite _

def boundaryEquiv (e : m → V) (he : Function.Injective e) : m ⊕ Outside e ≃ V := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl (Outside e))).trans
    (Equiv.sumCompl (fun v => v ∈ Set.range e))

@[simp] theorem boundaryEquiv_inl (e : m → V) (he : Function.Injective e) (a : m) :
    boundaryEquiv e he (Sum.inl a) = e a := rfl

@[simp] theorem boundaryEquiv_inr (e : m → V) (he : Function.Injective e) (v : Outside e) :
    boundaryEquiv e he (Sum.inr v) = (v : V) := rfl

/-- The chosen boundary and its complement give an actual reindexing of the
full finite matrix into its four literal submatrices. -/
theorem boundary_reindex (H : Matrix V V ℂ) (e : m → V) (he : Function.Injective e) :
    H.submatrix (boundaryEquiv e he) (boundaryEquiv e he) =
      Matrix.fromBlocks (H.submatrix e e) (H.submatrix e (fun v : Outside e => (v : V)))
        (H.submatrix (fun v : Outside e => (v : V)) e) (H.submatrix (fun v : Outside e => (v : V)) (fun v : Outside e => (v : V))) := by
  ext a b
  cases a <;> cases b <;> rfl

/-- Trace is invariant under this genuine finite coordinate permutation. -/
theorem trace_submatrix_equiv {W : Type*} [Fintype W] (H : Matrix V V ℂ) (q : W ≃ V) :
    Matrix.trace (H.submatrix q q) = Matrix.trace H := by
  exact Equiv.sum_comp q (fun v => H v v)

theorem boundary_reindex_shift_inverse (H : Matrix V V ℂ)
    (e : m → V) (he : Function.Injective e) (z : ℂ) :
    (H - z • (1 : Matrix V V ℂ))⁻¹.submatrix (boundaryEquiv e he) (boundaryEquiv e he) =
      (Matrix.fromBlocks (H.submatrix e e - z • 1) (H.submatrix e (fun v : Outside e => (v : V)))
        (H.submatrix (fun v : Outside e => (v : V)) e) (H.submatrix (fun v : Outside e => (v : V)) (fun v : Outside e => (v : V)) - z • 1))⁻¹ := by
  rw [← Matrix.inv_submatrix_equiv]
  congr 1
  rw [fromBlocks_shift, ← boundary_reindex H e he]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, (boundaryEquiv e he).injective.eq_iff]

/-- The exact scalar exterior coordinate is the trace of the actual deleted
minor resolvent, for any injective boundary selection. -/
theorem boundary_exterior_trace_identity (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (e : m → V) (he : Function.Injective e) (z : ℂ) (hz : z.im ≠ 0) :
    Matrix.trace ((H - z • (1 : Matrix V V ℂ))⁻¹) -
      Matrix.trace ((((H - z • (1 : Matrix V V ℂ))⁻¹).submatrix e e)⁻¹ *
        (((H - z • (1 : Matrix V V ℂ))⁻¹ *
          (H - z • (1 : Matrix V V ℂ))⁻¹).submatrix e e)) =
      Matrix.trace ((H.submatrix (fun v : Outside e => (v : V)) (fun v : Outside e => (v : V)) - z • 1)⁻¹) := by
  let q := boundaryEquiv e he
  let R := (H - z • (1 : Matrix V V ℂ))⁻¹
  let Rb := (Matrix.fromBlocks (H.submatrix e e - z • 1) (H.submatrix e (fun v : Outside e => (v : V)))
    (H.submatrix (fun v : Outside e => (v : V)) e) (H.submatrix (fun v : Outside e => (v : V)) (fun v : Outside e => (v : V)) - z • 1))⁻¹
  have hblocks : (Matrix.fromBlocks (H.submatrix e e) (H.submatrix e (fun v : Outside e => (v : V)))
      (H.submatrix (fun v : Outside e => (v : V)) e) (H.submatrix (fun v : Outside e => (v : V)) (fun v : Outside e => (v : V)))).IsHermitian := by
    rw [← boundary_reindex H e he]
    exact hH.submatrix q
  have hRb : Rb = R.submatrix q q := (boundary_reindex_shift_inverse H e he z).symm
  have hboundary : Rb.submatrix Sum.inl Sum.inl = R.submatrix e e := by
    rw [hRb]
    ext a b
    rfl
  have hsquare : (Rb * Rb).submatrix Sum.inl Sum.inl = (R * R).submatrix e e := by
    rw [hRb, Matrix.submatrix_mul_equiv]
    ext a b
    rfl
  have htrace : Matrix.trace Rb = Matrix.trace R := by
    rw [hRb]
    exact trace_submatrix_equiv R q
  have ht := shifted_exterior_trace_identity (H.submatrix e e) (H.submatrix e (fun v : Outside e => (v : V)))
    (H.submatrix (fun v : Outside e => (v : V)) e) (H.submatrix (fun v : Outside e => (v : V)) (fun v : Outside e => (v : V))) hblocks z hz
  change Matrix.trace Rb - Matrix.trace ((Rb.submatrix Sum.inl Sum.inl)⁻¹ *
    ((Rb * Rb).submatrix Sum.inl Sum.inl)) = _ at ht
  rw [htrace, hboundary, hsquare] at ht
  exact ht

/-- The actual boundary inverse, and hence its exterior self-energy, depends
on the outside minor and the two coupling blocks by the Schur formula. -/
theorem boundary_exterior_selfEnergy (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (e : m → V) (he : Function.Injective e) (J : Matrix m m ℂ)
    (z : ℂ) (hz : z.im ≠ 0) :
    J - (((H - z • (1 : Matrix V V ℂ))⁻¹).submatrix e e)⁻¹ =
      J - (H.submatrix e e - z • 1) + H.submatrix e (fun v : Outside e => (v : V)) *
        (H.submatrix (fun v : Outside e => (v : V)) (fun v : Outside e => (v : V)) - z • 1)⁻¹ *
          H.submatrix (fun v : Outside e => (v : V)) e := by
  let q := boundaryEquiv e he
  let A := H.submatrix e e
  let B := H.submatrix e (fun v : Outside e => (v : V))
  let C := H.submatrix (fun v : Outside e => (v : V)) e
  let D := H.submatrix (fun v : Outside e => (v : V)) (fun v : Outside e => (v : V))
  have hblocks : (Matrix.fromBlocks A B C D).IsHermitian := by
    rw [show Matrix.fromBlocks A B C D = H.submatrix q q from (boundary_reindex H e he).symm]
    exact hH.submatrix q
  have hD : D.IsHermitian := hH.submatrix (fun v : Outside e => (v : V))
  have hminor := hermitian_shift_isUnit D hD z hz
  have hschur := shifted_schurComplement_isUnit A B C D hblocks z hz
  have hb : ((Matrix.fromBlocks (A - z • 1) B C (D - z • 1))⁻¹).submatrix Sum.inl Sum.inl =
      ((H - z • (1 : Matrix V V ℂ))⁻¹).submatrix e e := by
    rw [← boundary_reindex_shift_inverse H e he z]
    ext a b
    rfl
  have ht := exterior_selfEnergy_identity J (A - z • 1) B C (D - z • 1) hminor hschur
  rw [hb] at ht
  exact ht

end GeneralizedBulk.Graph
