import GaussianWave.BS.LeafInnovationSplit

/-!
# Actual common-core plus single-extension coordinates

The fill map retains the common core and one chosen extension block, setting
other extension blocks to zero.  The projection and fill are proved literal
inverses on the selected coordinates.
-/
noncomputable section
namespace GaussianWave.BS

abbrev ForestInnovation (A : Type*) (m k : ℕ) := A ⊕ (A × BranchInnovation (m + 1) k)
abbrev ForestLocalInnovation (A : Type*) (m k : ℕ) := ForestInnovation A m k ⊕ NewBranchInnovation m k

def forestInnovationInclusion (A : Type*) (m k : ℕ) :
    ForestInnovation A m k → ForestInnovation A m (k + 1) :=
  Sum.elim Sum.inl (fun aj => Sum.inr (aj.1, branchInnovationInclusion (m + 1) k aj.2))

theorem forestInnovationSplit_old (A : Type*) (m k : ℕ) (j : ForestInnovation A m k) :
    forestInnovationSplit A m k (forestInnovationInclusion A m k j) = Sum.inl j := by
  cases j with
  | inl a => rfl
  | inr aj =>
      change Sum.elim (fun old => Sum.inl (Sum.inr (aj.1, old))) (fun new => Sum.inr (aj.1, new))
        (branchInnovationSplit m k (branchInnovationInclusion (m + 1) k aj.2)) = _
      rw [branchInnovationSplit_old]
      rfl

def forestLocalSection (A : Type*) [DecidableEq A] (m k : ℕ) (a : A) :
    (ForestLocalInnovation A m k → ℝ) →ₗ[ℝ]
      ((ForestInnovation A m k ⊕ (A × NewBranchInnovation m k)) → ℝ) where
  toFun z := Sum.elim (fun old => z (Sum.inl old))
    (fun bn => if bn.1 = a then z (Sum.inr bn.2) else 0)
  map_add' z w := by
    ext j
    cases j with
    | inl old => rfl
    | inr bn => by_cases h : bn.1 = a <;> simp [h]
  map_smul' r z := by
    ext j
    cases j with
    | inl old => rfl
    | inr bn => by_cases h : bn.1 = a <;> simp [h]

def forestLocalFill (A : Type*) [DecidableEq A] (m k : ℕ) (a : A) :
    (ForestLocalInnovation A m k → ℝ) →ₗ[ℝ] (ForestInnovation A m (k + 1) → ℝ) :=
  (LinearEquiv.funCongrLeft ℝ ℝ (forestInnovationSplit A m k)).toLinearMap.comp
    (forestLocalSection A m k a)

def forestLocalProjection (A : Type*) (m k : ℕ) (a : A) :
    (ForestInnovation A m (k + 1) → ℝ) →ₗ[ℝ] (ForestLocalInnovation A m k → ℝ) where
  toFun x := Sum.elim (fun old => x ((forestInnovationSplit A m k).symm (Sum.inl old)))
    (fun new => x ((forestInnovationSplit A m k).symm (Sum.inr (a, new))))
  map_add' x y := by
    ext j
    cases j <;> rfl
  map_smul' r x := by
    ext j
    cases j <;> rfl

theorem forestLocalFill_core (A : Type*) [DecidableEq A] (m k : ℕ) (a : A)
    (z : ForestLocalInnovation A m k → ℝ) (old : ForestInnovation A m k) :
    forestLocalFill A m k a z ((forestInnovationSplit A m k).symm (Sum.inl old)) = z (Sum.inl old) := by
  change forestLocalSection A m k a z
    (forestInnovationSplit A m k ((forestInnovationSplit A m k).symm (Sum.inl old))) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem forestLocalFill_new (A : Type*) [DecidableEq A] (m k : ℕ) (a : A)
    (z : ForestLocalInnovation A m k → ℝ) (new : NewBranchInnovation m k) :
    forestLocalFill A m k a z ((forestInnovationSplit A m k).symm (Sum.inr (a, new))) = z (Sum.inr new) := by
  change forestLocalSection A m k a z
    (forestInnovationSplit A m k ((forestInnovationSplit A m k).symm (Sum.inr (a, new)))) = _
  rw [Equiv.apply_symm_apply]
  simp [forestLocalSection]

theorem forestLocalProjection_fill (A : Type*) [DecidableEq A] (m k : ℕ) (a : A)
    (z : ForestLocalInnovation A m k → ℝ) :
    forestLocalProjection A m k a (forestLocalFill A m k a z) = z := by
  ext j
  cases j with
  | inl old => exact forestLocalFill_core A m k a z old
  | inr new => exact forestLocalFill_new A m k a z new

theorem forestLocalFill_old (A : Type*) [DecidableEq A] (m k : ℕ) (a : A)
    (z : ForestLocalInnovation A m k → ℝ) (old : ForestInnovation A m k) :
    forestLocalFill A m k a z (forestInnovationInclusion A m k old) = z (Sum.inl old) := by
  change forestLocalSection A m k a z
    (forestInnovationSplit A m k (forestInnovationInclusion A m k old)) = _
  rw [forestInnovationSplit_old]
  rfl

theorem forestLocalFill_projection_core (A : Type*) [DecidableEq A] (m k : ℕ) (a : A)
    (x : ForestInnovation A m (k + 1) → ℝ) (old : ForestInnovation A m k) :
    forestLocalFill A m k a (forestLocalProjection A m k a x)
      ((forestInnovationSplit A m k).symm (Sum.inl old)) =
      x ((forestInnovationSplit A m k).symm (Sum.inl old)) := by
  rw [forestLocalFill_core]
  rfl

theorem forestLocalFill_projection_new (A : Type*) [DecidableEq A] (m k : ℕ) (a : A)
    (x : ForestInnovation A m (k + 1) → ℝ) (new : NewBranchInnovation m k) :
    forestLocalFill A m k a (forestLocalProjection A m k a x)
      ((forestInnovationSplit A m k).symm (Sum.inr (a, new))) =
      x ((forestInnovationSplit A m k).symm (Sum.inr (a, new))) := by
  rw [forestLocalFill_new]
  rfl

theorem forestLocalFill_projection_old (A : Type*) [DecidableEq A] (m k : ℕ) (a : A)
    (x : ForestInnovation A m (k + 1) → ℝ) (old : ForestInnovation A m k) :
    forestLocalFill A m k a (forestLocalProjection A m k a x) (forestInnovationInclusion A m k old) =
      x (forestInnovationInclusion A m k old) := by
  have h : (forestInnovationSplit A m k).symm (Sum.inl old) = forestInnovationInclusion A m k old := by
    apply (forestInnovationSplit A m k).injective
    rw [Equiv.apply_symm_apply, forestInnovationSplit_old]
  rw [← h]
  exact forestLocalFill_projection_core A m k a x old

theorem forestLocalFill_projection_branch (A : Type*) [DecidableEq A] (m k : ℕ) (a : A)
    (x : ForestInnovation A m (k + 1) → ℝ) (j : BranchInnovation (m + 1) (k + 1)) :
    forestLocalFill A m k a (forestLocalProjection A m k a x) (Sum.inr (a, j)) = x (Sum.inr (a, j)) := by
  cases h : branchInnovationSplit m k j with
  | inl old =>
      have hg : forestInnovationSplit A m k (Sum.inr (a, j)) = Sum.inl (Sum.inr (a, old)) := by
        simp only [forestInnovationSplit, forestInnovationSplitTo, Equiv.coe_fn_mk, Sum.elim_inr,
          h, Sum.elim_inl]
      have hi : (forestInnovationSplit A m k).symm (Sum.inl (Sum.inr (a, old))) = Sum.inr (a, j) := by
        rw [← hg, Equiv.symm_apply_apply]
      rw [← hi]
      exact forestLocalFill_projection_core A m k a x (Sum.inr (a, old))
  | inr new =>
      have hg : forestInnovationSplit A m k (Sum.inr (a, j)) = Sum.inr (a, new) := by
        simp only [forestInnovationSplit, forestInnovationSplitTo, Equiv.coe_fn_mk, Sum.elim_inr, h]
      have hi : (forestInnovationSplit A m k).symm (Sum.inr (a, new)) = Sum.inr (a, j) := by
        rw [← hg, Equiv.symm_apply_apply]
      rw [← hi]
      exact forestLocalFill_projection_new A m k a x new

end GaussianWave.BS
