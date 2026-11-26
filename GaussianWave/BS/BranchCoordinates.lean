import GaussianWave.BS.FiniteTreeGeometry

/-!
# Constructive sibling-difference coordinates

At an internal vertex the eigenrelation fixes the sum of its child values.
Their differences from the first child give all the remaining coordinates.
This file constructs and inverts the coordinates recursively on a literal
finite branch.  It contains no covariance or independence hypothesis.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

def siblingFill (m : ℕ) (total : ℝ) (z : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases ((total - ∑ i, z i) / (m + 1))
    (fun i => z i + (total - ∑ j, z j) / (m + 1))

@[simp] theorem siblingFill_zero (m : ℕ) (s : ℝ) (z : Fin m → ℝ) :
    siblingFill m s z 0 = (s - ∑ i, z i) / (m + 1) := rfl

@[simp] theorem siblingFill_succ (m : ℕ) (s : ℝ) (z : Fin m → ℝ) (i : Fin m) :
    siblingFill m s z i.succ = z i + (s - ∑ j, z j) / (m + 1) := rfl

theorem sum_siblingFill (m : ℕ) (s : ℝ) (z : Fin m → ℝ) :
    (∑ a, siblingFill m s z a) = s := by
  rw [Fin.sum_univ_succ]
  simp only [siblingFill_succ, siblingFill_zero, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

@[simp] theorem siblingFill_difference (m : ℕ) (s : ℝ) (z : Fin m → ℝ) (i : Fin m) :
    siblingFill m s z i.succ - siblingFill m s z 0 = z i := by
  simp only [siblingFill_succ, siblingFill_zero]
  ring

theorem siblingFill_reconstruct (m : ℕ) (x : Fin (m + 1) → ℝ) :
    siblingFill m (∑ a, x a) (fun i => x i.succ - x 0) = x := by
  have hs : (∑ a, x a) - ∑ i : Fin m, (x i.succ - x 0) = (m + 1 : ℝ) * x 0 := by
    rw [Fin.sum_univ_succ]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  ext a
  refine Fin.cases ?_ (fun i => ?_) a
  · simp only [siblingFill_zero, hs, Nat.cast_add, Nat.cast_one,
      mul_div_cancel_left₀ _ hm]
  · simp only [siblingFill_succ, hs, Nat.cast_add, Nat.cast_one,
      mul_div_cancel_left₀ _ hm]
    ring

theorem siblingFill_add (m : ℕ) (s t : ℝ) (z w : Fin m → ℝ) :
    siblingFill m (s + t) (z + w) = siblingFill m s z + siblingFill m t w := by
  ext a
  refine Fin.cases ?_ (fun i => ?_) a <;>
    simp only [siblingFill_zero, siblingFill_succ, Pi.add_apply,
      Finset.sum_add_distrib] <;> ring

theorem siblingFill_smul (m : ℕ) (a s : ℝ) (z : Fin m → ℝ) :
    siblingFill m (a * s) (a • z) = a • siblingFill m s z := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp only [siblingFill_zero, siblingFill_succ, Pi.smul_apply,
      smul_eq_mul, ← Finset.mul_sum] <;> ring

/-- All eigenrelations inside a rooted branch; the supplied parent is just
outside the branch.  Boundary leaves carry no equation. -/
def BranchEigenrelation (m : ℕ) : (k : ℕ) → ℝ → ℝ → (BranchVertex (m + 1) k → ℝ) → Prop
  | 0, _, _, _ => True
  | k + 1, energy, parent, x =>
      (∑ a : Fin (m + 1), x (Sum.inr (a, branchRoot (m + 1) k))) =
          energy * x (Sum.inl ()) - parent ∧
      ∀ a, BranchEigenrelation m k energy (x (Sum.inl ())) (fun v => x (Sum.inr (a, v)))

def branchBuild (m : ℕ) : (k : ℕ) → ℝ → ℝ → ℝ →
    (BranchInnovation (m + 1) k → ℝ) → (BranchVertex (m + 1) k → ℝ)
  | 0, _, _, root, _ => fun _ => root
  | k + 1, energy, parent, root, z => Sum.elim (fun _ => root) (fun av =>
      branchBuild m k energy root
        (siblingFill m (energy * root - parent) (fun i => z (Sum.inl i)) av.1)
        (fun j => z (Sum.inr (av.1, j))) av.2)

@[simp] theorem branchBuild_root (m k : ℕ) (energy parent root : ℝ)
    (z : BranchInnovation (m + 1) k → ℝ) :
    branchBuild m k energy parent root z (branchRoot (m + 1) k) = root := by
  cases k <;> rfl

def branchExtract (m : ℕ) : (k : ℕ) → (BranchVertex (m + 1) k → ℝ) →
    (BranchInnovation (m + 1) k → ℝ)
  | 0, _ => Empty.elim
  | k + 1, x => Sum.elim
      (fun i => x (Sum.inr (i.succ, branchRoot (m + 1) k)) -
        x (Sum.inr (0, branchRoot (m + 1) k)))
      (fun aj => branchExtract m k (fun v => x (Sum.inr (aj.1, v))) aj.2)

theorem branchBuild_eigenrelation (m k : ℕ) (energy parent root : ℝ)
    (z : BranchInnovation (m + 1) k → ℝ) :
    BranchEigenrelation m k energy parent (branchBuild m k energy parent root z) := by
  induction k generalizing parent root with
  | zero => trivial
  | succ k ih =>
      constructor
      · simp only [branchBuild, Sum.elim_inr, Sum.elim_inl, branchBuild_root]
        exact sum_siblingFill _ _ _
      · intro a
        simpa only [branchBuild, Sum.elim_inl, Sum.elim_inr] using
          ih root (siblingFill m (energy * root - parent) (fun i => z (Sum.inl i)) a)
            (fun j => z (Sum.inr (a, j)))

theorem branchExtract_build (m k : ℕ) (energy parent root : ℝ)
    (z : BranchInnovation (m + 1) k → ℝ) :
    branchExtract m k (branchBuild m k energy parent root z) = z := by
  induction k generalizing parent root with
  | zero => ext i; exact Empty.elim i
  | succ k ih =>
      ext j
      cases j with
      | inl i =>
          simp only [branchExtract, Sum.elim_inl, branchBuild, Sum.elim_inr,
            branchBuild_root, siblingFill_difference]
      | inr aj =>
          simpa only [branchExtract, Sum.elim_inr, branchBuild] using
            congrFun (ih root
              (siblingFill m (energy * root - parent) (fun i => z (Sum.inl i)) aj.1)
              (fun j => z (Sum.inr (aj.1, j)))) aj.2

theorem branchBuild_extract (m k : ℕ) (energy parent : ℝ)
    (x : BranchVertex (m + 1) k → ℝ) (hx : BranchEigenrelation m k energy parent x) :
    branchBuild m k energy parent (x (branchRoot (m + 1) k)) (branchExtract m k x) = x := by
  induction k generalizing parent with
  | zero => ext i; cases i; rfl
  | succ k ih =>
      have hc : siblingFill m (energy * x (Sum.inl ()) - parent)
          (fun i => x (Sum.inr (i.succ, branchRoot (m + 1) k)) -
            x (Sum.inr (0, branchRoot (m + 1) k))) =
          fun a => x (Sum.inr (a, branchRoot (m + 1) k)) := by
        rw [← hx.1]
        exact siblingFill_reconstruct _ _
      ext v
      cases v with
      | inl u => cases u; rfl
      | inr av =>
          change branchBuild m k energy (x (Sum.inl ()))
            (siblingFill m _ _ av.1) _ av.2 = _
          change branchBuild m k energy (x (Sum.inl ()))
            (siblingFill m (energy * x (Sum.inl ()) - parent)
              (fun i => x (Sum.inr (i.succ, branchRoot (m + 1) k)) -
                x (Sum.inr (0, branchRoot (m + 1) k))) av.1)
            (branchExtract m k (fun v => x (Sum.inr (av.1, v)))) av.2 = _
          rw [congrFun hc av.1]
          exact congrFun (ih _ _ (hx.2 av.1)) av.2

theorem branchBuild_add (m k : ℕ) (energy p q r s : ℝ)
    (z w : BranchInnovation (m + 1) k → ℝ) :
    branchBuild m k energy (p + q) (r + s) (z + w) =
      branchBuild m k energy p r z + branchBuild m k energy q s w := by
  induction k generalizing p q r s with
  | zero => rfl
  | succ k ih =>
      ext v
      cases v with
      | inl u => rfl
      | inr av =>
          change branchBuild m k energy (r + s)
            (siblingFill m (energy * (r + s) - (p + q))
              (fun i => z (Sum.inl i) + w (Sum.inl i)) av.1)
            (fun j => z (Sum.inr (av.1, j)) + w (Sum.inr (av.1, j))) av.2 = _
          have hs : energy * (r + s) - (p + q) = (energy * r - p) + (energy * s - q) := by ring
          have hf : siblingFill m ((energy * r - p) + (energy * s - q))
              (fun i => z (Sum.inl i) + w (Sum.inl i)) av.1 =
              siblingFill m (energy * r - p) (fun i => z (Sum.inl i)) av.1 +
              siblingFill m (energy * s - q) (fun i => w (Sum.inl i)) av.1 :=
            congrFun (siblingFill_add m (energy * r - p) (energy * s - q)
              (fun i => z (Sum.inl i)) (fun i => w (Sum.inl i))) av.1
          rw [hs, hf]
          exact congrFun (ih _ _ _ _ _ _) av.2

theorem branchBuild_smul (m k : ℕ) (energy a p r : ℝ)
    (z : BranchInnovation (m + 1) k → ℝ) :
    branchBuild m k energy (a * p) (a * r) (a • z) = a • branchBuild m k energy p r z := by
  induction k generalizing p r with
  | zero => rfl
  | succ k ih =>
      ext v
      cases v with
      | inl u => rfl
      | inr av =>
          change branchBuild m k energy (a * r)
            (siblingFill m (energy * (a * r) - a * p)
              (fun i => a * z (Sum.inl i)) av.1)
            (fun j => a * z (Sum.inr (av.1, j))) av.2 = _
          have hs : energy * (a * r) - a * p = a * (energy * r - p) := by ring
          have hf : siblingFill m (a * (energy * r - p))
              (fun i => a * z (Sum.inl i)) av.1 =
              a * siblingFill m (energy * r - p) (fun i => z (Sum.inl i)) av.1 :=
            congrFun (siblingFill_smul m a (energy * r - p)
              (fun i => z (Sum.inl i))) av.1
          rw [hs, hf]
          exact congrFun (ih _ _ _) av.2

theorem branchExtract_add (m k : ℕ) (x y : BranchVertex (m + 1) k → ℝ) :
    branchExtract m k (x + y) = branchExtract m k x + branchExtract m k y := by
  induction k with
  | zero => ext i; exact Empty.elim i
  | succ k ih =>
      ext j
      cases j with
      | inl i =>
          simp only [branchExtract, Sum.elim_inl, Pi.add_apply]
          ring
      | inr aj => exact congrFun (ih _ _) aj.2

theorem branchExtract_smul (m k : ℕ) (a : ℝ) (x : BranchVertex (m + 1) k → ℝ) :
    branchExtract m k (a • x) = a • branchExtract m k x := by
  induction k with
  | zero => ext i; exact Empty.elim i
  | succ k ih =>
      ext j
      cases j with
      | inl i =>
          simp only [branchExtract, Sum.elim_inl, Pi.smul_apply, smul_eq_mul]
          ring
      | inr aj => exact congrFun (ih _) aj.2

def branchBuildLinear (m k : ℕ) (energy : ℝ) :
    (ℝ × ℝ × (BranchInnovation (m + 1) k → ℝ)) →ₗ[ℝ]
      (BranchVertex (m + 1) k → ℝ) where
  toFun z := branchBuild m k energy z.1 z.2.1 z.2.2
  map_add' x y := branchBuild_add m k energy x.1 y.1 x.2.1 y.2.1 x.2.2 y.2.2
  map_smul' a x := branchBuild_smul m k energy a x.1 x.2.1 x.2.2

def branchExtractLinear (m k : ℕ) :
    (BranchVertex (m + 1) k → ℝ) →ₗ[ℝ] (BranchInnovation (m + 1) k → ℝ) where
  toFun := branchExtract m k
  map_add' := branchExtract_add m k
  map_smul' := branchExtract_smul m k

end GaussianWave.BS
