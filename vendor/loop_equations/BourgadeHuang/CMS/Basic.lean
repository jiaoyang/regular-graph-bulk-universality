import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert

/-! Genuine coordinate differential operators on finite-dimensional complex space.
The derivatives are mathlib's complex derivatives of coordinate slices. -/

noncomputable section
open scoped BigOperators

namespace BourgadeHuang.CMS

abbrev Point (d : ℕ) := Fin d → ℂ
abbrev Sign := Bool

def signValue (s : Sign) : ℂ := if s then 1 else -1

@[simp] theorem signValue_true : signValue true = 1 := rfl
@[simp] theorem signValue_false : signValue false = -1 := rfl
@[simp] theorem signValue_sq (s : Sign) : signValue s ^ 2 = 1 := by
  cases s <;> norm_num [signValue]

/-- All pairwise coordinate collisions are excluded. -/
def CollisionFree {d : ℕ} (z : Point d) : Prop := Function.Injective z

theorem CollisionFree.sub_ne_zero {d : ℕ} {z : Point d}
    (hz : CollisionFree z) {i j : Fin d} (hij : i ≠ j) : z i - z j ≠ 0 :=
  _root_.sub_ne_zero.mpr (fun h => hij (hz h))

/-- The genuine complex coordDeriv derivative in coordinate `i`. -/
def coordDeriv {d : ℕ} (i : Fin d) (f : Point d → ℂ) (z : Point d) : ℂ :=
  deriv (fun w : ℂ => f (Function.update z i w)) (z i)

def secondPartial {d : ℕ} (i : Fin d) (f : Point d → ℂ) : Point d → ℂ :=
  coordDeriv i (coordDeriv i f)

/-- Appendix D, equation (D.6). -/
def reducedOperator {d : ℕ} (i : Fin d) (f : Point d → ℂ) (z : Point d) : ℂ :=
  secondPartial i f z + f z +
    ∑ j ∈ Finset.univ.erase i, (coordDeriv i f z - coordDeriv j f z) / (z i - z j)

def IsReducedSolution {d : ℕ} (f : Point d → ℂ) : Prop :=
  ∀ z, CollisionFree z → ∀ i, reducedOperator i f z = 0

/-- Coordinate slices are affine, including for a different coordinate. -/
theorem hasDerivAt_update_coord {d : ℕ} (z : Point d) (i j : Fin d) :
    HasDerivAt (fun w : ℂ => Function.update z i w j)
      (if j = i then 1 else 0) (z i) := by
  by_cases h : j = i
  · subst j
    simpa using hasDerivAt_id (z i)
  · simpa [Function.update_of_ne h, h] using hasDerivAt_const (z i) (z j)

/-- Product logarithmic-derivative rule, without any division by the factors. -/
theorem hasDerivAt_finset_prod_log {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℂ → ℂ) (a : ι → ℂ) (x : ℂ)
    (hf : ∀ k ∈ s, HasDerivAt (f k) (a k * f k x) x) :
    HasDerivAt (fun y => ∏ k ∈ s, f k y)
      ((∑ k ∈ s, a k) * ∏ k ∈ s, f k x) x := by
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const x (1 : ℂ)
  | @insert k s hks ih =>
    have hk := hf k (Finset.mem_insert_self k s)
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    convert hk.mul hs using 1 <;>
      simp only [Finset.prod_insert hks, Finset.sum_insert hks] <;> ring

end BourgadeHuang.CMS
