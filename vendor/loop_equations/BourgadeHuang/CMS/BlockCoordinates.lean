import BourgadeHuang.CMS.Gauge
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Fin.Basic

/-! The analytic two-block/combined-coordinate interface. These are identities
between the genuine coordinate derivatives defined in Basic and Gauge. -/
noncomputable section
open scoped BigOperators Topology
namespace BourgadeHuang.CMS

/-- Express a two-block function as a function on the combined coordinate space. -/
def blockFunction {n m : ℕ} (F : Point n → Point m → ℂ) (z : Point (n + m)) : ℂ :=
  F (fun i => z (Fin.castAdd m i)) (fun a => z (Fin.natAdd n a))

@[simp] theorem blockFunction_append {n m : ℕ} (F : Point n → Point m → ℂ)
    (t : Point n) (s : Point m) : blockFunction F (Fin.append t s) = F t s := by
  simp [blockFunction]

private theorem castAdd_ne_natAdd {n m : ℕ} (i : Fin n) (a : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n a := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = n + a.val at hv
  exact (Nat.not_lt_of_ge (Nat.le_add_right n a.val)) (hv ▸ i.isLt)

/-- A left block update is exactly the corresponding combined-coordinate update. -/
theorem blockFunction_update_left {n m : ℕ} (F : Point n → Point m → ℂ)
    (z : Point (n + m)) (i : Fin n) (u : ℂ) :
    blockFunction F (Function.update z (Fin.castAdd m i) u) =
      F (Function.update (fun j => z (Fin.castAdd m j)) i u)
        (fun a => z (Fin.natAdd n a)) := by
  unfold blockFunction
  rw [Function.update_comp_eq_of_injective' z (Fin.castAdd_injective n m) i u]
  rw [Function.update_comp_eq_of_forall_ne' z u
    (fun a => Ne.symm (castAdd_ne_natAdd i a))]

/-- The right block update identity. -/
theorem blockFunction_update_right {n m : ℕ} (F : Point n → Point m → ℂ)
    (z : Point (n + m)) (a : Fin m) (u : ℂ) :
    blockFunction F (Function.update z (Fin.natAdd n a) u) =
      F (fun i => z (Fin.castAdd m i))
        (Function.update (fun b => z (Fin.natAdd n b)) a u) := by
  unfold blockFunction
  rw [Function.update_comp_eq_of_forall_ne' z u (fun i => castAdd_ne_natAdd i a)]
  rw [Function.update_comp_eq_of_injective' z (show Function.Injective (Fin.natAdd n : Fin m → Fin (n + m)) from fun i j h =>
    Fin.ext (Nat.add_left_cancel (congrArg (fun k : Fin (n + m) => k.val) h))) a u]

/-- Actual coordinate derivative correspondence in the left block. -/
theorem coordDeriv_blockFunction_left {n m : ℕ} (F : Point n → Point m → ℂ)
    (i : Fin n) :
    coordDeriv (Fin.castAdd m i) (blockFunction F) = blockFunction (leftPartial i F) := by
  funext z
  unfold coordDeriv
  simp_rw [blockFunction_update_left]
  rfl

/-- Actual coordinate derivative correspondence in the right block. -/
theorem coordDeriv_blockFunction_right {n m : ℕ} (F : Point n → Point m → ℂ)
    (a : Fin m) :
    coordDeriv (Fin.natAdd n a) (blockFunction F) = blockFunction (rightPartial a F) := by
  funext z
  unfold coordDeriv
  simp_rw [blockFunction_update_right]
  rfl

theorem secondPartial_blockFunction_left {n m : ℕ} (F : Point n → Point m → ℂ)
    (i : Fin n) :
    secondPartial (Fin.castAdd m i) (blockFunction F) =
      blockFunction (leftPartial i (leftPartial i F)) := by
  rw [secondPartial, coordDeriv_blockFunction_left, coordDeriv_blockFunction_left]

theorem secondPartial_blockFunction_right {n m : ℕ} (F : Point n → Point m → ℂ)
    (a : Fin m) :
    secondPartial (Fin.natAdd n a) (blockFunction F) =
      blockFunction (rightPartial a (rightPartial a F)) := by
  rw [secondPartial, coordDeriv_blockFunction_right, coordDeriv_blockFunction_right]

/-- Inserting a prescribed zero diagonal term does not change a finite sum.
This is only a summation identity; no collision is removed from a PDE domain. -/
private theorem sum_erase_eq_sum {d : ℕ} (f : Fin d → ℂ) (i : Fin d) (hi : f i = 0) :
    (∑ j ∈ Finset.univ.erase i, f j) = ∑ j, f j := by
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  simpa [hi] using h

/-- The reduced operator (D.3) is precisely the combined-coordinate operator (D.6). -/
theorem reducedOperator_blockFunction_left {n m : ℕ}
    (F : Point n → Point m → ℂ) (i : Fin n) (t : Point n) (s : Point m) :
    reducedOperator (Fin.castAdd m i) (blockFunction F) (Fin.append t s) =
      leftReduced i F t s := by
  unfold reducedOperator
  rw [secondPartial_blockFunction_left]
  simp only [blockFunction_append]
  rw [sum_erase_eq_sum _ (Fin.castAdd m i) (by simp), Fin.sum_univ_add]
  simp only [coordDeriv_blockFunction_left, coordDeriv_blockFunction_right,
    blockFunction_append, Fin.append_left, Fin.append_right]
  rw [← sum_erase_eq_sum (fun j =>
    (leftPartial i F t s - leftPartial j F t s) / (t i - t j)) i (by simp)]
  unfold leftReduced
  ring

/-- The reduced operator (D.4) is precisely the combined-coordinate operator (D.6). -/
theorem reducedOperator_blockFunction_right {n m : ℕ}
    (F : Point n → Point m → ℂ) (a : Fin m) (t : Point n) (s : Point m) :
    reducedOperator (Fin.natAdd n a) (blockFunction F) (Fin.append t s) =
      rightReduced a F t s := by
  unfold reducedOperator
  rw [secondPartial_blockFunction_right]
  simp only [blockFunction_append]
  rw [sum_erase_eq_sum _ (Fin.natAdd n a) (by simp), Fin.sum_univ_add]
  simp only [coordDeriv_blockFunction_left, coordDeriv_blockFunction_right,
    blockFunction_append, Fin.append_left, Fin.append_right]
  rw [← sum_erase_eq_sum (fun b =>
    (rightPartial a F t s - rightPartial b F t s) / (s a - s b)) a (by simp)]
  unfold rightReduced
  ring

/-- Theorem D.1 with its reduced side written exactly as the combined-coordinate
operator (D.6) from Basic. This is an analytic gauge theorem for arbitrary n,m. -/
theorem gauge_combined_system_iff {n m : ℕ} (t : Point n) (s : Point m)
    (G : Point n → Point m → ℂ)
    (hc : CrossDistinct t s) (ht : Function.Injective t) (hs : Function.Injective s)
    (hgl : ∀ i, ∀ᶠ u in 𝓝 (t i),
      DifferentiableAt ℂ (fun v => G (Function.update t i v) s) u)
    (hgr : ∀ a, ∀ᶠ u in 𝓝 (s a),
      DifferentiableAt ℂ (fun v => G t (Function.update s a v)) u)
    (hgl2 : ∀ i, DifferentiableAt ℂ
      (fun u => leftPartial i G (Function.update t i u) s) (t i))
    (hgr2 : ∀ a, DifferentiableAt ℂ
      (fun u => rightPartial a G t (Function.update s a u)) (s a)) :
    ((∀ i, leftOriginal i (fun t s => mixedVandermonde t s * G t s) t s = 0) ∧
     (∀ a, rightOriginal a (fun t s => mixedVandermonde t s * G t s) t s = 0)) ↔
    (∀ r, reducedOperator r (blockFunction G) (Fin.append t s) = 0) := by
  rw [gauge_system_iff t s G hc ht hs hgl hgr hgl2 hgr2]
  constructor
  · rintro ⟨hl, hr⟩ r
    refine Fin.addCases (fun i => ?_) (fun a => ?_) r
    · simpa only [reducedOperator_blockFunction_left] using hl i
    · simpa only [reducedOperator_blockFunction_right] using hr a
  · intro h
    constructor
    · intro i
      simpa only [reducedOperator_blockFunction_left] using h (Fin.castAdd m i)
    · intro a
      simpa only [reducedOperator_blockFunction_right] using h (Fin.natAdd n a)


end BourgadeHuang.CMS
