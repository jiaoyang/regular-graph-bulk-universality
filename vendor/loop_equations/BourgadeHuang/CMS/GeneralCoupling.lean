import BourgadeHuang.CMS.OriginalContinuation

/-! # The unified general-coupling CMS operator

A numerator has charge −1 and a denominator has charge β/2. This charge notation
retains the actual complex coordinate derivatives and treats both blocks in one
operator. Polynomial clearing gives analytic continuation across numerator
collisions without any assumed PDE continuation principle.
-/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace BourgadeHuang.CMS

def deformedOperator {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (i : Fin d)
    (F : Point d → ℂ) (z : Point d) : ℂ :=
  secondPartial i F z+c i^2*F z+(2/β)*∑j∈Finset.univ.erase i,
    (c i*c j*coordDeriv i F z-c i^2*coordDeriv j F z)/(z i-z j)

def clearedDeformedOperator {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (i : Fin d)
    (F : Point d → ℂ) (z : Point d) : ℂ :=
  rowClearing i z*(secondPartial i F z+c i^2*F z)+(2/β)*∑j∈Finset.univ.erase i,
    rowClearingErase i j z*(c i*c j*coordDeriv i F z-c i^2*coordDeriv j F z)

theorem analyticAt_clearedDeformedOperator {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (i : Fin d)
    {F : Point d → ℂ} {z : Point d} (hf : AnalyticAt ℂ F z) :
    AnalyticAt ℂ (clearedDeformedOperator β c i F) z := by
  have hd j := analyticAt_coordDeriv hf j
  apply AnalyticAt.add
  · exact (analyticAt_rowClearing i z).mul
      ((analyticAt_coordDeriv (hd i) i).add (analyticAt_const.mul hf))
  · apply analyticAt_const.mul
    apply Finset.analyticAt_sum
    intro j _
    exact (analyticAt_rowClearingErase i j z).mul
      ((analyticAt_const.mul (hd i)).sub (analyticAt_const.mul (hd j)))

theorem clearedDeformedOperator_eq {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (i : Fin d)
    (F : Point d → ℂ) {z : Point d} (hz : CollisionFree z) :
    clearedDeformedOperator β c i F z = rowClearing i z*deformedOperator β c i F z := by
  unfold clearedDeformedOperator deformedOperator
  simp only [mul_add]
  rw [mul_left_comm (rowClearing i z) (2/β)]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [rowClearing_mul_div hz i j (Finset.mem_erase.mp hj).1.symm]

/-- A genuinely analytic deformed-CMS solution on one numerator neighborhood
extends to every collision-free numerator tuple with the denominators fixed. -/
theorem deformedOperator_eq_zero_of_local_numerator {n m : ℕ}
    (β : ℂ) (c : Fin (n+m) → ℂ) (F : Point (n+m) → ℂ) (v : Point m)
    (hf : ∀ u : Point n, AnalyticAt ℂ F (Fin.append u v)) (u₀ : Point n)
    (hlocal : ∀ᶠ u in nhds u₀, CollisionFree (Fin.append u v) ∧
      ∀ i, deformedOperator β c i F (Fin.append u v) = 0)
    (u : Point n) (hu : CollisionFree (Fin.append u v)) :
    ∀ i, deformedOperator β c i F (Fin.append u v) = 0 := by
  intro i
  have ha : AnalyticOnNhd ℂ (fun t : Point n =>
      clearedDeformedOperator β c i F (Fin.append t v)) Set.univ :=
    fun t _ => (analyticAt_clearedDeformedOperator β c i (hf t)).comp
      (f := fun w : Point n => Fin.append w v) (analyticAt_append_left v t)
  have he : (fun t : Point n => clearedDeformedOperator β c i F (Fin.append t v)) =ᶠ[nhds u₀]
      (fun _ => (0:ℂ)) := by
    filter_upwards [hlocal] with t ht
    rw [clearedDeformedOperator_eq β c i F ht.1,ht.2 i,mul_zero]
  have hz := congrFun (ha.eq_of_eventuallyEq analyticOnNhd_const he) u
  rw [clearedDeformedOperator_eq β c i F hu] at hz
  exact (mul_eq_zero.mp hz).resolve_left (rowClearing_ne_zero hu i)

/-- The two physical charges satisfy exactly the scalar relation required to
turn the hierarchy's self-interaction into a second coordinate derivative. -/
theorem charge_self_interaction {β c : ℂ} (hβ : β ≠ 0) (hc : c = -1 ∨ c = β/2) :
    c^2*((2-β)/β+(2/β)*c) = c := by
  rcases hc with rfl | rfl <;> field_simp <;> ring

/-- The algebraic conversion of a deformed loop head into the actual CMS
operator, valid for every finite family of charges satisfying the self relation. -/
theorem deformed_loop_algebra {d : ℕ} (β : ℂ) (c S D : Fin d → ℂ)
    (K : Fin d → Fin d → ℂ) (z : Point d) (P : ℂ) (i : Fin d)
    (hself : c i^2*((2-β)/β+(2/β)*c i) = c i)
    (hK : K i i = D i)
    (hquot : ∀j∈Finset.univ.erase i,(S i-S j)/(z i-z j)=K i j) :
    (c i*D i+c i^2*S i^2)*P+c i^2*P+(2/β)*
      (∑j∈Finset.univ.erase i,
        (c i*c j*(c i*S i*P)-c i^2*(c j*S j*P))/(z i-z j)) =
      c i^2*(((2-β)/β*D i+S i^2+1+(2/β)*∑j,c j*K i j)*P) := by
  have hterm j (hj : j∈Finset.univ.erase i) :
      (c i*c j*(c i*S i*P)-c i^2*(c j*S j*P))/(z i-z j) =
        c i^2*(c j*K i j)*P := by
    rw [← hquot j hj]
    ring
  have hsum : (∑j,c j*K i j) = (∑j∈Finset.univ.erase i,c j*K i j)+c i*D i := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),hK]
  rw [Finset.sum_congr rfl hterm]
  simp only [← Finset.sum_mul,← Finset.mul_sum,hsum]
  have he := congrArg (fun a : ℂ => a*D i*P) hself
  linear_combination -he

end BourgadeHuang.CMS
