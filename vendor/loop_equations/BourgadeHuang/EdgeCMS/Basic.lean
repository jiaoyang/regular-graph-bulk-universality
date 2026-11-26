import BourgadeHuang.CMS.GeneralCoupling

/-! The edge deformed Calogero--Moser system, with its actual linear
coordinate potential.  Numerator charges are `-1`; denominator charges are
`β / 2`.  These definitions encode equations (8.1)--(8.3), rather than
the constant-potential bulk system. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace BourgadeHuang.EdgeCMS
open CMS

/-- Unified edge equation: `∂ᵢ² F - cᵢ² zᵢ F` plus the genuine CMS
first-order pair interactions. -/
def edgeOperator {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (i : Fin d)
    (F : Point d → ℂ) (z : Point d) : ℂ :=
  secondPartial i F z - c i ^ 2 * z i * F z + (2 / β) *
    ∑ j ∈ Finset.univ.erase i,
      (c i * c j * coordDeriv i F z - c i ^ 2 * coordDeriv j F z) / (z i - z j)

def clearedEdgeOperator {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (i : Fin d)
    (F : Point d → ℂ) (z : Point d) : ℂ :=
  rowClearing i z * (secondPartial i F z - c i ^ 2 * z i * F z) + (2 / β) *
    ∑ j ∈ Finset.univ.erase i,
      rowClearingErase i j z *
        (c i * c j * coordDeriv i F z - c i ^ 2 * coordDeriv j F z)

theorem edgeOperator_eq_bulk_sub {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (i : Fin d)
    (F : Point d → ℂ) (z : Point d) :
    edgeOperator β c i F z =
      deformedOperator β c i F z - c i ^ 2 * (z i + 1) * F z := by
  unfold edgeOperator deformedOperator
  ring

theorem analyticAt_clearedEdgeOperator {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (i : Fin d)
    {F : Point d → ℂ} {z : Point d} (hf : AnalyticAt ℂ F z) :
    AnalyticAt ℂ (clearedEdgeOperator β c i F) z := by
  have hd j := analyticAt_coordDeriv hf j
  apply AnalyticAt.add
  · exact (analyticAt_rowClearing i z).mul
      ((analyticAt_coordDeriv (hd i) i).sub
        ((analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z)).mul hf))
  · apply analyticAt_const.mul
    apply Finset.analyticAt_sum
    intro j _
    exact (analyticAt_rowClearingErase i j z).mul
      ((analyticAt_const.mul (hd i)).sub (analyticAt_const.mul (hd j)))

theorem clearedEdgeOperator_eq {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (i : Fin d)
    (F : Point d → ℂ) {z : Point d} (hz : CollisionFree z) :
    clearedEdgeOperator β c i F z = rowClearing i z * edgeOperator β c i F z := by
  unfold clearedEdgeOperator edgeOperator
  simp only [mul_add]
  rw [mul_left_comm (rowClearing i z) (2 / β)]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [rowClearing_mul_div hz i j (Finset.mem_erase.mp hj).1.symm]

/-- Polynomial clearing removes the apparent singularities of the
numerator equations; analytic continuation therefore applies to the edge
operator with its linear potential as well. -/
theorem edgeOperator_eq_zero_of_local_numerator {n m : ℕ}
    (β : ℂ) (c : Fin (n + m) → ℂ) (F : Point (n + m) → ℂ) (v : Point m)
    (hf : ∀ u : Point n, AnalyticAt ℂ F (Fin.append u v)) (u₀ : Point n)
    (hlocal : ∀ᶠ u in nhds u₀, CollisionFree (Fin.append u v) ∧
      ∀ i, edgeOperator β c i F (Fin.append u v) = 0)
    (u : Point n) (hu : CollisionFree (Fin.append u v)) :
    ∀ i, edgeOperator β c i F (Fin.append u v) = 0 := by
  intro i
  have ha : AnalyticOnNhd ℂ (fun t : Point n =>
      clearedEdgeOperator β c i F (Fin.append t v)) Set.univ :=
    fun t _ => (analyticAt_clearedEdgeOperator β c i (hf t)).comp
      (f := fun w : Point n => Fin.append w v) (analyticAt_append_left v t)
  have he : (fun t : Point n => clearedEdgeOperator β c i F (Fin.append t v)) =ᶠ[nhds u₀]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [hlocal] with t ht
    rw [clearedEdgeOperator_eq β c i F ht.1, ht.2 i, mul_zero]
  have hz := congrFun (ha.eq_of_eventuallyEq analyticOnNhd_const he) u
  rw [clearedEdgeOperator_eq β c i F hu] at hz
  exact (mul_eq_zero.mp hz).resolve_left (rowClearing_ne_zero hu i)

/-- Algebraic passage from the edge loop head to the edge CMS equation.
The spectral term is `-zᵢ`, as in the article. -/
theorem edge_loop_algebra {d : ℕ} (β : ℂ) (c S D : Fin d → ℂ)
    (K : Fin d → Fin d → ℂ) (z : Point d) (P : ℂ) (i : Fin d)
    (hself : c i ^ 2 * ((2 - β) / β + (2 / β) * c i) = c i)
    (hK : K i i = D i)
    (hquot : ∀ j ∈ Finset.univ.erase i, (S i - S j) / (z i - z j) = K i j) :
    (c i * D i + c i ^ 2 * S i ^ 2) * P - c i ^ 2 * z i * P + (2 / β) *
      (∑ j ∈ Finset.univ.erase i,
        (c i * c j * (c i * S i * P) - c i ^ 2 * (c j * S j * P)) / (z i - z j)) =
      c i ^ 2 * (((2 - β) / β * D i + S i ^ 2 - z i +
        (2 / β) * ∑ j, c j * K i j) * P) := by
  have h := deformed_loop_algebra β c S D K z P i hself hK hquot
  linear_combination h

end BourgadeHuang.EdgeCMS
