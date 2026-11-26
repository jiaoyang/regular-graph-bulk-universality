import BourgadeHuang.CMS.CommutatorCalculus

/-! The local two-body and three-body commutator identities for genuine CMS
operators. The three-body cancellation is independent of the charge values. -/
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Topology
namespace BourgadeHuang.CMS
variable {d : ℕ} {f : Point d → ℂ} {z : Point d}

theorem pairOperator_reverse_commutator (c : Fin d → ℂ) (i j : Fin d)
    (hf : AnalyticAt ℂ f z) (hij : z i-z j ≠ 0) :
    operatorCommutator (pairOperator c i j) (pairOperator c j i) f z = 0 := by
  have hji : z j-z i ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hij).symm
  have hij' : i ≠ j := by intro h; subst j; simp at hij
  rw [pairOperator_commutator c i j j i hf hij hji,
    chargeDirection_inverseGap c i j j i hji,
    chargeDirection_inverseGap c j i i j hij]
  simp only [pairSlope,hij',hij'.symm,if_true,if_false,sub_zero,zero_sub,
    inverseGap,chargeDirection]
  field_simp [hij,hji]
  ring

theorem pairOperator_disjoint_commutator (c : Fin d → ℂ) (i j k l : Fin d)
    (hf : AnalyticAt ℂ f z) (hij : z i-z j ≠ 0) (hkl : z k-z l ≠ 0)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    operatorCommutator (pairOperator c i j) (pairOperator c k l) f z = 0 := by
  rw [pairOperator_commutator c i j k l hf hij hkl,
    chargeDirection_inverseGap c i j k l hkl,
    chargeDirection_inverseGap c k l i j hij]
  simp [pairSlope,hik,hil,hjk,hjl,hik.symm,hil.symm,hjk.symm,hjl.symm]

theorem free_pair_disjoint_commutator (c : Fin d → ℂ) (i k l : Fin d)
    (hf : AnalyticAt ℂ f z) (hkl : z k-z l ≠ 0) (hik : i≠k) (hil : i≠l) :
    operatorCommutator (freeOperator c i) (pairOperator c k l) f z = 0 := by
  rw [free_pair_commutator c i k l hf hkl,secondPartial_inverseGap k l i hkl,
    coordDeriv_inverseGap k l i hkl]
  simp [pairSlope,hik.symm,hil.symm]

theorem inverseGap_triangle (i j k : Fin d) (hz : CollisionFree z)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    inverseGap i j z*inverseGap i k z+inverseGap i k z*inverseGap j k z-
      inverseGap i j z*inverseGap j k z = 0 := by
  unfold inverseGap
  field_simp [hz.sub_ne_zero hij,hz.sub_ne_zero hik,hz.sub_ne_zero hjk]
  ring

/-- The full three-coordinate cancellation; no special charge relation is used. -/
theorem pairOperator_three_body_commutator (c : Fin d → ℂ) (i j k : Fin d)
    (hf : AnalyticAt ℂ f z) (hz : CollisionFree z) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    operatorCommutator (pairOperator c i j) (pairOperator c j k) f z+
    operatorCommutator (pairOperator c i k) (pairOperator c j i) f z+
    operatorCommutator (pairOperator c i k) (pairOperator c j k) f z =
      2*(inverseGap i j z)^2*(c i^2*pairOperator c j k f z-c j^2*pairOperator c i k f z) := by
  rw [pairOperator_commutator c i j j k hf (hz.sub_ne_zero hij) (hz.sub_ne_zero hjk),
    pairOperator_commutator c i k j i hf (hz.sub_ne_zero hik) (hz.sub_ne_zero hij.symm),
    pairOperator_commutator c i k j k hf (hz.sub_ne_zero hik) (hz.sub_ne_zero hjk)]
  simp only [chargeDirection_inverseGap c _ _ _ _ (hz.sub_ne_zero hjk),
    chargeDirection_inverseGap c _ _ _ _ (hz.sub_ne_zero hij),
    chargeDirection_inverseGap c _ _ _ _ (hz.sub_ne_zero hik),
    chargeDirection_inverseGap c _ _ _ _ (hz.sub_ne_zero hij.symm)]
  have hrev : inverseGap j i z = -inverseGap i j z := by
    unfold inverseGap
    rw [show z j-z i=-(z i-z j) by ring,inv_neg]
  simp only [pairSlope,hij,hij.symm,hik,hik.symm,hjk,hjk.symm,if_true,if_false,
    pairOperator,chargeDirection,hrev]
  linear_combination
    (c i*c j^2*c k*(inverseGap i j z+inverseGap i k z)*coordDeriv i f z+
      c i^2*c j*c k*(inverseGap i j z-inverseGap j k z)*coordDeriv j f z+
      c i^2*c j^2*(-2*inverseGap i j z-inverseGap i k z+inverseGap j k z)*coordDeriv k f z)*
        (inverseGap_triangle i j k hz hij hik hjk)

/-- Two physical charges provide precisely the remaining two-coordinate
cancellation. Both blocks, including the mixed block, are covered. -/
theorem free_pair_two_body_commutator (β : ℂ) (c : Fin d → ℂ) (i j : Fin d)
    (hf : AnalyticAt ℂ f z) (hz : CollisionFree z) (hij : i≠j) (hβ : β≠0)
    (hci : c i = -1 ∨ c i = β/2) (hcj : c j = -1 ∨ c j = β/2) :
    (2/β)*(operatorCommutator (freeOperator c i) (pairOperator c j i) f z+
      operatorCommutator (pairOperator c i j) (freeOperator c j) f z) =
    (4/β)*(inverseGap i j z)^2*
      (c i^2*(freeOperator c j f z+(2/β)*pairOperator c j i f z)-
       c j^2*(freeOperator c i f z+(2/β)*pairOperator c i j f z)) := by
  rw [operatorCommutator_swap (pairOperator c i j) (freeOperator c j),
    free_pair_commutator c i j i hf (hz.sub_ne_zero hij.symm),
    free_pair_commutator c j i j hf (hz.sub_ne_zero hij),
    secondPartial_inverseGap j i i (hz.sub_ne_zero hij.symm),
    secondPartial_inverseGap i j j (hz.sub_ne_zero hij),
    coordDeriv_inverseGap j i i (hz.sub_ne_zero hij.symm),
    coordDeriv_inverseGap i j j (hz.sub_ne_zero hij)]
  simp only [pairSlope,hij,hij.symm,if_true,if_false,pairOperator,chargeDirection,
    freeOperator,secondPartial]
  rw [coordDeriv_comm_analytic hf j i]
  have hrev : inverseGap j i z = -inverseGap i j z := by
    unfold inverseGap
    rw [show z j-z i=-(z i-z j) by ring,inv_neg]
  rw [hrev]
  have hcharge : (c i-c j)*(1+(2/β)*c i*c j)=0 := by
    rcases hci with hi | hi <;> rcases hcj with hj | hj
    all_goals
      rw [hi,hj]
      field_simp [hβ] <;> ring
  linear_combination
    (-2*(2/β)*(inverseGap i j z)^3*(c j*coordDeriv i f z-c i*coordDeriv j f z))*hcharge

end BourgadeHuang.CMS
