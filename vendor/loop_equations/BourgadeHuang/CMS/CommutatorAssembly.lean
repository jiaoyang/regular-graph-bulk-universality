import BourgadeHuang.CMS.CommutatorSums
import BourgadeHuang.CMS.GeneralCommutators

/-! Finite support assembly of the genuine CMS compatibility identity. -/
noncomputable section
open scoped BigOperators Topology
namespace BourgadeHuang.CMS
variable {d : ℕ}

private theorem sum_univ_two (F : Fin d → ℂ) (i j : Fin d) (hij : i≠j) :
    (∑k,F k) = F i+F j+∑k∈(Finset.univ.erase i).erase j,F k := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hij.symm,Finset.mem_univ j⟩)]
  ring

/-- Only the three overlapping pair orientations survive a double pair sum. -/
private theorem double_sum_pair_support (b : Fin d → Fin d → ℂ) (i j : Fin d)
    (hij : i≠j) (hrow : ∀l,b i l=0) (hcol : ∀k,b k j=0) (hrev : b j i=0)
    (hdis : ∀k∈(Finset.univ.erase i).erase j,∀l∈(Finset.univ.erase i).erase j,
      k≠l → b k l=0) :
    (∑k,∑l,b k l) = ∑k∈(Finset.univ.erase i).erase j,(b j k+b k i+b k k) := by
  have hd k (hk : k∈(Finset.univ.erase i).erase j) :
      (∑l∈(Finset.univ.erase i).erase j,b k l) = b k k := by
    apply Finset.sum_eq_single k
    · intro l hl hne
      exact hdis k hk l hl hne.symm
    · exact fun hn => (hn hk).elim
  rw [sum_univ_two (fun k => ∑l,b k l) i j hij]
  simp only [hrow,Finset.sum_const_zero,zero_add]
  rw [sum_univ_two (b j) i j hij,hrev,hcol,zero_add,zero_add]
  have he : (∑k∈(Finset.univ.erase i).erase j,∑l,b k l) =
      ∑k∈(Finset.univ.erase i).erase j,(b k i+b k k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [sum_univ_two (b k) i j hij,hcol,add_zero,hd k hk]
  rw [he]
  simp only [Finset.sum_add_distrib]
  ring

@[simp] theorem pairOperator_zero (c : Fin d → ℂ) (i j : Fin d) :
    pairOperator c i j (0 : Point d → ℂ) = 0 := by
  funext z
  simp [pairOperator,chargeDirection,coordDeriv]

@[simp] theorem freeOperator_zero (c : Fin d → ℂ) (i : Fin d) :
    freeOperator c i (0 : Point d → ℂ) = 0 := by
  funext z
  simp [freeOperator,secondPartial,coordDeriv]

theorem deformedOperator_commutator_expansion (β : ℂ) (c : Fin d → ℂ) (i j : Fin d)
    {f : Point d → ℂ} {z : Point d} (hf : AnalyticAt ℂ f z) (hz : CollisionFree z) :
    operatorCommutator (deformedOperator β c i) (deformedOperator β c j) f z =
      (2/β)*(∑k,operatorCommutator (freeOperator c i) (pairOperator c j k) f z)+
      (2/β)*(∑k,operatorCommutator (pairOperator c i k) (freeOperator c j) f z)+
      (2/β)^2*(∑k,∑l,operatorCommutator (pairOperator c i k) (pairOperator c j l) f z) := by
  rw [deformedOperator_commutator_atom_sum β c i j hf hz]
  simp only [Fintype.sum_option,cmsAtom,cmsAtomWeight,one_mul,mul_one,
    freeOperator_commutator c i j hf,Finset.sum_add_distrib,add_zero,
    ← Finset.mul_sum,← Finset.sum_mul]
  ring

theorem pairOperator_commutator_sum (c : Fin d → ℂ) (i j : Fin d)
    {f : Point d → ℂ} {z : Point d} (hf : AnalyticAt ℂ f z) (hz : CollisionFree z)
    (hij : i≠j) :
    (∑k,∑l,operatorCommutator (pairOperator c i k) (pairOperator c j l) f z) =
      2*(inverseGap i j z)^2*
        (c i^2*(∑k∈(Finset.univ.erase i).erase j,pairOperator c j k f z)-
         c j^2*(∑k∈(Finset.univ.erase i).erase j,pairOperator c i k f z)) := by
  rw [double_sum_pair_support (fun k l =>
    operatorCommutator (pairOperator c i k) (pairOperator c j l) f z) i j hij]
  · simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k≠i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k≠j := (Finset.mem_erase.mp hk).1
    exact pairOperator_three_body_commutator c i j k hf hz hij hki.symm hkj.symm
  · intro l
    simp [operatorCommutator,pairOperator_self]
  · intro k
    simp [operatorCommutator,pairOperator_self]
  · exact pairOperator_reverse_commutator c i j hf (hz.sub_ne_zero hij)
  · intro k hk l hl hkl
    have hki : k≠i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k≠j := (Finset.mem_erase.mp hk).1
    have hli : l≠i := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    have hlj : l≠j := (Finset.mem_erase.mp hl).1
    exact pairOperator_disjoint_commutator c i k j l hf
      (hz.sub_ne_zero hki.symm) (hz.sub_ne_zero hlj.symm) hij hli.symm hkj hkl

theorem free_pair_commutator_sum (c : Fin d → ℂ) (i j : Fin d)
    {f : Point d → ℂ} {z : Point d} (hf : AnalyticAt ℂ f z) (hz : CollisionFree z)
    (hij : i≠j) :
    (∑k,operatorCommutator (freeOperator c i) (pairOperator c j k) f z) =
      operatorCommutator (freeOperator c i) (pairOperator c j i) f z := by
  apply Finset.sum_eq_single i
  · intro k hk hki
    by_cases hkj : k=j
    · subst k
      simp [operatorCommutator,pairOperator_self]
    · exact free_pair_disjoint_commutator c i j k hf (hz.sub_ne_zero (Ne.symm hkj)) hij hki.symm
  · simp

/-- The general-coupling compatibility identity, proved for the actual
analytic coordinate derivatives. -/
theorem deformedOperator_commutator (β : ℂ) (c : Fin d → ℂ) (i j : Fin d)
    {f : Point d → ℂ} {z : Point d} (hf : AnalyticAt ℂ f z) (hz : CollisionFree z)
    (hij : i≠j) (hβ : β≠0) (hc : ∀k,c k = -1 ∨ c k = β/2) :
    deformedOperator β c i (deformedOperator β c j f) z-
      deformedOperator β c j (deformedOperator β c i f) z =
      (4/β)/(z i-z j)^2*
        (c i^2*deformedOperator β c j f z-c j^2*deformedOperator β c i f z) := by
  change operatorCommutator (deformedOperator β c i) (deformedOperator β c j) f z = _
  rw [deformedOperator_commutator_expansion β c i j hf hz,
    free_pair_commutator_sum c i j hf hz hij,pairOperator_commutator_sum c i j hf hz hij]
  have hr : (∑k,operatorCommutator (pairOperator c i k) (freeOperator c j) f z) =
      operatorCommutator (pairOperator c i j) (freeOperator c j) f z := by
    simp_rw [operatorCommutator_swap (pairOperator c i _) (freeOperator c j)]
    rw [Finset.sum_neg_distrib,free_pair_commutator_sum c j i hf hz hij.symm]
  rw [hr,← mul_add]
  rw [free_pair_two_body_commutator β c i j hf hz hij hβ (hc i) (hc j)]
  have hi : deformedOperator β c i f z = freeOperator c i f z+(2/β)*pairOperator c i j f z+
      (2/β)*∑k∈(Finset.univ.erase i).erase j,pairOperator c i k f z := by
    rw [deformedOperator_eq_atom_sum,Fintype.sum_option]
    simp only [cmsAtomWeight,cmsAtom,one_mul,← Finset.mul_sum]
    rw [sum_univ_two (fun k => pairOperator c i k f z) i j hij,pairOperator_self]
    simp only [Pi.zero_apply,zero_add]
    ring
  have hj : deformedOperator β c j f z = freeOperator c j f z+(2/β)*pairOperator c j i f z+
      (2/β)*∑k∈(Finset.univ.erase i).erase j,pairOperator c j k f z := by
    rw [deformedOperator_eq_atom_sum,Fintype.sum_option]
    simp only [cmsAtomWeight,cmsAtom,one_mul,← Finset.mul_sum]
    rw [sum_univ_two (fun k => pairOperator c j k f z) i j hij,pairOperator_self]
    simp only [Pi.zero_apply,add_zero]
    ring
  rw [hi,hj]
  simp only [inverseGap,div_eq_mul_inv,inv_pow]
  ring

end BourgadeHuang.CMS
