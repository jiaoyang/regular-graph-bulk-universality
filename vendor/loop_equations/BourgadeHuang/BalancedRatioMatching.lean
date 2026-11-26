import BourgadeHuang.EntireRatioExpectation
import BourgadeHuang.CMS.SignCounting

/-! Balanced sign counts give an actual denominator permutation matching
numerator half-planes. Characteristic products are unchanged by that pairing. -/
noncomputable section
open scoped Topology BigOperators
open MeasureTheory
namespace BourgadeHuang

/-- An actual permutation pairs the opposite numerator/denominator branch signs. -/
theorem exists_balanced_signMatching {q : ℕ} (ε η : Fin q → CMS.Sign)
    (hbalance : CMS.signCount ε false = CMS.signCount η true) :
    ∃ p : Equiv.Perm (Fin q), ∀ j, η (p j) = !(ε j) := by
  classical
  let P := fun j : Fin q => ε j = false
  let Q := fun j : Fin q => η j = true
  have hcard : Fintype.card {j // P j} = Fintype.card {j // Q j} := by
    simpa only [Fintype.card_subtype,P,Q,CMS.signCount] using hbalance
  let e₁ : {j // P j} ≃ {j // Q j} := Fintype.equivOfCardEq hcard
  let e₂ : {j // ¬P j} ≃ {j // ¬Q j} := Fintype.equivOfCardEq (by
    simp only [Fintype.card_subtype_compl,hcard])
  let p : Equiv.Perm (Fin q) := (Equiv.sumCompl P).symm.trans
    ((Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl Q))
  refine ⟨p,fun j => ?_⟩
  by_cases hj : P j
  · have he : p j = (e₁ ⟨j,hj⟩).val := by
      simp only [p,Equiv.trans_apply,Equiv.sumCompl_apply_symm_of_pos P j hj,
        Equiv.sumCongr_apply,Sum.map_inl,Equiv.sumCompl_apply_inl]
    rw [he]
    have hη := (e₁ ⟨j,hj⟩).property
    change η (e₁ ⟨j,hj⟩).val = true at hη
    change ε j = false at hj
    simp only [hj,Bool.not_false,hη]
  · have he : p j = (e₂ ⟨j,hj⟩).val := by
      simp only [p,Equiv.trans_apply,Equiv.sumCompl_apply_symm_of_neg P j hj,
        Equiv.sumCongr_apply,Sum.map_inr,Equiv.sumCompl_apply_inr]
    rw [he]
    have hη := (e₂ ⟨j,hj⟩).property
    change η (e₂ ⟨j,hj⟩).val ≠ true at hη
    change ε j ≠ false at hj
    cases hε : ε j <;> cases hη' : η (e₂ ⟨j,hj⟩).val <;> simp_all

/-- The product of genuine entire ratios is independent of denominator pairing. -/
theorem entireCharacteristicRatios_permute_denominators {q : ℕ}
    (s : AnchoredCountingState) (u v : Fin q → ℂ) (p : Equiv.Perm (Fin q)) :
    entireCharacteristicRatios s u (fun j => v (p j)) = entireCharacteristicRatios s u v := by
  unfold entireCharacteristicRatios entireCharacteristicRatio
  rw [Finset.prod_div_distrib,Finset.prod_div_distrib,Equiv.prod_comp p (fun j => anchoredEntireNumerator s (v j))]

theorem entireCharacteristicRatios_permute_numerators {q : ℕ}
    (s : AnchoredCountingState) (u v : Fin q → ℂ) (p : Equiv.Perm (Fin q)) :
    entireCharacteristicRatios s (fun j => u (p j)) v = entireCharacteristicRatios s u v := by
  unfold entireCharacteristicRatios entireCharacteristicRatio
  rw [Finset.prod_div_distrib,Finset.prod_div_distrib,Equiv.prod_comp p (fun j => anchoredEntireNumerator s (u j))]

theorem expectedEntireCharacteristicRatios_permute_denominators {q : ℕ}
    (ν : Measure AnchoredCountingState) (u v : Fin q → ℂ) (p : Equiv.Perm (Fin q)) :
    expectedEntireCharacteristicRatios ν u (fun j => v (p j)) = expectedEntireCharacteristicRatios ν u v := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => entireCharacteristicRatios_permute_denominators s u v p)

theorem expectedEntireCharacteristicRatios_permute_numerators {q : ℕ}
    (ν : Measure AnchoredCountingState) (u v : Fin q → ℂ) (p : Equiv.Perm (Fin q)) :
    expectedEntireCharacteristicRatios ν (fun j => u (p j)) v = expectedEntireCharacteristicRatios ν u v := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => entireCharacteristicRatios_permute_numerators s u v p)

end BourgadeHuang
