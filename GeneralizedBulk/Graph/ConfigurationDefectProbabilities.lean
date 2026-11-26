import GeneralizedBulk.Graph.PairingTwoEdges
import GeneralizedBulk.Graph.ConfigurationProfiles

/-! Actual loop and repeated-neighbor probabilities under uniform pairings. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration

variable {N d : ℕ} [Nonempty (Pairing (Stub N d))]

theorem rootPartner_probability_le (h : Stub N d) :
    (pairingLaw (Stub N d)).real {p | (p.val h).1 = h.1} ≤
      (d : ℝ) * (((N * d - 1 : ℕ) : ℝ)⁻¹) := by
  letI : IsProbabilityMeasure (pairingLaw (Stub N d)) := pairingLaw_isProbability _
  have heq : {p : Pairing (Stub N d) | (p.val h).1 = h.1} =
      ⋃ j : Fin d, {p | p.val h = (h.1,j)} := by
    ext p
    constructor
    · intro hp
      exact Set.mem_iUnion.mpr ⟨(p.val h).2,Prod.ext hp rfl⟩
    · intro hp
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hp
      change p.val h = (h.1,j) at hj
      have hv := congrArg (fun x : Stub N d => x.1) hj
      exact hv
  rw [heq]
  calc
    _ ≤ ∑ j : Fin d, (pairingLaw (Stub N d)).real {p | p.val h = (h.1,j)} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin d, (((N * d - 1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases he : h = (h.1,j)
      · have hs : {p : Pairing (Stub N d) | p.val h = (h.1,j)} = ∅ := by
          ext p
          simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
          simpa only [← he] using p.property.2 h
        rw [hs,measureReal_empty]
        positivity
      · simpa only [measureReal_def,Fintype.card_prod,Fintype.card_fin] using
          le_of_eq (pairingLaw_partner_probability h (h.1,j) he)
    _ = _ := by simp

abbrev ValidPartnerPair (h k : Stub N d) :=
  {rs : Stub N d × Stub N d // rs.1 ≠ h ∧ rs.1 ≠ k ∧ rs.2 ≠ h ∧ rs.2 ≠ k ∧
    rs.1 ≠ rs.2 ∧ rs.1.1 = rs.2.1}

theorem validPartnerPair_card_le (h k : Stub N d) :
    Fintype.card (ValidPartnerPair h k) ≤ N * d * d := by
  let f : ValidPartnerPair h k → Stub N d × Fin d := fun rs => (rs.val.1,rs.val.2.2)
  have hf : Function.Injective f := by
    intro x y he
    change (x.val.1,x.val.2.2) = (y.val.1,y.val.2.2) at he
    have h1 : x.val.1 = y.val.1 := congrArg (fun z : Stub N d × Fin d => z.1) he
    have h2 : x.val.2.2 = y.val.2.2 := congrArg (fun z : Stub N d × Fin d => z.2) he
    apply Subtype.ext
    apply Prod.ext h1
    apply Prod.ext _ h2
    exact x.property.2.2.2.2.2.symm.trans ((congrArg Prod.fst h1).trans y.property.2.2.2.2.2)
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective f hf

set_option maxHeartbeats 1000000 in
theorem partnerRoots_probability_le (h k : Stub N d) (hk : h ≠ k) :
    (pairingLaw (Stub N d)).real {p | (p.val h).1 = (p.val k).1} ≤
      (((N * d - 1 : ℕ) : ℝ)⁻¹) + (N * d * d : ℕ) *
        ((((N * d - 1) * (N * d - 3) : ℕ) : ℝ)⁻¹) := by
  letI : IsProbabilityMeasure (pairingLaw (Stub N d)) := pairingLaw_isProbability _
  let E : ValidPartnerPair h k → Set (Pairing (Stub N d)) :=
    fun rs => {p | p.val h = rs.val.1 ∧ p.val k = rs.val.2}
  have hsub : {p : Pairing (Stub N d) | (p.val h).1 = (p.val k).1} ⊆
      {p | p.val h = k} ∪ ⋃ rs : ValidPartnerPair h k, E rs := by
    intro p hp
    by_cases hpk : p.val h = k
    · exact Or.inl hpk
    right
    have hph : p.val k ≠ h := by
      intro he
      have hh := congrArg p.val he
      rw [p.property.1 k] at hh
      exact hpk hh.symm
    let rs : ValidPartnerPair h k := ⟨(p.val h,p.val k),p.property.2 h,hpk,hph,
      p.property.2 k,fun he => hk (p.val.injective he),hp⟩
    exact Set.mem_iUnion.mpr ⟨rs,rfl,rfl⟩
  have hE (rs : ValidPartnerPair h k) :
      (pairingLaw (Stub N d)).real (E rs) =
        ((((N * d - 1) * (N * d - 3) : ℕ) : ℝ)⁻¹) := by
    simpa only [E,measureReal_def,Fintype.card_prod,Fintype.card_fin] using
      pairingLaw_two_partner_probability h rs.val.1 k rs.val.2
        rs.property.1.symm hk.symm rs.property.2.1.symm rs.property.2.2.1
        rs.property.2.2.2.2.1.symm rs.property.2.2.2.1.symm
  calc
    _ ≤ (pairingLaw (Stub N d)).real ({p | p.val h = k} ∪ ⋃ rs : ValidPartnerPair h k, E rs) :=
      measureReal_mono hsub
    _ ≤ (pairingLaw (Stub N d)).real {p | p.val h = k} +
        (pairingLaw (Stub N d)).real (⋃ rs : ValidPartnerPair h k, E rs) := measureReal_union_le _ _
    _ ≤ (((N * d - 1 : ℕ) : ℝ)⁻¹) +
        ∑ rs : ValidPartnerPair h k, (pairingLaw (Stub N d)).real (E rs) := by
      apply add_le_add
      · simpa only [measureReal_def,Fintype.card_prod,Fintype.card_fin] using
          le_of_eq (pairingLaw_partner_probability h k hk)
      · exact measureReal_iUnion_fintype_le _
    _ = (((N * d - 1 : ℕ) : ℝ)⁻¹) + (Fintype.card (ValidPartnerPair h k) : ℝ) *
        ((((N * d - 1) * (N * d - 3) : ℕ) : ℝ)⁻¹) := by simp_rw [hE]; simp
    _ ≤ _ := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast validPartnerPair_card_le h k

end GeneralizedBulk.Graph.Configuration
