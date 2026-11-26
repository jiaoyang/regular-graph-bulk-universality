import GeneralizedBulk.Graph.ConfigurationDefects
import GeneralizedBulk.Graph.ConfigurationDefectProbabilities
import GeneralizedBulk.Graph.ProfileUniform

/-! A degree-uniform first moment for the actual number of defective stubs. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration

variable {N d : ℕ} [Nonempty (Pairing (Stub N d))]

theorem defect_le_witness_sum (p : Pairing (Stub N d)) :
    (defect p : ℝ) ≤ ∑ h : Stub N d,
      ((if (p.val h).1 = h.1 then (1 : ℝ) else 0) +
        ∑ j : Fin d, if Parallel p h (h.1,j) then (1 : ℝ) else 0) := by
  have he : (defect p : ℝ) = ∑ h : Stub N d, if BadStub p h then (1 : ℝ) else 0 := by
    simp only [defect,badStubs,Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum,
      Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [he]
  apply Finset.sum_le_sum
  intro h hh
  have hnn : 0 ≤ ∑ j : Fin d, if Parallel p h (h.1,j) then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun j hj => by split_ifs <;> norm_num)
  by_cases hl : (p.val h).1 = h.1
  · simp only [if_pos hl,if_pos (show BadStub p h from Or.inl hl)]
    linarith
  · by_cases hb : BadStub p h
    · obtain ⟨k,hk⟩ := hb.resolve_left hl
      have hp : Parallel p h (h.1,k.2) := by
        have he : k = (h.1,k.2) := Prod.ext hk.1.symm rfl
        simpa only [← he] using hk
      have hs := Finset.single_le_sum (f := fun j : Fin d => if Parallel p h (h.1,j) then (1 : ℝ) else 0)
        (fun j hj => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ k.2)
      simp only [if_pos hp] at hs
      simpa only [if_pos hb,if_neg hl,zero_add] using hs
    · simp only [if_neg hb,if_neg hl,zero_add]
      exact hnn

theorem integral_indicator_one_pairing (R : Pairing (Stub N d) → Prop) [DecidablePred R] :
    (∫ p, (if R p then (1 : ℝ) else 0) ∂pairingLaw (Stub N d)) =
      (pairingLaw (Stub N d)).real {p | R p} := by
  simpa only [Set.indicator,Set.mem_setOf_eq,Pi.one_apply] using
    (integral_indicator_one (μ := pairingLaw (Stub N d)) (show MeasurableSet {p | R p} from trivial))

set_option maxHeartbeats 1000000 in
theorem integral_defect_le_rational :
    (∫ p, (defect p : ℝ) ∂pairingLaw (Stub N d)) ≤
      (N * d : ℕ) * ((d : ℝ) * (((N * d - 1 : ℕ) : ℝ)⁻¹) +
        d * ((((N * d - 1 : ℕ) : ℝ)⁻¹) + (N * d * d : ℕ) *
          ((((N * d - 1) * (N * d - 3) : ℕ) : ℝ)⁻¹))) := by
  letI : IsProbabilityMeasure (pairingLaw (Stub N d)) := pairingLaw_isProbability _
  apply (integral_mono (integrable_pairingLaw_real _) (integrable_pairingLaw_real _)
    defect_le_witness_sum).trans
  rw [integral_finset_sum _ (fun h hh => integrable_pairingLaw_real _)]
  calc
    _ ≤ ∑ _h : Stub N d,
        ((d : ℝ) * (((N * d - 1 : ℕ) : ℝ)⁻¹) +
          d * ((((N * d - 1 : ℕ) : ℝ)⁻¹) + (N * d * d : ℕ) *
            ((((N * d - 1) * (N * d - 3) : ℕ) : ℝ)⁻¹))) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [integral_add (integrable_pairingLaw_real _) (integrable_pairingLaw_real _),
        integral_finset_sum _ (fun j hj => integrable_pairingLaw_real _),
        integral_indicator_one_pairing (fun p => (p.val h).1 = h.1)]
      apply add_le_add (rootPartner_probability_le h)
      calc
        _ ≤ ∑ _j : Fin d, ((((N * d - 1 : ℕ) : ℝ)⁻¹) + (N * d * d : ℕ) *
            ((((N * d - 1) * (N * d - 3) : ℕ) : ℝ)⁻¹)) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [integral_indicator_one_pairing (fun p => Parallel p h (h.1,j))]
          by_cases he : h = (h.1,j)
          · have hs : {p : Pairing (Stub N d) | Parallel p h (h.1,j)} = ∅ := by
              ext p; simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
              intro hp; exact hp.2.1 he
            rw [hs,measureReal_empty]
            positivity
          · apply (measureReal_mono (μ := pairingLaw (Stub N d))
              (show {p | Parallel p h (h.1,j)} ⊆ {p | (p.val h).1 = (p.val (h.1,j)).1} from fun p hp => hp.2.2)).trans
            exact partnerRoots_probability_le h (h.1,j) he
        _ = _ := by simp; ring
    _ = _ := by simp [Fintype.card_prod,Fintype.card_fin]; ring

set_option maxHeartbeats 1000000 in
theorem integral_defect_le_degree_bound (hL : 6 ≤ N * d) :
    (∫ p, (defect p : ℝ) ∂pairingLaw (Stub N d)) ≤ 4 * d + 4 * (d : ℝ) ^ 2 := by
  apply integral_defect_le_rational.trans
  have hL1 : 1 ≤ N * d := by omega
  have hL3 : 3 ≤ N * d := by omega
  have hR : (6 : ℝ) ≤ (N * d : ℕ) := by exact_mod_cast hL
  have h1 : (0 : ℝ) < (N * d : ℕ) - 1 := by linarith
  have h3 : (0 : ℝ) < (N * d : ℕ) - 3 := by linarith
  have hA : (N * d : ℕ) * (((N * d : ℕ) : ℝ) - 1)⁻¹ ≤ 2 := by
    rw [← div_eq_mul_inv,div_le_iff₀ h1]
    linarith
  have hB : ((N * d : ℕ) : ℝ) ^ 2 *
      ((((N * d : ℕ) : ℝ) - 1) * (((N * d : ℕ) : ℝ) - 3))⁻¹ ≤ 4 := by
    rw [← div_eq_mul_inv,div_le_iff₀ (mul_pos h1 h3)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (show (0 : ℝ) ≤ (N * d : ℕ) from by positivity)]
  simp only [Nat.cast_mul,Nat.cast_sub hL1,Nat.cast_sub hL3,Nat.cast_ofNat,Nat.cast_one,mul_inv_rev]
  push_cast at hA hB
  simp only [mul_inv_rev] at hB
  have hd : (0 : ℝ) ≤ d := by positivity
  have hAA := mul_le_mul_of_nonneg_right hA hd
  have hBB := mul_le_mul_of_nonneg_right hB (sq_nonneg (d : ℝ))
  nlinarith

end GeneralizedBulk.Graph.Configuration
