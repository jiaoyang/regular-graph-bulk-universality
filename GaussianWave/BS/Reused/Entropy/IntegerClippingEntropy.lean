import GaussianWave.BS.Reused.Entropy.CountableTailSplit
import GaussianWave.BS.Reused.Entropy.ClippedQuantizer

/-! Actual clipping entropy loss for arbitrary correlated integer-vector
laws. The reference constant grows linearly with the vector dimension. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Entropy

def clipIntegerVector {m : ℕ} (K : ℕ) (j : Fin m → ℤ) (i : Fin m) : ℤ := clipInteger K (j i)

def integerClippingTail {m : ℕ} (K : ℕ) (j : Fin m → ℤ) : Prop :=
  ∃ i,j i < -(K : ℤ) ∨ (K : ℤ) ≤ j i

theorem clipIntegerVector_eq_self_off_tail {m : ℕ} (K : ℕ) (j : Fin m → ℤ)
    (hj : ¬ integerClippingTail K j) : clipIntegerVector K j = j := by
  funext i
  apply clipInteger_eq_self
  · by_contra hi
    exact hj ⟨i,Or.inl (lt_of_not_ge hi)⟩
  · by_contra hi
    exact hj ⟨i,Or.inr (by omega)⟩

theorem integerEnergy_nonneg {m : ℕ} (j : Fin m → ℤ) : 0 ≤ integerEnergy j :=
  Finset.sum_nonneg (fun i hi => abs_nonneg _)

set_option maxHeartbeats 1000000 in
theorem global_integer_clipping_entropy_bound {m : ℕ} (p : (Fin m → ℤ) → ℝ)
    (hp : ∀ j,0 ≤ p j) (hs : HasSum p 1)
    (hmoment : Summable (fun j => p j*integerEnergy j)) (K : ℕ) :
    countableEntropy p-countableEntropy (countablePush p (clipIntegerVector K)) ≤
      Real.binEntropy (tailMass p (integerClippingTail K))+
        tailMass p (integerClippingTail K)*linearIntegerEntropyConstant m+
          (∑' j,restrictedMass p (integerClippingTail K) j*integerEnergy j) := by
  have hH := summable_integer_entropy p hp hs hmoment
  have hpure := countable_clipping_loss_le_tail p hp hs hH (integerClippingTail K) (clipIntegerVector K)
    (clipIntegerVector_eq_self_off_tail K)
  have htailMom : Summable (fun j => restrictedMass p (integerClippingTail K) j*integerEnergy j) := by
    apply Summable.of_nonneg_of_le
      (fun j => mul_nonneg (restrictedMass_nonneg p hp _ j) (integerEnergy_nonneg j)) _ hmoment
    intro j
    unfold restrictedMass
    split_ifs
    · rfl
    · exact (by simpa only [zero_mul] using mul_nonneg (hp j) (integerEnergy_nonneg j))
  have henergy := subprob_integer_entropy_energy_bound (restrictedMass p (integerClippingTail K))
    (restrictedMass_nonneg p hp _) (tailMass p (integerClippingTail K))
    (tailMass_nonneg p hp _) (summable_restrictedMass p hp hs.summable _).hasSum htailMom
  linarith

def codedClipIntegerVector {m : ℕ} (K : ℕ) (hK : 0 < K) (j : Fin m → ℤ) (i : Fin m) : Fin (2*K) :=
  clipLabelEquivFin K (clipLabel K hK (j i))

def decodeClipIntegerVector {m : ℕ} (K : ℕ) (j : Fin m → Fin (2*K)) (i : Fin m) : ℤ :=
  ((clipLabelEquivFin K).symm (j i)).val

theorem codedClip_decode_leftInverse {m : ℕ} (K : ℕ) (hK : 0 < K) :
    Function.LeftInverse (codedClipIntegerVector (m := m) K hK) (decodeClipIntegerVector K) := by
  intro j
  funext i
  have hbox := Finset.mem_Icc.mp ((clipLabelEquivFin K).symm (j i)).property
  have he : clipLabel K hK (((clipLabelEquivFin K).symm (j i)).val) = (clipLabelEquivFin K).symm (j i) :=
    Subtype.ext (clipInteger_eq_self K _ hbox.1 hbox.2)
  change clipLabelEquivFin K (clipLabel K hK (((clipLabelEquivFin K).symm (j i)).val)) = j i
  rw [he,Equiv.apply_symm_apply]

theorem decode_codedClip_eq_raw {m : ℕ} (K : ℕ) (hK : 0 < K) :
    decodeClipIntegerVector (m := m) K ∘ codedClipIntegerVector K hK = clipIntegerVector K := by
  funext j i
  simp only [Function.comp_apply,decodeClipIntegerVector,codedClipIntegerVector,Equiv.symm_apply_apply]
  rfl

theorem countableEntropy_codedClip_eq_raw {m : ℕ} (p : (Fin m → ℤ) → ℝ)
    (hp : ∀ j,0 ≤ p j) (hs : HasSum p 1)
    (hH : Summable (fun j => Real.negMulLog (p j))) (K : ℕ) (hK : 0 < K) :
    countableEntropy (countablePush p (codedClipIntegerVector K hK)) =
      countableEntropy (countablePush p (clipIntegerVector K)) := by
  have h := countableEntropy_push_eq_of_leftInverse (countablePush p (codedClipIntegerVector K hK))
    (countablePush_nonneg p hp _) (countablePush_hasSum p hs _)
    (summable_entropy_countablePush p hp hs hH _) (decodeClipIntegerVector K) (codedClipIntegerVector K hK)
    (codedClip_decode_leftInverse K hK)
  rw [countablePush_comp p hs.summable,decode_codedClip_eq_raw] at h
  exact h.symm

theorem coded_integer_clipping_entropy_bound {m : ℕ} (p : (Fin m → ℤ) → ℝ)
    (hp : ∀ j,0 ≤ p j) (hs : HasSum p 1)
    (hmoment : Summable (fun j => p j*integerEnergy j)) (K : ℕ) (hK : 0 < K) :
    countableEntropy p-countableEntropy (countablePush p (codedClipIntegerVector K hK)) ≤
      Real.binEntropy (tailMass p (integerClippingTail K))+
        tailMass p (integerClippingTail K)*linearIntegerEntropyConstant m+
          (∑' j,restrictedMass p (integerClippingTail K) j*integerEnergy j) := by
  rw [countableEntropy_codedClip_eq_raw p hp hs (summable_integer_entropy p hp hs hmoment)]
  exact global_integer_clipping_entropy_bound p hp hs hmoment K

end GaussianWave.BS.Reused.Entropy
