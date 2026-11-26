import BourgadeHuang.NevanlinnaLoop

/-! Polynomial growth bounds for all reconstructed loop observables. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- Polynomial growth measured by the single complex anchor. -/
def AnchoredGrowth (F : AnchoredCountingState → ℂ) (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ‖F s‖ ≤ C * (1 + ‖s.val.2‖) ^ d

namespace AnchoredGrowth

theorem const (c : ℂ) : AnchoredGrowth (fun _ => c) 0 :=
  ⟨‖c‖, norm_nonneg _, fun _ => by simp⟩

theorem of_linear_bound {F : AnchoredCountingState → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ s, ‖F s‖ ≤ C * ‖s.val.2‖) : AnchoredGrowth F 1 :=
  ⟨C, hC, fun s => (hb s).trans (by simp only [pow_one]; nlinarith)⟩

theorem add {F G : AnchoredCountingState → ℂ} {d : ℕ}
    (hF : AnchoredGrowth F d) (hG : AnchoredGrowth G d) :
    AnchoredGrowth (fun s => F s + G s) d := by
  obtain ⟨C, hC, hb⟩ := hF
  obtain ⟨D, hD, hd⟩ := hG
  refine ⟨C + D, add_nonneg hC hD, fun s => ?_⟩
  exact (norm_add_le _ _).trans ((add_le_add (hb s) (hd s)).trans_eq (by ring))

theorem neg {F : AnchoredCountingState → ℂ} {d : ℕ} (hF : AnchoredGrowth F d) :
    AnchoredGrowth (fun s => -F s) d := by
  simpa only [AnchoredGrowth, norm_neg] using hF

theorem sub {F G : AnchoredCountingState → ℂ} {d : ℕ}
    (hF : AnchoredGrowth F d) (hG : AnchoredGrowth G d) :
    AnchoredGrowth (fun s => F s - G s) d := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem mul {F G : AnchoredCountingState → ℂ} {d e : ℕ}
    (hF : AnchoredGrowth F d) (hG : AnchoredGrowth G e) :
    AnchoredGrowth (fun s => F s * G s) (d + e) := by
  obtain ⟨C, hC, hb⟩ := hF
  obtain ⟨D, hD, hd⟩ := hG
  refine ⟨C * D, mul_nonneg hC hD, fun s => ?_⟩
  rw [norm_mul]
  exact (mul_le_mul (hb s) (hd s) (norm_nonneg _) (by positivity)).trans_eq
    (by rw [pow_add]; ring)

theorem mono {F : AnchoredCountingState → ℂ} {d e : ℕ}
    (hF : AnchoredGrowth F d) (hde : d ≤ e) : AnchoredGrowth F e := by
  obtain ⟨C, hC, hb⟩ := hF
  refine ⟨C, hC, fun s => (hb s).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [norm_nonneg s.val.2]) hde) hC

theorem const_mul {F : AnchoredCountingState → ℂ} {d : ℕ}
    (c : ℂ) (hF : AnchoredGrowth F d) : AnchoredGrowth (fun s => c * F s) d := by
  simpa only [zero_add] using (const c).mul hF

theorem div_const {F : AnchoredCountingState → ℂ} {d : ℕ}
    (hF : AnchoredGrowth F d) (c : ℂ) : AnchoredGrowth (fun s => F s / c) d := by
  simpa only [div_eq_mul_inv, mul_comm] using const_mul c⁻¹ hF

theorem finset_sum {ι : Type*} (t : Finset ι) (F : ι → AnchoredCountingState → ℂ) {d : ℕ}
    (hF : ∀ i ∈ t, AnchoredGrowth (F i) d) :
    AnchoredGrowth (fun s => ∑ i ∈ t, F i s) d := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (const 0).mono (Nat.zero_le d)
  | @insert a t ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hF a (Finset.mem_insert_self a t)).add (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

theorem finset_prod {ι : Type*} (t : Finset ι) (F : ι → AnchoredCountingState → ℂ)
    (hF : ∀ i ∈ t, AnchoredGrowth (F i) 1) :
    AnchoredGrowth (fun s => ∏ i ∈ t, F i s) t.card := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.card_empty] using const 1
  | @insert a t ha ih =>
    simpa only [Finset.prod_insert ha, Finset.card_insert_of_not_mem ha, Nat.add_comm 1] using
      (hF a (Finset.mem_insert_self a t)).mul (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

end AnchoredGrowth

theorem anchoredGrowth_nevanlinna {z : ℂ} (hz : z.im ≠ 0) :
    AnchoredGrowth (fun s => anchoredNevanlinna s z) 1 :=
  AnchoredGrowth.of_linear_bound (by positivity) (fun s => norm_anchoredNevanlinna_le_anchor s hz)

theorem anchoredGrowth_powerIntegral (q : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    AnchoredGrowth (fun s => anchoredPowerIntegral q s z) 1 :=
  AnchoredGrowth.of_linear_bound (by positivity) (fun s => norm_anchoredPowerIntegral_le q s hz)

theorem anchoredGrowth_derivative {z : ℂ} (hz : z.im ≠ 0) :
    AnchoredGrowth (fun s => anchoredDerivative s z) 1 := by
  have him : AnchoredGrowth (fun s => (s.val.2.im : ℂ)) 1 :=
    AnchoredGrowth.of_linear_bound (by norm_num : (0 : ℝ) ≤ 1) (fun s => by
      simp only [one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact Complex.abs_im_le_norm _)
  exact (him.add (AnchoredGrowth.const_mul _ (anchoredGrowth_powerIntegral 0 hz))).add
    (AnchoredGrowth.const_mul _ (anchoredGrowth_powerIntegral 1 hz))

theorem anchoredGrowth_secondHalf {z : ℂ} (hz : z.im ≠ 0) :
    AnchoredGrowth (fun s => anchoredSecondHalf s z) 1 :=
  ((anchoredGrowth_powerIntegral 0 hz).add
    (AnchoredGrowth.const_mul _ (anchoredGrowth_powerIntegral 1 hz))).add
    (AnchoredGrowth.const_mul _ (anchoredGrowth_powerIntegral 2 hz))

theorem anchoredGrowth_interaction {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    AnchoredGrowth (fun s => anchoredInteraction s w v) 1 := by
  unfold anchoredInteraction
  split_ifs
  · exact anchoredGrowth_secondHalf hw
  · exact (((anchoredGrowth_nevanlinna hw).sub (anchoredGrowth_nevanlinna hv)).sub
      (AnchoredGrowth.const_mul _ (anchoredGrowth_derivative hv))).div_const _

/-- All parameters may repeat: the bound has degree `n+2` and uses only the anchor. -/
theorem anchoredGrowth_loopIntegrand {n : ℕ} (β : Beta) {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (haux : ∀ a, (aux a).im ≠ 0) :
    AnchoredGrowth (fun s => anchoredLoopIntegrand β s w aux) (n + 2) := by
  have hhead : AnchoredGrowth (fun s =>
      ((2 - β.value) / β.value) * anchoredDerivative s w + anchoredNevanlinna s w ^ 2 + 1) 2 := by
    have hs := (anchoredGrowth_nevanlinna hw).mul (anchoredGrowth_nevanlinna hw)
    simp only [← pow_two] at hs
    exact (((AnchoredGrowth.const_mul _ (anchoredGrowth_derivative hw)).mono (by omega)).add hs).add
      ((AnchoredGrowth.const 1).mono (by omega))
  have hp : AnchoredGrowth (fun s => ∏ a, anchoredNevanlinna s (aux a)) n := by
    simpa using AnchoredGrowth.finset_prod Finset.univ (fun a s => anchoredNevanlinna s (aux a))
      (fun a _ => anchoredGrowth_nevanlinna (haux a))
  have he (a : Fin n) : AnchoredGrowth
      (fun s => excludedProduct (fun b => anchoredNevanlinna s (aux b)) a) n := by
    exact (AnchoredGrowth.finset_prod (Finset.univ.erase a) (fun b s => anchoredNevanlinna s (aux b))
      (fun b _ => anchoredGrowth_nevanlinna (haux b))).mono
        ((Finset.card_erase_le).trans (by simp))
  have hsum : AnchoredGrowth (fun s => ∑ a, anchoredInteraction s w (aux a) *
      excludedProduct (fun b => anchoredNevanlinna s (aux b)) a) (n + 2) := by
    apply AnchoredGrowth.finset_sum
    intro a _
    exact ((anchoredGrowth_interaction hw (haux a)).mul (he a)).mono (by omega)
  have hmain : AnchoredGrowth (fun s =>
      (((2 - β.value) / β.value) * anchoredDerivative s w + anchoredNevanlinna s w ^ 2 + 1) *
        ∏ a, anchoredNevanlinna s (aux a)) (n + 2) := by
    simpa only [Nat.add_comm 2] using hhead.mul hp
  exact hmain.add (AnchoredGrowth.const_mul _ hsum)

end BourgadeHuang
