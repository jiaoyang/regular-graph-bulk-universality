import GeneralizedBulk.Graph.ProposalMarks
import GeneralizedBulk.Graph.SwitchingProbability

/-! Exact finite conditioning on a uniform graph fiber. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph

/-- Equal-size fibers give the literal finite conditional expectation formula.
No conditional-expectation regularity theorem or independence is assumed. -/
theorem integral_finiteUniform_fibers
    {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (f : α → β) (K : ℕ) (hK : ∀ b, Fintype.card {a // f a = b} = K) (g : α → ℝ) :
    (∫ a, g a ∂finiteUniform α) =
      ∫ b, (∫ a : {a // f a = b}, g a ∂finiteUniform {a // f a = b}) ∂finiteUniform β := by
  have hc : Fintype.card α = Fintype.card β * K := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
    simp only [hK, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  rw [integral_finiteUniform, integral_finiteUniform]
  simp_rw [integral_finiteUniform, hK]
  rw [← Finset.mul_sum, Fintype.sum_fiberwise, hc, Nat.cast_mul, mul_inv_rev]
  ring

theorem integral_finiteUniform_indicator_one
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] (s : Set α) :
    (∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂finiteUniform α) = (finiteUniform α).real s := by
  rw [integral_indicator (Set.toFinite s |>.measurableSet), setIntegral_const]
  simp only [smul_eq_mul, mul_one, measureReal_def]

/-- A fiberwise event probability estimate remains valid after averaging
against any graph event. This is the precise unconditioned-proposal step
needed in the reversible tail argument. -/
theorem finiteUniform_fiber_event_bound
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (f : α → β) (K : ℕ) (hK : 0 < K)
    (hfiber : ∀ b, Fintype.card {a // f a = b} = K)
    (E : Set β) (F : Set α) (q : ℝ)
    (hcond : ∀ b ∈ E, (finiteUniform {a // f a = b}).real {a | (a : α) ∈ F} ≤ q) :
    (finiteUniform α).real {a | f a ∈ E ∧ a ∈ F} ≤ q * (finiteUniform β).real E := by
  letI := finiteUniform_isProbability α
  letI := finiteUniform_isProbability β
  letI (b : β) : Nonempty {a // f a = b} := Fintype.card_pos_iff.mp (by rw [hfiber]; exact hK)
  letI (b : β) := finiteUniform_isProbability {a // f a = b}
  have hE : MeasurableSet E := Set.toFinite E |>.measurableSet
  have hF : MeasurableSet {a : α | f a ∈ E ∧ a ∈ F} := Set.toFinite _ |>.measurableSet
  rw [← integral_finiteUniform_indicator_one ({a : α | f a ∈ E ∧ a ∈ F}), integral_finiteUniform_fibers f K hfiber]
  have hinner (b : β) :
      (∫ a : {a // f a = b}, {a : α | f a ∈ E ∧ a ∈ F}.indicator (fun _ => (1 : ℝ)) a
        ∂finiteUniform {a // f a = b}) =
      E.indicator (fun b => (finiteUniform {a // f a = b}).real {a | (a : α) ∈ F}) b := by
    by_cases hb : b ∈ E
    · rw [Set.indicator_of_mem hb, ← integral_finiteUniform_indicator_one {a : {a // f a = b} | (a : α) ∈ F}]
      apply integral_congr_ae
      filter_upwards [] with a
      simp only [Set.indicator, Set.mem_setOf_eq, a.property, hb, true_and]
    · rw [Set.indicator_of_not_mem hb]
      have heq : (fun a : {a // f a = b} =>
          {a : α | f a ∈ E ∧ a ∈ F}.indicator (fun _ => (1 : ℝ)) a) = fun _ => 0 := by
        funext a
        simp only [Set.indicator, Set.mem_setOf_eq, a.property, hb, false_and, ↓reduceIte]
      rw [heq, integral_zero]
  simp_rw [hinner]
  have hpoint (b : β) :
      E.indicator (fun b => (finiteUniform {a // f a = b}).real {a | (a : α) ∈ F}) b ≤
        q * E.indicator (fun _ => (1 : ℝ)) b := by
    by_cases hb : b ∈ E
    · simpa only [Set.indicator_of_mem hb, mul_one] using hcond b hb
    · simp only [Set.indicator_of_not_mem hb, mul_zero, le_refl]
  calc
    _ ≤ ∫ b, q * E.indicator (fun _ => (1 : ℝ)) b ∂finiteUniform β :=
      integral_mono (integrable_finiteUniform_real _) (integrable_finiteUniform_real _) hpoint
    _ = _ := by rw [integral_const_mul, integral_finiteUniform_indicator_one]

/-- In particular the actual finite graph/proposal law is an average of the
literal uniform conditional graph fibers. -/
theorem integral_edgePairLaw_fibers {N d : ℕ} (g : EdgePairState N d → ℝ) :
    (∫ s, g s ∂edgePairLaw N d) =
      ∫ G, (∫ s : {s : EdgePairState N d // edgePairGraph s = G}, g s
        ∂finiteUniform {s : EdgePairState N d // edgePairGraph s = G}) ∂regularGraphLaw N d := by
  apply integral_finiteUniform_fibers edgePairGraph ((N * d) ^ 2)
  intro G
  rw [Fintype.card_subtype]
  exact edgePairGraph_fiber_card G

end GeneralizedBulk.Graph
