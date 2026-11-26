import GaussianWave.BS.Reused.Graph.ConfigurationUniform

/-!
# Literal conditioning of the pairing law on simplicity

The finite uniform simple-configuration law is proved to be the uniform
pairing law conditioned on the actual loop/multiple-edge-free event. Its
projected graph law is therefore exactly the uniform regular graph law.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS.Reused.Graph

theorem finiteUniform_finset_apply
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] (s : Finset α) :
    finiteUniform α (s : Set α) = (s.card : ENNReal) / Fintype.card α := by
  have hsum : (∑ x : α, (s : Set α).indicator (1 : α → ENNReal) x) = (s.card : ENNReal) := by
    simp [Set.indicator, ← Finset.sum_filter]
  simp [finiteUniform, Measure.smul_apply, Finset.sum_apply, Measure.dirac_apply',
    hsum, div_eq_mul_inv, mul_comm]

theorem finiteUniform_set_apply
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] (s : Set α) :
    finiteUniform α s = (Fintype.card s : ENNReal) / Fintype.card α := by
  calc
    _ = finiteUniform α (s.toFinite.toFinset : Set α) :=
      congrArg (finiteUniform α) (Set.Finite.coe_toFinset s.toFinite).symm
    _ = (s.toFinite.toFinset.card : ENNReal) / Fintype.card α := finiteUniform_finset_apply _
    _ = _ := by rw [s.toFinite.card_toFinset]

theorem finiteUniform_singleton_apply
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) :
    finiteUniform α {a} = (Fintype.card α : ENNReal)⁻¹ := by
  rw [← Finset.coe_singleton, finiteUniform_finset_apply]
  simp

/-- Uniform sampling on a nonempty finite subtype is exactly conditional
uniform sampling on its underlying event. -/
theorem finiteUniform_subtype_condition
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (s : Set α) [Nonempty s] :
    Measure.map (Subtype.val : s → α) (finiteUniform s) = ProbabilityTheory.cond (finiteUniform α) s := by
  letI : Nonempty α := ⟨(Classical.choice (inferInstance : Nonempty s)).val⟩
  have hα0 : (Fintype.card α : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hαtop : (Fintype.card α : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton a),
    ProbabilityTheory.cond_apply (Set.toFinite s |>.measurableSet)]
  by_cases ha : a ∈ s
  · have hpre : (Subtype.val : s → α) ⁻¹' {a} = {⟨a,ha⟩} := by
      ext b
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
    have hsingle : s ∩ {a} = {a} := by ext b; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]; aesop
    rw [hpre, finiteUniform_singleton_apply, hsingle,
      finiteUniform_set_apply, finiteUniform_singleton_apply,
      ENNReal.inv_div (Or.inl hαtop) (Or.inl hα0)]
    simp only [div_eq_mul_inv]
    symm
    calc
      _ = (Fintype.card s : ENNReal)⁻¹ *
          ((Fintype.card α : ENNReal)⁻¹ * Fintype.card α) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel hα0 hαtop, mul_one]
  · have hpre : (Subtype.val : s → α) ⁻¹' {a} = ∅ := by
      ext b
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact ha (h ▸ b.property)
    rw [hpre, measure_empty, (Set.inter_singleton_eq_empty.mpr ha), measure_empty, mul_zero]

end GaussianWave.BS.Reused.Graph

namespace GaussianWave.BS.Reused.Graph.Configuration

/-- The actual simple pairing sampler is the pairing law conditioned on
simplicity, not a separately stipulated probability kernel. -/
theorem simpleConfigurationLaw_eq_conditioned_pairing (N d : ℕ) [Nonempty (RegularGraph N d)] :
    Measure.map (Subtype.val : SimplePairing N d → Pairing (Fin N × Fin d)) (simpleConfigurationLaw N d) =
      ProbabilityTheory.cond (pairingLaw (Fin N × Fin d)) {p | SimpleConfiguration p} := by
  exact @finiteUniform_subtype_condition (Pairing (Fin N × Fin d)) _ _ _
    {p | SimpleConfiguration p} (simplePairing_nonempty N d)

/-- A total projection, with an irrelevant fallback outside the simple
event, lets the conditional graph law be stated directly on pairings. -/
def configurationProjection (N d : ℕ) [Nonempty (RegularGraph N d)]
    (p : Pairing (Fin N × Fin d)) : RegularGraph N d :=
  if hp : SimpleConfiguration p then configurationGraph p hp else Classical.choice inferInstance

/-- Conditioning the actual half-edge pairing model on being simple gives
exactly the uniform labeled simple regular graph. -/
theorem conditioned_pairing_graph_law (N d : ℕ) [Nonempty (RegularGraph N d)] :
    Measure.map (configurationProjection N d)
      (ProbabilityTheory.cond (pairingLaw (Fin N × Fin d)) {p | SimpleConfiguration p}) =
        regularGraphLaw N d := by
  rw [← simpleConfigurationLaw_eq_conditioned_pairing N d,
    Measure.map_map (measurable_of_finite _) measurable_subtype_coe]
  have hcomp : configurationProjection N d ∘ (Subtype.val : SimplePairing N d → Pairing (Fin N × Fin d)) =
      simpleConfigurationGraph := by
    funext p
    exact dif_pos p.property
  rw [hcomp]
  exact simpleConfigurationLaw_graph_marginal N d

/-- The exact simplicity probability exposes the port-label multiplicity
needed by configuration counting and the simplicity lower bound. -/
theorem pairingLaw_simple_probability (N d : ℕ) :
    (pairingLaw (Fin N × Fin d) {p | SimpleConfiguration p}).toReal =
      ((Fintype.card (RegularGraph N d) : ℝ) * (Nat.factorial d : ℝ) ^ N) /
        Fintype.card (Pairing (Fin N × Fin d)) := by
  rw [pairingLaw, finiteUniform_set_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  change (Fintype.card (SimplePairing N d) : ℝ) / _ = _
  rw [simplePairing_card, Nat.cast_mul, Nat.cast_pow]

theorem pairingLaw_simple_ne_zero (N d : ℕ) [Nonempty (RegularGraph N d)] :
    pairingLaw (Fin N × Fin d) {p | SimpleConfiguration p} ≠ 0 := by
  rw [pairingLaw, finiteUniform_set_apply, ENNReal.div_ne_zero]
  constructor
  · have hc : Fintype.card (SimplePairing N d) ≠ 0 := by
      letI := simplePairing_nonempty N d
      exact Fintype.card_ne_zero
    change (Fintype.card (SimplePairing N d) : ENNReal) ≠ 0
    exact_mod_cast hc
  · exact ENNReal.natCast_ne_top _

/-- An event counted in the unrestricted configuration model bounds a
uniform graph event after division only by the actual simplicity probability. -/
theorem regularGraphLaw_event_le_pairing_event_div_simple
    (N d : ℕ) [Nonempty (RegularGraph N d)]
    (E : Set (RegularGraph N d)) (F : Set (Pairing (Fin N × Fin d)))
    (hF : ∀ p (hp : SimpleConfiguration p), configurationGraph p hp ∈ E → p ∈ F) :
    regularGraphLaw N d E ≤ pairingLaw (Fin N × Fin d) F /
      pairingLaw (Fin N × Fin d) {p | SimpleConfiguration p} := by
  have hsub : {p | SimpleConfiguration p} ∩ configurationProjection N d ⁻¹' E ⊆ F := by
    intro p hp
    apply hF p hp.1
    have hm := hp.2
    change configurationProjection N d p ∈ E at hm
    have hsimple : SimpleConfiguration p := hp.1
    simpa only [configurationProjection, dif_pos hsimple] using hm
  calc
    _ = (Measure.map (configurationProjection N d)
        (ProbabilityTheory.cond (pairingLaw (Fin N × Fin d)) {p | SimpleConfiguration p})) E := by
      rw [conditioned_pairing_graph_law]
    _ = (ProbabilityTheory.cond (pairingLaw (Fin N × Fin d)) {p | SimpleConfiguration p})
        (configurationProjection N d ⁻¹' E) :=
      Measure.map_apply (measurable_of_finite _) (Set.toFinite E |>.measurableSet)
    _ = (pairingLaw (Fin N × Fin d) {p | SimpleConfiguration p})⁻¹ *
        pairingLaw (Fin N × Fin d) ({p | SimpleConfiguration p} ∩ configurationProjection N d ⁻¹' E) :=
      ProbabilityTheory.cond_apply (Set.toFinite _ |>.measurableSet) _ _
    _ ≤ (pairingLaw (Fin N × Fin d) {p | SimpleConfiguration p})⁻¹ * pairingLaw (Fin N × Fin d) F :=
      mul_le_mul_left' (measure_mono hsub) _
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- The same exact configuration-to-graph bound in real probabilities. -/
theorem regularGraphLaw_real_event_le_pairing_event_div_simple
    (N d : ℕ) [Nonempty (RegularGraph N d)]
    (E : Set (RegularGraph N d)) (F : Set (Pairing (Fin N × Fin d)))
    (hF : ∀ p (hp : SimpleConfiguration p), configurationGraph p hp ∈ E → p ∈ F) :
    (regularGraphLaw N d).real E ≤ (pairingLaw (Fin N × Fin d)).real F /
      (pairingLaw (Fin N × Fin d)).real {p | SimpleConfiguration p} := by
  letI : Nonempty (Pairing (Fin N × Fin d)) :=
    ⟨(Classical.choice (simplePairing_nonempty N d)).val⟩
  letI := pairingLaw_isProbability (Fin N × Fin d)
  have hfinite := (ENNReal.div_lt_top (measure_ne_top (pairingLaw (Fin N × Fin d)) F)
    (pairingLaw_simple_ne_zero N d)).ne
  have h := ENNReal.toReal_mono hfinite
    (regularGraphLaw_event_le_pairing_event_div_simple N d E F hF)
  simpa only [measureReal_def, ENNReal.toReal_div] using h

end GaussianWave.BS.Reused.Graph.Configuration
