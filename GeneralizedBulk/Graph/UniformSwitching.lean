import Mathlib

/-!
# Concrete finite regular-graph switching

The graph sample space is the actual finite set of labeled simple regular
graphs. Accepted switches toggle the alternating four-cycle and exchange the
two proposed endpoint partners. Their finite uniform law is therefore handled
by an explicit involution, independently of BS and HY.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators symmDiff Classical

namespace GeneralizedBulk.Graph

def finiteUniform (α : Type*) [Fintype α] [MeasurableSpace α] : Measure α :=
  (Fintype.card α : ENNReal)⁻¹ • ∑ a : α, Measure.dirac a

theorem finiteUniform_isProbability (α : Type*) [Fintype α] [Nonempty α]
    [MeasurableSpace α] : IsProbabilityMeasure (finiteUniform α) := by
  constructor
  simp [finiteUniform, Measure.smul_apply, Finset.sum_apply]
  apply ENNReal.inv_mul_cancel
  · exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
  · exact ENNReal.natCast_ne_top _

theorem finiteUniform_equiv_invariant {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (e : α ≃ α) :
    Measure.map e (finiteUniform α) = finiteUniform α := by
  have hm : Measurable e := measurable_of_finite _
  rw [finiteUniform, ← Measure.mapₗ_apply_of_measurable hm, map_smul, map_sum]
  simp only [Measure.mapₗ_apply_of_measurable hm, Measure.map_dirac hm]
  congr 1
  exact Equiv.sum_comp e Measure.dirac

def RegularGraph (N d : ℕ) := {G : SimpleGraph (Fin N) // G.IsRegularOfDegree d}

instance (N d : ℕ) : Fintype (RegularGraph N d) := by
  classical
  unfold RegularGraph
  infer_instance

instance (N d : ℕ) : MeasurableSpace (RegularGraph N d) := ⊤
instance (N d : ℕ) : MeasurableSingletonClass (RegularGraph N d) := ⟨fun _ => trivial⟩

def regularGraphLaw (N d : ℕ) : Measure (RegularGraph N d) := finiteUniform _

theorem regularGraphLaw_isProbability (N d : ℕ) [Nonempty (RegularGraph N d)] :
    IsProbabilityMeasure (regularGraphLaw N d) := finiteUniform_isProbability _

def oldPartner : Fin 4 → Fin 4 := ![1, 0, 3, 2]
def newPartner : Fin 4 → Fin 4 := ![3, 2, 1, 0]
def swapPartners : Equiv.Perm (Fin 4) := Equiv.swap 1 3

def cycleRelation {V : Type*} (e : Fin 4 → V) (v w : V) : Prop :=
  (v = e 0 ∧ w = e 1) ∨ (v = e 2 ∧ w = e 3) ∨
    (v = e 0 ∧ w = e 3) ∨ (v = e 2 ∧ w = e 1)

def cycleMask {V : Type*} (e : Fin 4 → V) : SimpleGraph V :=
  SimpleGraph.fromRel (cycleRelation e)

def switchGraph {V : Type*} (G : SimpleGraph V) (e : Fin 4 → V) : SimpleGraph V :=
  G ∆ cycleMask e

theorem switchGraph_involutive {V : Type*} (G : SimpleGraph V) (e : Fin 4 → V) :
    switchGraph (switchGraph G e) e = G := symmDiff_symmDiff_cancel_right _ _

theorem switchGraph_adj {V : Type*} (G : SimpleGraph V) (e : Fin 4 → V) (v w : V) :
    (switchGraph G e).Adj v w ↔
      (G.Adj v w ∧ ¬(cycleMask e).Adj v w) ∨ ((cycleMask e).Adj v w ∧ ¬G.Adj v w) := by
  simp only [switchGraph, symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]

theorem cycleMask_endpoint {V : Type*} (e : Fin 4 → V) (he : Function.Injective e)
    (i : Fin 4) (w : V) :
    (cycleMask e).Adj (e i) w ↔ w = e (oldPartner i) ∨ w = e (newPartner i) := by
  have hne (i j : Fin 4) (hij : i ≠ j) : e i ≠ e j := he.ne hij
  fin_cases i <;>
    simp [cycleMask, SimpleGraph.fromRel_adj, cycleRelation, oldPartner, newPartner, he.eq_iff]
  all_goals aesop

theorem cycleMask_outside {V : Type*} (e : Fin 4 → V) (v w : V)
    (hv : ∀ i, v ≠ e i) : ¬(cycleMask e).Adj v w := by
  simp [cycleMask, SimpleGraph.fromRel_adj, cycleRelation, hv]

def Alternating {V : Type*} (G : SimpleGraph V) (e : Fin 4 → V) : Prop :=
  G.Adj (e 0) (e 1) ∧ G.Adj (e 2) (e 3) ∧
    ¬G.Adj (e 0) (e 3) ∧ ¬G.Adj (e 2) (e 1)

theorem alternating_endpoint {V : Type*} {G : SimpleGraph V} {e : Fin 4 → V}
    (h : Alternating G e) (i : Fin 4) :
    G.Adj (e i) (e (oldPartner i)) ∧ ¬G.Adj (e i) (e (newPartner i)) := by
  fin_cases i <;> simp only [oldPartner, newPartner, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  · exact ⟨h.1, h.2.2.1⟩
  · exact ⟨G.symm h.1, fun hn => h.2.2.2 (G.symm hn)⟩
  · exact ⟨h.2.1, h.2.2.2⟩
  · exact ⟨G.symm h.2.1, fun hn => h.2.2.1 (G.symm hn)⟩

theorem degree_exchange {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (v old new : V) (hne : old ≠ new) (hold : G.Adj v old) (hnew : ¬G.Adj v new)
    (hrow : ∀ w, H.Adj v w ↔
      (G.Adj v w ∧ ¬(w = old ∨ w = new)) ∨ ((w = old ∨ w = new) ∧ ¬G.Adj v w)) :
    H.degree v = G.degree v := by
  have hs : H.neighborFinset v = insert new ((G.neighborFinset v).erase old) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_erase, hrow]
    by_cases ho : w = old
    · subst w
      simp [hold, hne, Ne.symm hne]
    · by_cases hn : w = new
      · subst w
        simp [hnew, ho]
      · simp [ho, hn]
  have hmem : old ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v old).mpr hold
  have hnmem : new ∉ (G.neighborFinset v).erase old := by
    simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    exact fun h => hnew h.2
  rw [SimpleGraph.degree, hs, Finset.card_insert_of_not_mem hnmem, Finset.card_erase_of_mem hmem]
  have hc : 0 < (G.neighborFinset v).card := Finset.card_pos.mpr ⟨old, hmem⟩
  change (G.neighborFinset v).card - 1 + 1 = (G.neighborFinset v).card
  omega

theorem switchGraph_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (e : Fin 4 → V) (he : Function.Injective e) (h : Alternating G e)
    (v : V) : (switchGraph G e).degree v = G.degree v := by
  classical
  by_cases hv : ∃ i, e i = v
  · obtain ⟨i, rfl⟩ := hv
    have hne : e (oldPartner i) ≠ e (newPartner i) := by
      apply he.ne
      fin_cases i <;> decide
    apply degree_exchange G (switchGraph G e) (e i) (e (oldPartner i)) (e (newPartner i)) hne
      (alternating_endpoint h i).1 (alternating_endpoint h i).2
    intro w
    rw [switchGraph_adj, cycleMask_endpoint e he i]
  · have houtside : ∀ i, v ≠ e i := by
      intro i hi
      exact hv ⟨i, hi.symm⟩
    have hs : (switchGraph G e).neighborFinset v = G.neighborFinset v := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, switchGraph_adj,
        cycleMask_outside e v w houtside, not_false_eq_true, and_true, false_and, or_false]
    exact congrArg Finset.card hs

theorem switchGraph_regular {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d : ℕ} (hG : G.IsRegularOfDegree d)
    (e : Fin 4 → V) (he : Function.Injective e) (h : Alternating G e) :
    (switchGraph G e).IsRegularOfDegree d := by
  classical
  intro v
  rw [switchGraph_degree G e he h v]
  exact hG v

theorem cycleMask_swapPartners {V : Type*} (e : Fin 4 → V) :
    cycleMask (e ∘ swapPartners) = cycleMask e := by
  ext v w
  simp [cycleMask, SimpleGraph.fromRel_adj, cycleRelation, Function.comp_def,
    swapPartners, Equiv.swap_apply_def]
  tauto

theorem swappedPartners_twice {V : Type*} (e : Fin 4 → V) :
    (e ∘ swapPartners) ∘ swapPartners = e := by
  funext i
  simp only [Function.comp_apply, swapPartners, Equiv.swap_apply_self]

def switchedPair {V : Type*} (s : SimpleGraph V × (Fin 4 → V)) :
    SimpleGraph V × (Fin 4 → V) :=
  (switchGraph s.1 s.2, s.2 ∘ swapPartners)

theorem switchedPair_involutive {V : Type*} : Function.Involutive (switchedPair (V := V)) := by
  rintro ⟨G, e⟩
  apply Prod.ext
  · change switchGraph (switchGraph G e) (e ∘ swapPartners) = G
    unfold switchGraph
    rw [cycleMask_swapPartners, symmDiff_symmDiff_cancel_right]
  · exact swappedPartners_twice e

theorem switchGraph_new_edges {V : Type*} (G : SimpleGraph V) (e : Fin 4 → V)
    (he : Function.Injective e) (h : Alternating G e) :
    (switchGraph G e).Adj (e 0) (e 3) ∧ (switchGraph G e).Adj (e 2) (e 1) ∧
      ¬(switchGraph G e).Adj (e 0) (e 1) ∧ ¬(switchGraph G e).Adj (e 2) (e 3) := by
  have h03 : (cycleMask e).Adj (e 0) (e 3) :=
    (cycleMask_endpoint e he 0 _).mpr (Or.inr rfl)
  have h21 : (cycleMask e).Adj (e 2) (e 1) :=
    (cycleMask_endpoint e he 2 _).mpr (Or.inr rfl)
  have h01 : (cycleMask e).Adj (e 0) (e 1) :=
    (cycleMask_endpoint e he 0 _).mpr (Or.inl rfl)
  have h23 : (cycleMask e).Adj (e 2) (e 3) :=
    (cycleMask_endpoint e he 2 _).mpr (Or.inl rfl)
  simp only [switchGraph_adj, h03, h21, h01, h23, h.1, h.2.1, h.2.2.1, h.2.2.2,
    not_true_eq_false, not_false_eq_true, and_false, false_or, and_true, true_and, and_self,
    false_and, or_false]

theorem switchedPair_alternating {V : Type*} (G : SimpleGraph V) (e : Fin 4 → V)
    (he : Function.Injective e) (h : Alternating G e) :
    Alternating (switchGraph G e) (e ∘ swapPartners) := by
  have hn := switchGraph_new_edges G e he h
  simpa only [Alternating, Function.comp_apply, swapPartners, Equiv.swap_apply_def,
    Fin.reduceFinMk, Fin.isValue, ↓reduceIte] using hn

def EdgePairState (N d : ℕ) :=
  {s : SimpleGraph (Fin N) × (Fin 4 → Fin N) //
    s.1.IsRegularOfDegree d ∧ s.1.Adj (s.2 0) (s.2 1) ∧ s.1.Adj (s.2 2) (s.2 3)}

instance (N d : ℕ) : Fintype (EdgePairState N d) := by unfold EdgePairState; infer_instance
instance (N d : ℕ) : MeasurableSpace (EdgePairState N d) := ⊤
instance (N d : ℕ) : MeasurableSingletonClass (EdgePairState N d) := ⟨fun _ => trivial⟩

def Accepted {N d : ℕ} (s : EdgePairState N d) : Prop :=
  Function.Injective s.val.2 ∧ ¬s.val.1.Adj (s.val.2 0) (s.val.2 3) ∧
    ¬s.val.1.Adj (s.val.2 2) (s.val.2 1)

theorem accepted_alternating {N d : ℕ} (s : EdgePairState N d) (h : Accepted s) :
    Alternating s.val.1 s.val.2 := ⟨s.property.2.1, s.property.2.2, h.2.1, h.2.2⟩

def acceptedSwitch {N d : ℕ} (s : EdgePairState N d) (h : Accepted s) : EdgePairState N d :=
  ⟨switchedPair s.val,
    switchGraph_regular s.val.1 s.property.1 s.val.2 h.1 (accepted_alternating s h),
    (switchedPair_alternating s.val.1 s.val.2 h.1 (accepted_alternating s h)).1,
    (switchedPair_alternating s.val.1 s.val.2 h.1 (accepted_alternating s h)).2.1⟩

theorem accepted_acceptedSwitch {N d : ℕ} (s : EdgePairState N d) (h : Accepted s) :
    Accepted (acceptedSwitch s h) := by
  refine ⟨h.1.comp swapPartners.injective, ?_, ?_⟩
  · exact (switchedPair_alternating s.val.1 s.val.2 h.1 (accepted_alternating s h)).2.2.1
  · exact (switchedPair_alternating s.val.1 s.val.2 h.1 (accepted_alternating s h)).2.2.2

def proposalSwitch {N d : ℕ} (s : EdgePairState N d) : EdgePairState N d :=
  if h : Accepted s then acceptedSwitch s h else s

theorem proposalSwitch_involutive (N d : ℕ) : Function.Involutive (@proposalSwitch N d) := by
  intro s
  by_cases hs : Accepted s
  · have hfirst : proposalSwitch s = acceptedSwitch s hs := dif_pos hs
    rw [hfirst, proposalSwitch, dif_pos (accepted_acceptedSwitch s hs)]
    apply Subtype.ext
    exact switchedPair_involutive s.val
  · simp only [proposalSwitch, hs, ↓reduceDIte]

def proposalSwitchEquiv (N d : ℕ) : EdgePairState N d ≃ EdgePairState N d :=
  (proposalSwitch_involutive N d).toPerm proposalSwitch

def edgePairLaw (N d : ℕ) : Measure (EdgePairState N d) := finiteUniform _

/-- The exact accepted/rejected two-edge switch preserves the actual finite
uniform graph-and-oriented-edge-pair law. -/
theorem edgePairLaw_switch_invariant (N d : ℕ) :
    Measure.map proposalSwitch (edgePairLaw N d) = edgePairLaw N d :=
  finiteUniform_equiv_invariant (proposalSwitchEquiv N d)

theorem finiteUniform_finset_toReal {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (s : Finset α) :
    (finiteUniform α (s : Set α)).toReal = (s.card : ℝ) / Fintype.card α := by
  have hsum : (∑ x : α, (s : Set α).indicator (1 : α → ENNReal) x) = (s.card : ENNReal) := by
    simp [Set.indicator, ← Finset.sum_filter]
  simp [finiteUniform, Measure.smul_apply, Finset.sum_apply, Measure.dirac_apply',
    hsum, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]

instance {V : Type*} (G : SimpleGraph V) : MeasurableSpace G.Dart := ⊤
instance {V : Type*} (G : SimpleGraph V) : MeasurableSingletonClass G.Dart := ⟨fun _ => trivial⟩

section Rejection
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem dart_snd_fiber_card (v : V) :
    (Finset.univ.filter (fun a : G.Dart => a.snd = v)).card = G.degree v := by
  let e : G.Dart ≃ G.Dart := SimpleGraph.Dart.symm_involutive.toPerm SimpleGraph.Dart.symm
  have h := Finset.card_equiv (s := Finset.univ.filter (fun a : G.Dart => a.snd = v))
    (t := Finset.univ.filter (fun a : G.Dart => a.fst = v)) e (fun a => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl)
  exact h.trans (G.dart_fst_fiber_card_eq_degree v)

theorem dart_fst_in_neighbors_card {d : ℕ} (hG : G.IsRegularOfDegree d) (v : V) :
    (Finset.univ.filter (fun a : G.Dart => G.Adj v a.fst)).card = d * d := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset G.Dart)
    (G.neighborFinset v) (fun a : G.Dart => a.fst)
  simp only [SimpleGraph.mem_neighborFinset] at h
  rw [← h]
  simp only [G.dart_fst_fiber_card_eq_degree, hG.degree_eq, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, Nat.cast_id]

theorem dart_snd_in_neighbors_card {d : ℕ} (hG : G.IsRegularOfDegree d) (v : V) :
    (Finset.univ.filter (fun a : G.Dart => G.Adj v a.snd)).card = d * d := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset G.Dart)
    (G.neighborFinset v) (fun a : G.Dart => a.snd)
  simp only [SimpleGraph.mem_neighborFinset] at h
  rw [← h]
  simp only [dart_snd_fiber_card, hG.degree_eq, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, Nat.cast_id]

def dartEndpoints (a b : G.Dart) : Fin 4 → V := ![a.fst, a.snd, b.fst, b.snd]

theorem dartEndpoints_injective_iff (a b : G.Dart) :
    Function.Injective (dartEndpoints G a b) ↔
      a.fst ≠ b.fst ∧ a.fst ≠ b.snd ∧ a.snd ≠ b.fst ∧ a.snd ≠ b.snd := by
  constructor
  · intro he
    exact ⟨he.ne (by decide : (0 : Fin 4) ≠ 2), he.ne (by decide : (0 : Fin 4) ≠ 3),
      he.ne (by decide : (1 : Fin 4) ≠ 2), he.ne (by decide : (1 : Fin 4) ≠ 3)⟩
  · rintro ⟨h02, h03, h12, h13⟩ i j hij
    have ha := a.fst_ne_snd
    have hb := b.fst_ne_snd
    fin_cases i <;> fin_cases j <;> simp_all [dartEndpoints]

def badSecond (a : G.Dart) : Finset G.Dart :=
  Finset.univ.filter (fun b => ¬Function.Injective (dartEndpoints G a b) ∨
    G.Adj a.fst b.snd ∨ G.Adj b.fst a.snd)

/-- At fixed first oriented edge, at most `4d + 2d²` second oriented edges
are rejected. This includes every endpoint collision and pre-existing new edge. -/
theorem badSecond_card_le {d : ℕ} (hG : G.IsRegularOfDegree d) (a : G.Dart) :
    (badSecond G a).card ≤ 4 * d + 2 * d ^ 2 := by
  let s0 := Finset.univ.filter (fun b : G.Dart => b.fst = a.fst)
  let s1 := Finset.univ.filter (fun b : G.Dart => b.fst = a.snd)
  let s2 := Finset.univ.filter (fun b : G.Dart => b.snd = a.fst)
  let s3 := Finset.univ.filter (fun b : G.Dart => b.snd = a.snd)
  let s4 := Finset.univ.filter (fun b : G.Dart => G.Adj a.fst b.snd)
  let s5 := Finset.univ.filter (fun b : G.Dart => G.Adj a.snd b.fst)
  have hsub : badSecond G a ⊆ s0 ∪ s1 ∪ s2 ∪ s3 ∪ s4 ∪ s5 := by
    intro b hb
    simp only [badSecond, Finset.mem_filter, Finset.mem_univ, true_and,
      dartEndpoints_injective_iff] at hb
    simp only [s0, s1, s2, s3, s4, s5, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hcomm : G.Adj b.fst a.snd ↔ G.Adj a.snd b.fst := G.adj_comm _ _
    tauto
  have h0 : s0.card = d := (G.dart_fst_fiber_card_eq_degree a.fst).trans (hG a.fst)
  have h1 : s1.card = d := (G.dart_fst_fiber_card_eq_degree a.snd).trans (hG a.snd)
  have h2 : s2.card = d := (dart_snd_fiber_card G a.fst).trans (hG a.fst)
  have h3 : s3.card = d := (dart_snd_fiber_card G a.snd).trans (hG a.snd)
  have h4 : s4.card = d * d := dart_snd_in_neighbors_card G hG a.fst
  have h5 : s5.card = d * d := dart_fst_in_neighbors_card G hG a.snd
  have hc := Finset.card_le_card hsub
  have hc01 := Finset.card_union_le s0 s1
  have hc012 := Finset.card_union_le (s0 ∪ s1) s2
  have hc0123 := Finset.card_union_le (s0 ∪ s1 ∪ s2) s3
  have hc01234 := Finset.card_union_le (s0 ∪ s1 ∪ s2 ∪ s3) s4
  have hc012345 := Finset.card_union_le (s0 ∪ s1 ∪ s2 ∪ s3 ∪ s4) s5
  nlinarith

theorem regular_dart_card {d : ℕ} (hG : G.IsRegularOfDegree d) :
    Fintype.card G.Dart = Fintype.card V * d := by
  rw [G.dart_card_eq_sum_degrees]
  simp only [hG.degree_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

end Rejection

/-- Actual rejection probability for an independent uniform second oriented
edge, uniformly in the first edge and in the regular graph. -/
theorem rejection_probability_bound {N d : ℕ} (G : SimpleGraph (Fin N))
    (hG : G.IsRegularOfDegree d) (hN : 0 < N) (hd : 0 < d) (a : G.Dart) :
    (finiteUniform G.Dart (badSecond G a : Set G.Dart)).toReal ≤ (4 + 2 * (d : ℝ)) / N := by
  rw [finiteUniform_finset_toReal, regular_dart_card G hG, Fintype.card_fin, Nat.cast_mul]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_le_iff₀ (mul_pos hNR hdR)).mpr
  have hc : ((badSecond G a).card : ℝ) ≤ 4 * (d : ℝ) + 2 * (d : ℝ) ^ 2 := by
    exact_mod_cast badSecond_card_le G hG a
  have he : (4 + 2 * (d : ℝ)) / N * ((N : ℝ) * d) = 4 * (d : ℝ) + 2 * (d : ℝ) ^ 2 := by
    field_simp
    ring
  rw [he]
  exact hc

end GeneralizedBulk.Graph
