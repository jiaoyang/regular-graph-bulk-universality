import GaussianWave.BS.Reused.Graph.UniformSwitching

/-! Direct switching estimates for the literal uniform simple regular graph.
The protected graph records already prescribed edges.  We retain these edges
when deleting one additional edge by an accepted two-edge switch. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An accepted switch preserves every edge of a protected subgraph provided
neither deleted edge belongs to that subgraph. -/
theorem protected_le_switchGraph (F G : SimpleGraph V) (e : Fin 4 → V)
    (hFG : F ≤ G) (hacc : Alternating G e)
    (h01 : ¬F.Adj (e 0) (e 1)) (h23 : ¬F.Adj (e 2) (e 3)) :
    F ≤ switchGraph G e := by
  intro v w hF
  have hG : G.Adj v w := hFG hF
  have hmask : ¬(cycleMask e).Adj v w := by
    intro hm
    have hm' : cycleRelation e v w ∨ cycleRelation e w v := by
      exact ((SimpleGraph.fromRel_adj ..).mp hm).2
    rcases hm' with hm | hm
    · rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact h01 hF
      · exact h23 hF
      · exact hacc.2.2.1 hG
      · exact hacc.2.2.2 hG
    · rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact h01 (F.symm hF)
      · exact h23 (F.symm hF)
      · exact hacc.2.2.1 (G.symm hG)
      · exact hacc.2.2.2 (G.symm hG)
  exact (switchGraph_adj G e v w).mpr (Or.inl ⟨hG,hmask⟩)

/-- Darts of `G` whose edge is protected are in bijection with darts of `F`. -/
def protectedDartEquiv (F G : SimpleGraph V) (hFG : F ≤ G) :
    {a : G.Dart // F.Adj a.fst a.snd} ≃ F.Dart where
  toFun a := ⟨(a.val.fst,a.val.snd),a.property⟩
  invFun a := ⟨⟨(a.fst,a.snd),hFG a.adj⟩,a.adj⟩
  left_inv a := by apply Subtype.ext; apply SimpleGraph.Dart.ext <;> rfl
  right_inv a := by apply SimpleGraph.Dart.ext <;> rfl

/-- At least the total dart count minus the fixed rejection count and the
number of protected darts can be used as the second switching edge. -/
theorem goodSecond_card_lower (F G : SimpleGraph V) {d : ℕ}
    (hG : G.IsRegularOfDegree d) (hFG : F ≤ G) (a : G.Dart) :
    Fintype.card V*d-(4*d+2*d^2+Fintype.card F.Dart) ≤
      (Finset.univ.filter (fun b : G.Dart => b ∉ badSecond G a ∧ ¬F.Adj b.fst b.snd)).card := by
  let p := Finset.univ.filter (fun b : G.Dart => F.Adj b.fst b.snd)
  have hp : p.card = Fintype.card F.Dart := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (protectedDartEquiv F G hFG)
  have hu : (badSecond G a ∪ p).card ≤ 4*d+2*d^2+Fintype.card F.Dart :=
    (Finset.card_union_le _ _).trans (by rw [hp]; exact Nat.add_le_add_right (badSecond_card_le G hG a) _)
  have hc : (Finset.univ.filter (fun b : G.Dart => b ∉ badSecond G a ∧ ¬F.Adj b.fst b.snd)).card +
      (badSecond G a ∪ p).card = Fintype.card G.Dart := by
    have he : Finset.univ.filter (fun b : G.Dart => b ∉ badSecond G a ∧ ¬F.Adj b.fst b.snd) =
        Finset.univ \ (badSecond G a ∪ p) := by ext b; simp [p]
    rw [he,Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _),Finset.card_univ]
  rw [regular_dart_card G hG] at hc
  omega

section FiniteSwitching
variable {N d : ℕ} (F : SimpleGraph (Fin N)) (a b : Fin N)

abbrev PrescribedGraphs := {G : RegularGraph N d // F ≤ G.val}
abbrev PrescribedEdgeGraphs := {G : RegularGraph N d // F ≤ G.val ∧ G.val.Adj a b}

abbrev SafeSecond (G : PrescribedEdgeGraphs (d := d) F a b) :=
  {z : G.val.val.Dart // z ∉ badSecond G.val.val ⟨(a,b),G.property.2⟩ ∧ ¬F.Adj z.fst z.snd}

abbrev SwitchSource := Σ G : PrescribedEdgeGraphs (d := d) F a b, SafeSecond F a b G

abbrev SwitchTarget :=
  {s : EdgePairState N d // s.val.2 0 = a ∧ s.val.2 3 = b ∧ F ≤ s.val.1}

def sourceSwitchState (s : SwitchSource (d := d) F a b) : EdgePairState N d :=
  ⟨(s.1.val.val,![a,b,s.2.val.fst,s.2.val.snd]),s.1.val.property,s.1.property.2,s.2.val.adj⟩

theorem sourceSwitchState_accepted (s : SwitchSource (d := d) F a b) :
    Accepted (sourceSwitchState F a b s) := by
  have h := s.2.property.1
  simp only [badSecond,Finset.mem_filter,Finset.mem_univ,true_and,not_or] at h
  exact ⟨not_not.mp h.1,h.2.1,h.2.2⟩

theorem sourceSwitchState_injective :
    Function.Injective (sourceSwitchState (d := d) F a b) := by
  rintro ⟨⟨G,hG⟩,⟨z,hz⟩⟩ ⟨⟨H,hH⟩,⟨w,hw⟩⟩ he
  have hGH : G = H := Subtype.ext (congrArg (fun t : EdgePairState N d => t.val.1) he)
  subst H
  have hzw : z = w := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact congrArg (fun t : EdgePairState N d => t.val.2 2) he
    · exact congrArg (fun t : EdgePairState N d => t.val.2 3) he
  subst w
  rfl

def switchedSource (hF : ¬F.Adj a b) (s : SwitchSource (d := d) F a b) :
    SwitchTarget (d := d) F a b := by
  let z := sourceSwitchState F a b s
  have hz := sourceSwitchState_accepted F a b s
  refine ⟨acceptedSwitch z hz,?_,?_,?_⟩
  · rfl
  · rfl
  · exact protected_le_switchGraph F _ _ s.1.property.1 (accepted_alternating z hz) hF s.2.property.2

theorem switchedSource_injective (hF : ¬F.Adj a b) :
    Function.Injective (switchedSource (d := d) F a b hF) := by
  intro s t h
  apply sourceSwitchState_injective F a b
  apply (proposalSwitch_involutive N d).injective
  have hs : proposalSwitch (sourceSwitchState F a b s) =
      (switchedSource F a b hF s).val := dif_pos (sourceSwitchState_accepted F a b s)
  have ht : proposalSwitch (sourceSwitchState F a b t) =
      (switchedSource F a b hF t).val := dif_pos (sourceSwitchState_accepted F a b t)
  rw [hs,ht,congrArg Subtype.val h]

abbrev SwitchCode := Σ G : PrescribedGraphs (d := d) F,
  {v : Fin N // G.val.val.Adj a v} × {v : Fin N // G.val.val.Adj b v}

def targetCode (s : SwitchTarget (d := d) F a b) : SwitchCode (d := d) F a b :=
  ⟨⟨⟨s.val.val.1,s.val.property.1⟩,s.property.2.2⟩,
    ⟨⟨s.val.val.2 1,by simpa only [s.property.1] using s.val.property.2.1⟩,
     ⟨s.val.val.2 2,by simpa only [s.property.2.1] using s.val.val.1.symm s.val.property.2.2⟩⟩⟩

theorem targetCode_injective : Function.Injective (targetCode (d := d) F a b) := by
  intro s t h
  have hG : s.val.val.1 = t.val.val.1 := congrArg (fun z : SwitchCode (d := d) F a b => z.1.val.val) h
  have h1 : s.val.val.2 1 = t.val.val.2 1 := congrArg (fun z : SwitchCode (d := d) F a b => z.2.1.val) h
  have h2 : s.val.val.2 2 = t.val.val.2 2 := congrArg (fun z : SwitchCode (d := d) F a b => z.2.2.val) h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext hG
  funext i
  fin_cases i
  · exact s.property.1.trans t.property.1.symm
  · exact h1
  · exact h2
  · exact s.property.2.1.trans t.property.2.1.symm

theorem switchCode_card : Fintype.card (SwitchCode (d := d) F a b) =
    Fintype.card (PrescribedGraphs (d := d) F)*d^2 := by
  have hc (G : PrescribedGraphs (d := d) F) (v : Fin N) :
      Fintype.card {w : Fin N // G.val.val.Adj v w} = d := by
    change Fintype.card (G.val.val.neighborSet v) = d
    rw [SimpleGraph.card_neighborSet_eq_degree,G.val.property.degree_eq]
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_prod,hc]
  simp [pow_two]

/-- The finite switching count for one additional prescribed edge.  It is a
statement about literal numbers of labeled simple regular graphs, with no
configuration-model conditioning loss. -/
theorem prescribed_edge_extension_count (hF : ¬F.Adj a b) :
    Fintype.card (PrescribedEdgeGraphs (d := d) F a b)*
      (N*d-(4*d+2*d^2+Fintype.card F.Dart)) ≤
        Fintype.card (PrescribedGraphs (d := d) F)*d^2 := by
  have hlower : Fintype.card (PrescribedEdgeGraphs (d := d) F a b)*
      (N*d-(4*d+2*d^2+Fintype.card F.Dart)) ≤
        Fintype.card (SwitchSource (d := d) F a b) := by
    rw [Fintype.card_sigma]
    calc
      _ = ∑ _G : PrescribedEdgeGraphs (d := d) F a b,
          (N*d-(4*d+2*d^2+Fintype.card F.Dart)) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun G _ => by
        rw [Fintype.card_subtype]
        simpa only [Fintype.card_fin] using
          goodSecond_card_lower F G.val.val G.val.property G.property.1
            (⟨(a,b),G.property.2⟩ : G.val.val.Dart))
  exact hlower.trans ((Fintype.card_le_of_injective _
    ((targetCode_injective F a b).comp (switchedSource_injective F a b hF))).trans_eq
      (switchCode_card F a b))

/-- Adding a genuinely new nonloop edge to the protected graph is precisely
requiring that edge in addition to the old protected subgraph. -/
def prescribedSupEdgeEquiv (hab : a ≠ b) :
    PrescribedGraphs (d := d) (F ⊔ SimpleGraph.edge a b) ≃ PrescribedEdgeGraphs (d := d) F a b where
  toFun G := ⟨G.val,(sup_le_iff.mp G.property).1,
    (sup_le_iff.mp G.property).2 ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab⟩)⟩
  invFun G := ⟨G.val,sup_le G.property.1 (by
    intro v w hvw
    rcases (SimpleGraph.edge_adj ..).mp hvw with ⟨(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩),hne⟩
    · exact G.property.2
    · exact G.val.val.symm G.property.2)⟩
  left_inv G := rfl
  right_inv G := rfl

/-- The prescribed-edge probability multiplier is at most `2d/N` once the
total number of darts is twice the fixed excluded-dart budget. -/
theorem prescribed_sup_edge_count_real (hN : 0 < N) (hd : 0 < d) (hab : a ≠ b)
    (hF : ¬F.Adj a b) (hsize : 2*(4*d+2*d^2+Fintype.card F.Dart) ≤ N*d) :
    (Fintype.card (PrescribedGraphs (d := d) (F ⊔ SimpleGraph.edge a b)) : ℝ) ≤
      Fintype.card (PrescribedGraphs (d := d) F)*(2*(d : ℝ)/(N : ℝ)) := by
  rw [Fintype.card_congr (prescribedSupEdgeEquiv F a b hab)]
  let K := 4*d+2*d^2+Fintype.card F.Dart
  have hK : K ≤ N*d := by dsimp [K]; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : (Fintype.card (PrescribedEdgeGraphs (d := d) F a b) : ℝ)*
      ((N : ℝ)*d-K) ≤ Fintype.card (PrescribedGraphs (d := d) F)*(d : ℝ)^2 := by
    have h := prescribed_edge_extension_count (d := d) F a b hF
    have hreal := (Nat.cast_le (α := ℝ)).mpr h
    simp only [Nat.cast_mul,Nat.cast_pow] at hreal
    change (Fintype.card (PrescribedEdgeGraphs (d := d) F a b) : ℝ)*((N*d-K : ℕ) : ℝ) ≤ _ at hreal
    rw [Nat.cast_sub hK,Nat.cast_mul] at hreal
    exact hreal
  have hs : 2*(K : ℝ) ≤ (N : ℝ)*d := by exact_mod_cast hsize
  have ha : (0 : ℝ) ≤ Fintype.card (PrescribedEdgeGraphs (d := d) F a b) := by positivity
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hn).mpr
  apply (mul_le_mul_right hdp).mp
  nlinarith

end FiniteSwitching
section FiniteEdgeSets
variable {N d : ℕ}

/-- The graph constructed from a loop-free finite edge set has exactly that
edge set, and consequently exactly twice as many oriented darts. -/
theorem fromEdgeSet_dart_card (E : Finset (Sym2 (Fin N)))
    (hE : ∀ e ∈ E,¬e.IsDiag) :
    Fintype.card (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin N)))).Dart = 2*E.card := by
  have hfin : @SimpleGraph.edgeFinset (Fin N) (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin N))))
      (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin N)))).fintypeEdgeSet = E := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_fromEdgeSet,Set.mem_diff,
      Finset.mem_coe,Set.mem_setOf_eq]
    exact and_iff_left_of_imp (hE e)
  rw [SimpleGraph.dart_card_eq_twice_card_edges]
  exact congrArg (fun S : Finset (Sym2 (Fin N)) => 2*S.card) hfin

/-- Requiring no protected edges places no restriction on the graph. -/
def prescribedBotEquiv : PrescribedGraphs (N := N) (d := d) ⊥ ≃ RegularGraph N d where
  toFun G := G.val
  invFun G := ⟨G,bot_le⟩
  left_inv G := rfl
  right_inv G := rfl

/-- Uniform simple-graph prescribed-edge counting, obtained by successively
performing the exact switching bound.  The finite edge set is arbitrary;
no independence of its individual adjacency events is asserted. -/
theorem prescribed_finite_edge_count_real (hN : 0 < N) (hd : 0 < d) (L : ℕ)
    (hsize : 2*(4*d+2*d^2+2*L) ≤ N*d) :
    ∀ E : Finset (Sym2 (Fin N)), E.card ≤ L → (∀ e ∈ E,¬e.IsDiag) →
    (Fintype.card (PrescribedGraphs (d := d)
      (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin N))))) : ℝ) ≤
        Fintype.card (RegularGraph N d)*(2*(d : ℝ)/(N : ℝ))^E.card := by
  intro E
  induction E using Finset.induction_on with
  | empty =>
    intro hcard hE
    simp only [Finset.coe_empty,SimpleGraph.fromEdgeSet_empty,Finset.card_empty,pow_zero,mul_one]
    exact le_of_eq (congrArg (fun n : ℕ => (n : ℝ)) (Fintype.card_congr prescribedBotEquiv))
  | @insert e E he ih =>
    intro hcard hE
    obtain ⟨a,b⟩ := e
    have hab : a ≠ b := by
      simpa only [Sym2.isDiag_iff_proj_eq] using hE s(a,b) (Finset.mem_insert_self _ _)
    have hcardE : E.card ≤ L := (Finset.card_le_card (Finset.subset_insert _ _)).trans hcard
    have hdiagE : ∀ e ∈ E,¬e.IsDiag := fun e hm => hE e (Finset.mem_insert_of_mem hm)
    let F := SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin N)))
    have hnot : ¬F.Adj a b := by
      intro ha
      exact he ((SimpleGraph.fromEdgeSet_adj ..).mp ha).1
    have hbudget : 2*(4*d+2*d^2+Fintype.card F.Dart) ≤ N*d := by
      rw [fromEdgeSet_dart_card E hdiagE]
      exact (Nat.mul_le_mul_left 2 (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hcardE) _)).trans hsize
    have hnew : SimpleGraph.fromEdgeSet ((insert s(a,b) E : Finset (Sym2 (Fin N))) : Set (Sym2 (Fin N))) =
        F ⊔ SimpleGraph.edge a b := by
      simpa only [Finset.coe_insert,Set.union_singleton,SimpleGraph.edge] using
        (SimpleGraph.fromEdgeSet_union (E : Set (Sym2 (Fin N))) {s(a,b)})
    rw [hnew,Finset.card_insert_of_not_mem he,pow_succ]
    calc
      _ ≤ Fintype.card (PrescribedGraphs (d := d) F)*(2*(d : ℝ)/(N : ℝ)) :=
        prescribed_sup_edge_count_real F a b hN hd hab hnot hbudget
      _ ≤ (Fintype.card (RegularGraph N d)*(2*(d : ℝ)/(N : ℝ))^E.card)*
          (2*(d : ℝ)/(N : ℝ)) :=
        mul_le_mul_of_nonneg_right (ih hcardE hdiagE) (by positivity)
      _ = _ := by ring

/-- The actual uniform labeled simple-regular-graph law satisfies the finite
prescribed-edge bound, with no external probability estimate. -/
theorem prescribed_finite_edge_probability [Nonempty (RegularGraph N d)]
    (hN : 0 < N) (hd : 0 < d) (L : ℕ) (hsize : 2*(4*d+2*d^2+2*L) ≤ N*d)
    (E : Finset (Sym2 (Fin N))) (hcard : E.card ≤ L) (hE : ∀ e ∈ E,¬e.IsDiag) :
    (regularGraphLaw N d).real {G | SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin N))) ≤ G.val} ≤
      (2*(d : ℝ)/(N : ℝ))^E.card := by
  let F := SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin N)))
  have he : {G : RegularGraph N d | F ≤ G.val} =
      (Finset.univ.filter (fun G : RegularGraph N d => F ≤ G.val) : Set (RegularGraph N d)) := by
    ext G; simp
  change (regularGraphLaw N d {G | F ≤ G.val}).toReal ≤ _
  rw [regularGraphLaw,he,finiteUniform_finset_toReal,← Fintype.card_subtype]
  apply (div_le_iff₀ (show (0 : ℝ) < Fintype.card (RegularGraph N d) by exact_mod_cast Fintype.card_pos)).mpr
  simpa only [mul_comm] using prescribed_finite_edge_count_real hN hd L hsize E hcard hE

/-- A convenient form of the bound indexed directly by a finite protected
graph rather than by a separate loop-free edge palette. -/
theorem prescribed_graph_probability [Nonempty (RegularGraph N d)]
    (F : SimpleGraph (Fin N)) (hN : 0 < N) (hd : 0 < d)
    (hsize : 2*(4*d+2*d^2+2*F.edgeFinset.card) ≤ N*d) :
    (regularGraphLaw N d).real {G | F ≤ G.val} ≤
      (2*(d : ℝ)/(N : ℝ))^F.edgeFinset.card := by
  have h := prescribed_finite_edge_probability hN hd F.edgeFinset.card hsize F.edgeFinset le_rfl
    (fun e he => F.not_isDiag_of_mem_edgeSet ((SimpleGraph.mem_edgeFinset).mp he))
  simpa only [SimpleGraph.coe_edgeFinset,SimpleGraph.fromEdgeSet_edgeSet] using h

/-- Instance-independent edge cardinality form, useful after transporting a
finite pattern by an injective vertex map. -/
theorem prescribed_graph_probability_natCard [Nonempty (RegularGraph N d)]
    (F : SimpleGraph (Fin N)) (hN : 0 < N) (hd : 0 < d)
    (hsize : 2*(4*d+2*d^2+2*Nat.card F.edgeSet) ≤ N*d) :
    (regularGraphLaw N d).real {G | F ≤ G.val} ≤
      (2*(d : ℝ)/(N : ℝ))^(Nat.card F.edgeSet) := by
  have he : F.edgeFinset.card = Nat.card F.edgeSet := by
    rw [SimpleGraph.edgeFinset_card,Fintype.card_eq_nat_card]
  have hs : 2*(4*d+2*d^2+2*F.edgeFinset.card) ≤ N*d := by rw [he]; exact hsize
  simpa only [he] using prescribed_graph_probability F hN hd hs

end FiniteEdgeSets
end GaussianWave.BS.Lower
