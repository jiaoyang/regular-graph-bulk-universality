import GaussianWave.BS.Reused.Graph.UniformSwitching

/-! The oriented-edge-pair uniform model has the uniform regular-graph marginal. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph

theorem finiteUniform_map_of_fiber_card
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (f : α → β) (K : ℕ) (hK : 0 < K)
    (hfiber : ∀ b, (Finset.univ.filter (fun a => f a = b)).card = K) :
    Measure.map f (finiteUniform α) = finiteUniform β := by
  letI := finiteUniform_isProbability α
  letI := finiteUniform_isProbability β
  have hm : Measurable f := measurable_of_finite _
  have hcard : Fintype.card α = Fintype.card β * K := by
    have h := Finset.card_eq_sum_card_fiberwise (f := f)
      (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β)) (fun a ha => Finset.mem_univ _)
    simpa only [Finset.card_univ, hfiber, Finset.sum_const, nsmul_eq_mul, Nat.cast_id] using h
  have hKR : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  have hBR : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext s hs
  apply (ENNReal.toReal_eq_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  let t := s.toFinite.toFinset
  let u := Finset.univ.filter (fun a : α => f a ∈ t)
  have ht : (t : Set β) = s := Set.Finite.coe_toFinset _
  have hu : (u : Set α) = f ⁻¹' s := by
    ext a
    simp only [u, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_preimage]
    exact Iff.of_eq (congrArg (fun q : Set β => f a ∈ q) ht)
  have hc : u.card = t.card * K := by
    have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset α) t f
    simpa only [hfiber, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, u] using h.symm
  rw [Measure.map_apply hm hs, ← hu, finiteUniform_finset_toReal, ← ht,
    finiteUniform_finset_toReal, hc, hcard, Nat.cast_mul]
  field_simp
  ring

def edgePairGraph {N d : ℕ} (s : EdgePairState N d) : RegularGraph N d :=
  ⟨s.val.1, s.property.1⟩

def edgePairGraphFiberEquiv {N d : ℕ} (G : RegularGraph N d) :
    {s : EdgePairState N d // edgePairGraph s = G} ≃ (G.val.Dart × G.val.Dart) where
  toFun s := by
    rcases s with ⟨⟨⟨H, e⟩, hreg, h01, h23⟩, hs⟩
    have hHG : H = G.val := congrArg Subtype.val hs
    subst H
    exact ⟨⟨(e 0, e 1), h01⟩, ⟨(e 2, e 3), h23⟩⟩
  invFun darts :=
    ⟨⟨(G.val, ![darts.1.fst, darts.1.snd, darts.2.fst, darts.2.snd]),
      G.property, darts.1.adj, darts.2.adj⟩, Subtype.ext rfl⟩
  left_inv s := by
    rcases s with ⟨⟨⟨H, e⟩, hreg, h01, h23⟩, hs⟩
    have hHG : H = G.val := congrArg Subtype.val hs
    subst H
    apply Subtype.ext
    apply Subtype.ext
    change (G.val, ![e 0, e 1, e 2, e 3]) = (G.val, e)
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
  right_inv darts := by
    rcases darts with ⟨a, b⟩
    rfl

theorem edgePairGraph_fiber_card {N d : ℕ} (G : RegularGraph N d) :
    (Finset.univ.filter (fun s : EdgePairState N d => edgePairGraph s = G)).card = (N * d) ^ 2 := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (edgePairGraphFiberEquiv G), Fintype.card_prod,
    regular_dart_card G.val G.property, Fintype.card_fin]
  ring

theorem edgePairState_nonempty {N d : ℕ} [Nonempty (RegularGraph N d)]
    (hN : 0 < N) (hd : 0 < d) : Nonempty (EdgePairState N d) := by
  obtain ⟨G⟩ := (inferInstance : Nonempty (RegularGraph N d))
  let v : Fin N := ⟨0, hN⟩
  have hc : 0 < (G.val.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, G.property.degree_eq]
    exact hd
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hc
  have hAdj := (SimpleGraph.mem_neighborFinset G.val v w).mp hw
  exact ⟨⟨(G.val, ![v, w, v, w]), G.property, hAdj, hAdj⟩⟩

/-- Uniform graph plus two independent uniform oriented edges is represented
by the finite switch-invariant edge-pair law: every graph fiber has `(Nd)²`
elements. In particular its graph marginal is exactly uniform. -/
theorem edgePairLaw_graph_marginal {N d : ℕ} [Nonempty (RegularGraph N d)]
    (hN : 0 < N) (hd : 0 < d) :
    Measure.map edgePairGraph (edgePairLaw N d) = regularGraphLaw N d := by
  letI := edgePairState_nonempty hN hd
  exact finiteUniform_map_of_fiber_card edgePairGraph ((N * d) ^ 2)
    (pow_pos (Nat.mul_pos hN hd) _) edgePairGraph_fiber_card

end GaussianWave.BS.Reused.Graph
