import GeneralizedBulk.Graph.AdmissibleSizeLimits

/-! Explicit unions of complete graphs witness the nontriviality of the
admissible-size filter at every fixed degree. -/
noncomputable section
open Filter
open scoped Classical

namespace GeneralizedBulk.Graph

/-- Disjoint copies of the complete graph on `d+1` vertices give a regular
graph with `k*(d+1)` labelled vertices. -/
theorem regularGraph_nonempty_clique_blocks (d k : ℕ) :
    Nonempty (RegularGraph (k*(d+1)) d) := by
  classical
  let G := SimpleGraph.boxProd (⊥ : SimpleGraph (Fin k))
    (⊤ : SimpleGraph (Fin (d+1)))
  letI finiteG : SimpleGraph.LocallyFinite G := fun v => G.neighborSetFintype v
  have hG : G.IsRegularOfDegree d := by
    intro v
    exact (SimpleGraph.boxProd_degree (G := (⊥ : SimpleGraph (Fin k)))
      (H := (⊤ : SimpleGraph (Fin (d+1)))) v).trans (by simp [SimpleGraph.bot_degree])
  have hnatG (v : Fin k × Fin (d+1)) : Nat.card (G.neighborSet v) = d := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree, hG]
  let e : (Fin k × Fin (d+1)) ≃ Fin (k*(d+1)) := finProdFinEquiv
  let H := G.comap e.symm
  refine ⟨⟨H,?_⟩⟩
  intro v
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr ((SimpleGraph.Iso.comap e.symm G).mapNeighborSet v)).trans (hnatG _)

/-- Arbitrarily large actual admissible positive sizes exist. -/
theorem frequently_admissibleSize (d : ℕ) : ∃ᶠ M in atTop, AdmissibleSize d M := by
  apply Filter.frequently_atTop.mpr
  intro k
  refine ⟨(k+1)*(d+1), ?_, ?_⟩
  · nlinarith
  · exact ⟨by positivity, regularGraph_nonempty_clique_blocks d (k+1)⟩

/-- The literal admissible-size convergence filter is nontrivial. -/
instance (d : ℕ) : NeBot (admissibleSizeFilter d) :=
  Filter.frequently_iff_neBot.mp (frequently_admissibleSize d)

end GeneralizedBulk.Graph
