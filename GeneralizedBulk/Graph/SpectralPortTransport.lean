import GeneralizedBulk.Graph.ProposalFiberVariance
import GeneralizedBulk.Graph.QuantizedSampling

/-! Exact transport between the canonical graph ports used in counting and
the arbitrary neighbor enumeration in the spectral model. Uniform star and
edge sampling is preserved by explicit per-root permutation equivalences. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph GeneralizedBulk.Graph.Configuration GeneralizedBulk.Entropy

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def spectralNeighborEquiv (v : Fin (N n)) : Fin d ≃ {w // (D.spectralRegularGraph n ω).val.Adj v w} where
  toFun j := ⟨D.neighbor n ω v j,(D.neighbor_exact n ω v _).mpr ⟨j,rfl⟩⟩
  invFun w := Classical.choose ((D.neighbor_exact n ω v w.val).mp w.property)
  left_inv j := by
    apply D.neighbor_injective n ω v
    exact Classical.choose_spec ((D.neighbor_exact n ω v _).mp ((D.neighbor_exact n ω v _).mpr ⟨j,rfl⟩))
  right_inv w := Subtype.ext (Classical.choose_spec ((D.neighbor_exact n ω v w.val).mp w.property))

def canonicalToSpectralPort (v : Fin (N n)) : Equiv.Perm (Fin d) :=
  (canonicalPortLabeling (D.spectralRegularGraph n ω) v).trans (D.spectralNeighborEquiv n ω v).symm

theorem canonical_neighbor_eq (v : Fin (N n)) (j : Fin d) :
    graphNeighbor (D.spectralRegularGraph n ω) v j = D.neighbor n ω v (D.canonicalToSpectralPort n ω v j) := by
  exact (congrArg Subtype.val ((D.spectralNeighborEquiv n ω v).apply_symm_apply
    (canonicalPortLabeling (D.spectralRegularGraph n ω) v j))).symm

def canonicalStarSampleEquiv : (Fin (N n) × Equiv.Perm (Fin d)) ≃ (Fin (N n) × Equiv.Perm (Fin d)) where
  toFun z := (z.1,z.2.symm.trans (D.canonicalToSpectralPort n ω z.1))
  invFun z := (z.1,(z.2.trans (D.canonicalToSpectralPort n ω z.1).symm).symm)
  left_inv z := by
    dsimp only
    apply Prod.ext
    · rfl
    · ext j; simp
  right_inv z := by
    dsimp only
    apply Prod.ext
    · rfl
    · ext j; simp

def canonicalEdgeSampleEquiv : (Fin (N n) × Fin d) ≃ (Fin (N n) × Fin d) where
  toFun z := (z.1,D.canonicalToSpectralPort n ω z.1 z.2)
  invFun z := (z.1,(D.canonicalToSpectralPort n ω z.1).symm z.2)
  left_inv z := by simp
  right_inv z := by simp

theorem canonical_star_selector_eq (z : Fin (N n) × Equiv.Perm (Fin d)) :
    starVertexSelection (D.spectralRegularGraph n ω) z = D.starVertex n ω (D.canonicalStarSampleEquiv n ω z) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · change graphNeighbor (D.spectralRegularGraph n ω) z.1 (z.2.symm j) = _
    rw [D.canonical_neighbor_eq n ω]
    rfl

theorem canonical_edge_selector_eq (z : Fin (N n) × Fin d) (j : Fin 2) :
    edgeVertexSelection (D.spectralRegularGraph n ω) z j =
      if j = 0 then (D.canonicalEdgeSampleEquiv n ω z).1 else
        D.neighbor n ω (D.canonicalEdgeSampleEquiv n ω z).1 (D.canonicalEdgeSampleEquiv n ω z).2 := by
  by_cases hj : j = 0
  · simp [edgeVertexSelection,hj,canonicalEdgeSampleEquiv]
  · simp only [edgeVertexSelection,if_neg hj,canonicalEdgeSampleEquiv,Equiv.coe_fn_mk]
    exact D.canonical_neighbor_eq n ω z.1 z.2

theorem realStarSampleLaw_spectral_ports {k : ℕ} (μ : Measure (Fin k × Fin (N n) → ℝ))
    (mean : Fin k × Fin (N n) → ℝ) :
    realStarSampleLaw μ (D.spectralRegularGraph n ω) mean =
      finiteSampleLaw μ (uniformSampleWeight (Fin (N n) × Equiv.Perm (Fin d)))
        (fun z x => (mean+x) ∘ flatSelection (D.starVertex n ω z)) := by
  unfold realStarSampleLaw
  simp_rw [D.canonical_star_selector_eq n ω]
  unfold finiteSampleLaw uniformSampleWeight
  exact (D.canonicalStarSampleEquiv n ω).sum_comp
    (fun z => ENNReal.ofReal (Fintype.card (Fin (N n) × Equiv.Perm (Fin d)) : ℝ)⁻¹ •
      Measure.map (fun x => (mean+x) ∘ flatSelection (D.starVertex n ω z)) μ)

end GeneralizedBulk.External.RegularSpectralData
