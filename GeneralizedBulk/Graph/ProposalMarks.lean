import GeneralizedBulk.Graph.MeasurableGaussianMarks
import GeneralizedBulk.Graph.OrientedEdgeSampling
import GeneralizedBulk.Graph.ProposalVariance

/-!
# Exact Gaussian-limit sampler for the physical two-edge proposals

The randomly ordered leaf of a sampled empirical star is exactly a uniformly
sampled oriented edge. This module proves that the two-edge mark law used by
the BS limit is the literal law of the eigenvectors at the four endpoints of
the physical independent edge proposals. No asymptotic replacement of the
sampler, or conditioning on accepted switches, is involved.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph

@[simp] theorem finiteUniform_singleton {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : α) :
    finiteUniform α {a} = (Fintype.card α : ENNReal)⁻¹ := by
  simp [finiteUniform, Finset.sum_apply, Measure.dirac_apply', Set.indicator]

/-- Independent finite uniform samplers are the finite uniform sampler on
the product, including their exact normalizing constants. -/
theorem finiteUniform_prod {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    (finiteUniform α).prod (finiteUniform β) = finiteUniform (α × β) := by
  letI := finiteUniform_isProbability α
  letI := finiteUniform_isProbability β
  apply Measure.ext_of_singleton
  rintro ⟨a,b⟩
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, finiteUniform_singleton, finiteUniform_singleton]
  rw [Set.singleton_prod_singleton, finiteUniform_singleton]
  simp only [Fintype.card_prod, Nat.cast_mul]
  exact (ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _))).symm

/-- Concatenation of the endpoints of two independently sampled oriented
edges, retaining the order required by the literal switching matrices. -/
def mergeEdgeMarks {k : ℕ} (xy : ((Fin k × Fin 2) → ℝ) × ((Fin k × Fin 2) → ℝ))
    (ai : Fin k × Fin 4) : ℝ :=
  ![xy.1 (ai.1, 0), xy.1 (ai.1, 1), xy.2 (ai.1, 0), xy.2 (ai.1, 1)] ai.2

theorem measurable_mergeEdgeMarks (k : ℕ) : Measurable (mergeEdgeMarks (k := k)) := by
  apply measurable_pi_lambda
  rintro ⟨a,i⟩
  fin_cases i
  · exact (measurable_pi_apply (a, 0)).comp measurable_fst
  · exact (measurable_pi_apply (a, 1)).comp measurable_fst
  · exact (measurable_pi_apply (a, 0)).comp measurable_snd
  · exact (measurable_pi_apply (a, 1)).comp measurable_snd

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def proposalMark {k : ℕ} (q : Fin k → Fin (N n) → ℝ)
    (s : ProposalSample (N n) d) (ai : Fin k × Fin 4) : ℝ :=
  Real.sqrt (N n) * q ai.1 (D.proposalEndpoints n ω s ai.2)

def proposalMarkLaw {k : ℕ} (q : Fin k → Fin (N n) → ℝ) : Measure ((Fin k × Fin 4) → ℝ) :=
  Measure.map (D.proposalMark n ω q) (uniformOrientedProposals (N n) d)

theorem proposalMarkLaw_isProbability {k : ℕ} (hd : 0 < d) (q : Fin k → Fin (N n) → ℝ) :
    IsProbabilityMeasure (D.proposalMarkLaw n ω q) := by
  letI := uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  exact MeasureTheory.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

/-- The two independent BS star endpoints have exactly the same physical law
as the two uniformly sampled oriented-edge proposals. In particular the law
is independent of the chosen ordered star leaf. -/
theorem twoEdgeLaw_eq_proposalMarkLaw {k : ℕ} (a : Fin k → Fin (N n)) (leaf : Fin d) :
    D.twoEdgeLaw n ω a leaf = D.proposalMarkLaw n ω (fun i => D.eigenvector n ω (a i)) := by
  let q := fun i => D.eigenvector n ω (a i)
  let μ := D.starLaw n ω q
  letI : IsProbabilityMeasure μ := D.starLaw_isProbability n ω q
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0, D.size_pos n⟩, leaf⟩⟩
  letI := finiteUniform_isProbability (Fin (N n) × Fin d)
  have hrestriction :
      (fun xy => (Gaussian.starEndpointRestriction (k := k) leaf).mulVec (Gaussian.mergeVectors xy)) =
        mergeEdgeMarks ∘ Prod.map (starEdgeRestriction leaf) (starEdgeRestriction leaf) := by
    funext xy ai
    rcases ai with ⟨b,i⟩
    fin_cases i <;>
      simp [Gaussian.starEndpointRestriction, Gaussian.selectionMatrix_mulVec,
        Gaussian.starEndpointSource, Gaussian.mergeVectors, mergeEdgeMarks,
        starEdgeRestriction, Matrix.cons_val_two, Matrix.cons_val_three]
  change Measure.map (fun x => (Gaussian.starEndpointRestriction (k := k) leaf).mulVec x)
    (Measure.map Gaussian.mergeVectors (μ.prod μ)) = _
  rw [Measure.map_map (Gaussian.measurable_finiteMatrixAction _)
    Gaussian.continuous_mergeVectors.measurable]
  change Measure.map (fun xy => (Gaussian.starEndpointRestriction (k := k) leaf).mulVec
    (Gaussian.mergeVectors xy)) (μ.prod μ) = _
  rw [hrestriction, ← Measure.map_map (measurable_mergeEdgeMarks k)
    ((measurable_starEdgeRestriction leaf).prodMap (measurable_starEdgeRestriction leaf)),
    ← Measure.map_prod_map μ μ (measurable_starEdgeRestriction leaf) (measurable_starEdgeRestriction leaf)]
  rw [D.starLaw_edge_marginal n ω q leaf]
  rw [orientedEdgeLaw, Measure.map_prod_map _ _ (measurable_of_finite _) (measurable_of_finite _),
    Measure.map_map (measurable_mergeEdgeMarks k)
      ((measurable_of_finite _).prodMap (measurable_of_finite _)), finiteUniform_prod]
  congr 1
  funext s ai
  rcases ai with ⟨b,i⟩
  fin_cases i <;> rfl

/-- Products of the actual normalized endpoint marks are the quadratic marks
appearing in the exact finite resolvent expansion. -/
theorem proposalMark_product {k : ℕ} (a : Fin k → Fin (N n)) (b : Fin k)
    (i j : Fin 4) (s : ProposalSample (N n) d) :
    D.proposalMark n ω (fun b => D.eigenvector n ω (a b)) s (b,i) *
      D.proposalMark n ω (fun b => D.eigenvector n ω (a b)) s (b,j) =
      D.proposalQuadratic n ω (a b) i j s := by
  have hs : Real.sqrt (N n : ℝ) ^ 2 = N n := Real.sq_sqrt (Nat.cast_nonneg _)
  simp only [proposalMark, proposalQuadratic]
  calc
    _ = Real.sqrt (N n : ℝ) ^ 2 *
      (D.eigenvector n ω (a b) (D.proposalEndpoints n ω s i) *
        D.eigenvector n ω (a b) (D.proposalEndpoints n ω s j)) := by ring
    _ = _ := by rw [hs]; ring

end GeneralizedBulk.External.RegularSpectralData
