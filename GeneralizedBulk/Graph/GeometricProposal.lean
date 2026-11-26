import GeneralizedBulk.Graph.BallCounting
import GeneralizedBulk.Graph.EndpointUniform
import GeneralizedBulk.ExternalGeometry

/-!
# Exceptional probability for two fixed-radius edge neighborhoods

Ball cardinality comes from finite walk counts. Endpoint marginals are
literal uniform laws, so two independent edges have a short connection with
probability at most a fixed constant divided by the graph size.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GeneralizedBulk.Graph

/-- Two independent uniform vertices are close with probability at most the
fixed ball-cardinality bound divided by `N`. -/
theorem uniformVertexPair_close_probability_bound
    {N d : ℕ} (G : SimpleGraph (Fin N)) (hG : G.IsRegularOfDegree d) (hN : 0 < N) (R : ℕ) :
    ((finiteUniform (Fin N)).prod (finiteUniform (Fin N))).real
      {p | G.edist p.1 p.2 ≤ (R : ℕ∞)} ≤ (regularBallBound d R : ℝ) / N := by
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  let B := Finset.univ.filter (fun p : Fin N × Fin N => G.edist p.1 p.2 ≤ (R : ℕ∞))
  have hs : (B : Set (Fin N × Fin N)) = {p | G.edist p.1 p.2 ≤ (R : ℕ∞)} := by ext p; simp [B]
  have hc : B.card ≤ N * regularBallBound d R := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [Fintype.sum_prod_type]
    calc
      _ = ∑ v : Fin N, (graphBallVertices G v R).card := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [graphBallVertices, Finset.card_eq_sum_ones, Finset.sum_filter]
      _ ≤ ∑ _v : Fin N, regularBallBound d R :=
        Finset.sum_le_sum (fun v _ => regular_graphBall_card_le G hG v R)
      _ = _ := by simp
  rw [finiteUniform_prod, measureReal_def, ← hs, finiteUniform_finset_toReal]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  calc
    _ ≤ ((N : ℝ) * regularBallBound d R) / ((N : ℝ) * N) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = _ := by field_simp; ring

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem firstProposalEndpoint_set_probability (hd : 0 < d) (i : Fin 2) (B : Set (Fin (N n))) :
    (uniformOrientedProposals (N n) d).real {s | D.proposalEndpoint n ω s.1 i ∈ B} =
      (finiteUniform (Fin (N n))).real B := by
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  letI := finiteUniform_isProbability (Fin (N n))
  have h := congrArg (fun mu : Measure (Fin (N n) × Fin (N n)) => mu (B ×ˢ Set.univ))
    (D.crossProposalEndpoints_uniform_law n ω hd i 0)
  dsimp only at h
  rw [Measure.map_apply (measurable_of_finite _) (Set.toFinite _ |>.measurableSet),
    Measure.prod_prod, measure_univ, mul_one] at h
  have heq : (fun s : ProposalSample (N n) d =>
      (D.proposalEndpoint n ω s.1 i,D.proposalEndpoint n ω s.2 0)) ⁻¹' (B ×ˢ Set.univ) =
      {s | D.proposalEndpoint n ω s.1 i ∈ B} := by ext s; simp
  rw [heq] at h
  exact congrArg ENNReal.toReal h

theorem secondProposalEndpoint_set_probability (hd : 0 < d) (j : Fin 2) (B : Set (Fin (N n))) :
    (uniformOrientedProposals (N n) d).real {s | D.proposalEndpoint n ω s.2 j ∈ B} =
      (finiteUniform (Fin (N n))).real B := by
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  letI := finiteUniform_isProbability (Fin (N n))
  have h := congrArg (fun mu : Measure (Fin (N n) × Fin (N n)) => mu (Set.univ ×ˢ B))
    (D.crossProposalEndpoints_uniform_law n ω hd 0 j)
  dsimp only at h
  rw [Measure.map_apply (measurable_of_finite _) (Set.toFinite _ |>.measurableSet),
    Measure.prod_prod, measure_univ, one_mul] at h
  have heq : (fun s : ProposalSample (N n) d =>
      (D.proposalEndpoint n ω s.1 0,D.proposalEndpoint n ω s.2 j)) ⁻¹' (Set.univ ×ˢ B) =
      {s | D.proposalEndpoint n ω s.2 j ∈ B} := by ext s; simp
  rw [heq] at h
  exact congrArg ENNReal.toReal h

theorem crossProposal_close_probability_bound (hd : 0 < d) (R : ℕ) (i j : Fin 2) :
    (uniformOrientedProposals (N n) d).real {s |
      (D.simpleGraph n ω).edist (D.proposalEndpoint n ω s.1 i) (D.proposalEndpoint n ω s.2 j) ≤ (R : ℕ∞)} ≤
        (regularBallBound d R : ℝ) / N n := by
  have h := congrArg (fun mu : Measure (Fin (N n) × Fin (N n)) =>
    mu {p | (D.simpleGraph n ω).edist p.1 p.2 ≤ (R : ℕ∞)})
    (D.crossProposalEndpoints_uniform_law n ω hd i j)
  dsimp only at h
  rw [Measure.map_apply (measurable_of_finite _) (Set.toFinite _ |>.measurableSet)] at h
  have heq := congrArg ENNReal.toReal h
  exact heq.le.trans (uniformVertexPair_close_probability_bound (D.simpleGraph n ω)
    (D.simpleGraph_regular n ω) (D.size_pos n) R)

def geometricProposalBad (R : ℕ) (bad : Finset (Fin (N n))) : Set (ProposalSample (N n) d) :=
  ({s | s.1.1 ∈ bad} ∪ {s | s.2.1 ∈ bad}) ∪
    ⋃ ij : Fin 2 × Fin 2, {s | (D.simpleGraph n ω).edist
      (D.proposalEndpoint n ω s.1 ij.1) (D.proposalEndpoint n ω s.2 ij.2) ≤ (R : ℕ∞)}

/-- Fixed-radius tree failures cost the actual root proportion; short
connections between the two independently proposed edges cost only `O(1/N)`. -/
theorem geometricProposalBad_probability_bound (hd : 0 < d) (R : ℕ) (bad : Finset (Fin (N n))) :
    (uniformOrientedProposals (N n) d).real (D.geometricProposalBad n ω R bad) ≤
      2 * (bad.card : ℝ) / N n + 4 * (regularBallBound d R : ℝ) / N n := by
  have hfirst : (uniformOrientedProposals (N n) d).real {s : ProposalSample (N n) d | s.1.1 ∈ bad} =
      (bad.card : ℝ) / N n := by
    have h := D.firstProposalEndpoint_set_probability n ω hd 0 (bad : Set _)
    change (uniformOrientedProposals (N n) d).real {s | s.1.1 ∈ bad} = _ at h
    simp only [measureReal_def] at h
    rw [finiteUniform_finset_toReal, Fintype.card_fin] at h
    exact h
  have hsecond : (uniformOrientedProposals (N n) d).real {s : ProposalSample (N n) d | s.2.1 ∈ bad} =
      (bad.card : ℝ) / N n := by
    have h := D.secondProposalEndpoint_set_probability n ω hd 0 (bad : Set _)
    change (uniformOrientedProposals (N n) d).real {s | s.2.1 ∈ bad} = _ at h
    simp only [measureReal_def] at h
    rw [finiteUniform_finset_toReal, Fintype.card_fin] at h
    exact h
  have hcross := measureReal_iUnion_fintype_le (μ := uniformOrientedProposals (N n) d)
    (fun ij : Fin 2 × Fin 2 => {s | (D.simpleGraph n ω).edist
      (D.proposalEndpoint n ω s.1 ij.1) (D.proposalEndpoint n ω s.2 ij.2) ≤ (R : ℕ∞)})
  have hsum := Finset.sum_le_sum (fun ij (_ : ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2))) =>
    D.crossProposal_close_probability_bound n ω hd R ij.1 ij.2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hunion := measureReal_union_le (μ := uniformOrientedProposals (N n) d)
    ({s : ProposalSample (N n) d | s.1.1 ∈ bad} ∪ {s | s.2.1 ∈ bad})
    (⋃ ij : Fin 2 × Fin 2, {s | (D.simpleGraph n ω).edist
      (D.proposalEndpoint n ω s.1 ij.1) (D.proposalEndpoint n ω s.2 ij.2) ≤ (R : ℕ∞)})
  have hroots := measureReal_union_le (μ := uniformOrientedProposals (N n) d)
    {s : ProposalSample (N n) d | s.1.1 ∈ bad} {s | s.2.1 ∈ bad}
  rw [hfirst,hsecond] at hroots
  change _ ≤ _ at hunion
  have hfinal := hunion.trans (add_le_add hroots (hcross.trans hsum))
  convert hfinal using 1 <;> dsimp only [geometricProposalBad] <;> norm_num <;> ring

end GeneralizedBulk.External.RegularSpectralData
