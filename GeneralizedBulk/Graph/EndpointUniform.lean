import GeneralizedBulk.Graph.ProposalMarks
import GeneralizedBulk.Graph.UniformMarginals

/-! Exact uniform endpoint marginals for independent oriented-edge proposals. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GeneralizedBulk.Graph

def rootPortFiberEquiv (N d : ℕ) (v : Fin N) : {a : Fin N × Fin d // a.1 = v} ≃ Fin d where
  toFun a := a.val.2
  invFun j := ⟨(v,j),rfl⟩
  left_inv a := Subtype.ext (Prod.ext a.property.symm rfl)
  right_inv j := rfl

theorem uniformRootPort_root_law (N d : ℕ) (hN : 0 < N) (hd : 0 < d) :
    Measure.map (Prod.fst : Fin N × Fin d → Fin N) (finiteUniform (Fin N × Fin d)) = finiteUniform (Fin N) := by
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  apply finiteUniform_map_of_fiber_card Prod.fst d hd
  intro v
  rw [← Fintype.card_subtype, Fintype.card_congr (rootPortFiberEquiv N d v), Fintype.card_fin]

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def portReverseEquiv : (Fin (N n) × Fin d) ≃ (Fin (N n) × Fin d) :=
  (D.portDartEquiv n ω).trans
    ((⟨SimpleGraph.Dart.symm, SimpleGraph.Dart.symm,
      SimpleGraph.Dart.symm_symm, SimpleGraph.Dart.symm_symm⟩ :
        Equiv.Perm (D.simpleGraph n ω).Dart).trans (D.portDartEquiv n ω).symm)

@[simp] theorem portReverseEquiv_first (a : Fin (N n) × Fin d) :
    (D.portReverseEquiv n ω a).1 = D.neighbor n ω a.1 a.2 := rfl

/-- Both endpoints, including the uniformly chosen neighbor, have exactly
the uniform vertex law before conditioning on switching acceptance. -/
theorem proposalEndpoint_uniform_law (hd : 0 < d) (i : Fin 2) :
    Measure.map (fun a => D.proposalEndpoint n ω a i) (finiteUniform (Fin (N n) × Fin d)) =
      finiteUniform (Fin (N n)) := by
  fin_cases i
  · exact uniformRootPort_root_law (N n) d (D.size_pos n) hd
  · change Measure.map (fun a => D.proposalEndpoint n ω a 1) (finiteUniform (Fin (N n) × Fin d)) =
      finiteUniform (Fin (N n))
    have heq : (fun a => D.proposalEndpoint n ω a 1) =
        Prod.fst ∘ D.portReverseEquiv n ω := rfl
    rw [heq, ← Measure.map_map measurable_fst (measurable_of_finite _),
      finiteUniform_equiv_invariant, uniformRootPort_root_law (N n) d (D.size_pos n) hd]

theorem proposalEndpoint_integral (hd : 0 < d) (i : Fin 2) (f : Fin (N n) → ℝ) :
    (∫ a, f (D.proposalEndpoint n ω a i) ∂finiteUniform (Fin (N n) × Fin d)) =
      ∫ v, f v ∂finiteUniform (Fin (N n)) := by
  rw [← D.proposalEndpoint_uniform_law n ω hd i,
    integral_map (measurable_of_finite _).aemeasurable (measurable_of_finite _).aestronglyMeasurable]

/-- Endpoint choices on the two independently proposed edges have exactly
the product of the uniform vertex laws, for every one of the four choices. -/
theorem crossProposalEndpoints_uniform_law (hd : 0 < d) (i j : Fin 2) :
    Measure.map (fun s : ProposalSample (N n) d =>
      (D.proposalEndpoint n ω s.1 i, D.proposalEndpoint n ω s.2 j))
      (uniformOrientedProposals (N n) d) =
      (finiteUniform (Fin (N n))).prod (finiteUniform (Fin (N n))) := by
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  letI := finiteUniform_isProbability (Fin (N n) × Fin d)
  change Measure.map (Prod.map (fun a => D.proposalEndpoint n ω a i)
    (fun a => D.proposalEndpoint n ω a j)) (finiteUniform ((Fin (N n) × Fin d) × (Fin (N n) × Fin d))) = _
  rw [← finiteUniform_prod, ← Measure.map_prod_map _ _ (measurable_of_finite _) (measurable_of_finite _),
    D.proposalEndpoint_uniform_law n ω hd i, D.proposalEndpoint_uniform_law n ω hd j]

end GeneralizedBulk.External.RegularSpectralData
