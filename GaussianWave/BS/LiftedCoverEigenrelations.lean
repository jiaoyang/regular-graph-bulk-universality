import GaussianWave.BS.LiftedCoverMoments
import GaussianWave.BS.ProcessEigenrelations

/-! Every actual graph eigenvector coloring of the actual uniform tree
cover satisfies the tree eigenrelations almost surely at every channel and
site. The root relation is read from the literal C0 sampler; proved cover
invariance moves it to every actual tree vertex. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

theorem tree_root_neighbor_sum (d r : ℕ) (a : Fin r)
    (x : (Fin r × RegularTreeVertex d) → ℝ) :
    (∑ z : (regularWordTree d).neighborSet none, x (a,z.val))=
      ∑ j : Fin d, x (a,some (j,[])) := by
  have h := Equiv.sum_comp (regularTreeNeighborEquiv d none)
    (fun z : (regularWordTree d).neighborSet none => x (a,z.val))
  exact h.symm

theorem uniformLiftedTreeLaw_root_eigenrelations {N m r : ℕ} (G : RegularGraph N (m+2))
    (hN : 0<N) (energy : Fin r → ℝ) (f : Fin r → Fin N → ℝ)
    (hf : ∀ a, GraphEigenrelation G (energy a) (f a)) :
    ∀ᵐ x ∂uniformLiftedTreeLaw G hN f, ∀ a, treeEigenResidual (m+2) r energy a none x=0 := by
  have h := finiteVertexCoverLaw_ae_eigenrelation G 0 energy f hf
  rw [← uniformLiftedTreeLaw_ball G hN f 0] at h
  have hB : Measurable (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
      fun av : Fin r × VertexBallVertex (m+2) 0 => z (av.1,vertexBallEmbedding (m+2) 0 av.2)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have ha := ae_of_ae_map hB.aemeasurable h
  filter_upwards [ha] with x hx
  intro a
  unfold treeEigenResidual
  rw [tree_root_neighbor_sum]
  have he := (hx a).1
  change (∑ j : Fin (m+2), x (a,some (j,[])))=energy a*x (a,none) at he
  exact sub_eq_zero.mpr he

/-- Actual lifted graph eigenvectors obey every tree eigenrelation,
without a cover, stationarity, or eigenprocess contract as a premise. -/
theorem uniformLiftedTreeLaw_eigenrelations {N m r : ℕ} (G : RegularGraph N (m+2))
    (hN : 0<N) (energy : Fin r → ℝ) (f : Fin r → Fin N → ℝ)
    (hf : ∀ a, GraphEigenrelation G (energy a) (f a)) :
    ∀ᵐ x ∂uniformLiftedTreeLaw G hN f, ∀ a u, treeEigenResidual (m+2) r energy a u x=0 := by
  have hsite (u : RegularTreeVertex (m+2)) :
      ∀ᵐ x ∂uniformLiftedTreeLaw G hN f, ∀ a, treeEigenResidual (m+2) r energy a u x=0 := by
    let e := regularTreeReroot (m+1) u
    have he : e none=u := regularTreeReroot_root (m+1) u
    let T := fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
      fun av : Fin r × RegularTreeVertex (m+2) => z (av.1,e av.2)
    have hT : Measurable T := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    have hr := uniformLiftedTreeLaw_root_eigenrelations G hN energy f hf
    rw [← uniformLiftedTreeLaw_invariant G hN f e] at hr
    have ha := ae_of_ae_map hT.aemeasurable hr
    filter_upwards [ha] with x hx
    intro a
    have h := hx a
    rw [treeEigenResidual_equivariant,he] at h
    exact h
  have hall := ae_all_iff.mpr hsite
  filter_upwards [hall] with x hx
  intro a u
  exact hx u a

end GaussianWave.BS
