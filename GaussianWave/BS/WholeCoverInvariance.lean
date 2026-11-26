import GaussianWave.BS.RootedCoverInvariance

/-! Rooted symmetries and the proved edge-flip symmetry give invariance
under every actual tree automorphism. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

def treeProcessRelabel {A : Type*} {d : ℕ} (e : regularWordTree d ≃g regularWordTree d)
    (z : RegularTreeVertex d → A) : RegularTreeVertex d → A := fun v => z (e v)

theorem measurable_treeProcessRelabel {A : Type*} [MeasurableSpace A] {d : ℕ}
    (e : regularWordTree d ≃g regularWordTree d) : Measurable (treeProcessRelabel (A := A) e) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

def TreeLawInvariant {A : Type*} [MeasurableSpace A] {d : ℕ}
    (Q : Measure (RegularTreeVertex d → A)) (e : regularWordTree d ≃g regularWordTree d) : Prop :=
  Measure.map (treeProcessRelabel e) Q = Q

theorem TreeLawInvariant.refl {A : Type*} [MeasurableSpace A] {d : ℕ}
    (Q : Measure (RegularTreeVertex d → A)) : TreeLawInvariant Q SimpleGraph.Iso.refl :=
  Measure.map_id

theorem TreeLawInvariant.trans {A : Type*} [MeasurableSpace A] {d : ℕ}
    {Q : Measure (RegularTreeVertex d → A)} {e f : regularWordTree d ≃g regularWordTree d}
    (he : TreeLawInvariant Q e) (hf : TreeLawInvariant Q f) : TreeLawInvariant Q (e.trans f) := by
  change Measure.map (treeProcessRelabel e ∘ treeProcessRelabel f) Q = Q
  rw [← Measure.map_map (measurable_treeProcessRelabel e) (measurable_treeProcessRelabel f),hf,he]

theorem TreeLawInvariant.symm {A : Type*} [MeasurableSpace A] {d : ℕ}
    {Q : Measure (RegularTreeVertex d → A)} {e : regularWordTree d ≃g regularWordTree d}
    (he : TreeLawInvariant Q e) : TreeLawInvariant Q e.symm := by
  have h := congrArg (Measure.map (treeProcessRelabel (A := A) e.symm)) he
  rw [Measure.map_map (measurable_treeProcessRelabel e.symm) (measurable_treeProcessRelabel e)] at h
  have hc : treeProcessRelabel (A := A) e.symm ∘ treeProcessRelabel e = id := by
    funext z v
    exact congrArg z (e.apply_symm_apply v)
  rw [hc,Measure.map_id] at h
  exact h.symm

theorem treeLawInvariant_of_rooted_and_flip {A : Type*} [MeasurableSpace A] (q : ℕ)
    (Q : Measure (RegularTreeVertex (q+1) → A))
    (hrooted : ∀ e : regularWordTree (q+1) ≃g regularWordTree (q+1),
      e none = none → TreeLawInvariant Q e)
    (hflip : TreeLawInvariant Q (regularTreeEdgeFlip q))
    (e : regularWordTree (q+1) ≃g regularWordTree (q+1)) : TreeLawInvariant Q e := by
  have hneighbor (a : Fin (q+1)) : TreeLawInvariant Q (regularTreeRerootNeighbor q a) :=
    hflip.trans (hrooted _ rfl)
  have hstep {v w : RegularTreeVertex (q+1)} (h : (regularWordTree (q+1)).Adj v w)
      (hv : ∃ a : regularWordTree (q+1) ≃g regularWordTree (q+1),
        a none = v ∧ TreeLawInvariant Q a) :
      ∃ a : regularWordTree (q+1) ≃g regularWordTree (q+1),
        a none = w ∧ TreeLawInvariant Q a := by
    obtain ⟨a,ha,hIa⟩ := hv
    have hh := a.symm.map_rel_iff.mpr h
    rw [← ha] at hh
    simp only [a.symm_apply_apply] at hh
    obtain ⟨j,hj⟩ := exists_regularTreeNeighbor_of_adj none (a.symm w) hh
    refine ⟨(regularTreeRerootNeighbor q j).trans a, ?_, (hneighbor j).trans hIa⟩
    change a (regularTreeRerootNeighbor q j none) = w
    rw [regularTreeRerootNeighbor_root]
    change a (regularTreeNeighbor none j) = w
    rw [hj,a.apply_symm_apply]
  have horbit (v : RegularTreeVertex (q+1)) :
      ∃ a : regularWordTree (q+1) ≃g regularWordTree (q+1),
        a none = v ∧ TreeLawInvariant Q a := by
    cases v with
    | none => exact ⟨SimpleGraph.Iso.refl,rfl,TreeLawInvariant.refl Q⟩
    | some aw =>
      rcases aw with ⟨a,w⟩
      induction w with
      | nil => exact ⟨regularTreeRerootNeighbor q a,regularTreeRerootNeighbor_root q a,hneighbor a⟩
      | cons b w ih => exact hstep (regularTreeNeighbor_adj (some (a,w)) (some b)) ih
  obtain ⟨a,ha,hIa⟩ := horbit (e none)
  let f := e.trans a.symm
  have hf : f none = none := by
    change a.symm (e none) = none
    rw [← ha,a.symm_apply_apply]
  have hIf := hrooted f hf
  have heq : f.trans a = e := by
    exact DFunLike.ext _ _ (fun v => a.apply_symm_apply (e v))
  simpa only [heq] using hIf.trans hIa

theorem uniformTreeCoverLaw_invariant {N m : ℕ} (G : RegularGraph N (m+2)) (hN : 0<N)
    (e : regularWordTree (m+2) ≃g regularWordTree (m+2)) :
    Measure.map (fun z : RegularTreeVertex (m+2) → Fin N => fun v => z (e v))
      (uniformTreeCoverLaw G hN : Measure _) = (uniformTreeCoverLaw G hN : Measure _) := by
  let Q : Measure (RegularTreeVertex (m+2) → Fin N) := uniformTreeCoverLaw G hN
  exact treeLawInvariant_of_rooted_and_flip (A := Fin N) (m+1) Q
    (fun f hf => uniformTreeCoverLaw_rooted_invariant G hN f hf)
    (uniformTreeCoverLaw_edgeFlip_invariant G hN) e

theorem uniformLiftedTreeLaw_invariant {N m r : ℕ} (G : RegularGraph N (m+2))
    (hN : 0<N) (f : Fin r → Fin N → ℝ)
    (e : regularWordTree (m+2) ≃g regularWordTree (m+2)) :
    Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun av => z (av.1,e av.2))
      (uniformLiftedTreeLaw G hN f) = uniformLiftedTreeLaw G hN f := by
  let C := fun z : RegularTreeVertex (m+2) → Fin N =>
    fun av : Fin r × RegularTreeVertex (m+2) => f av.1 (z av.2)
  let T := fun z : RegularTreeVertex (m+2) → Fin N => fun v => z (e v)
  let U := fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
    fun av : Fin r × RegularTreeVertex (m+2) => z (av.1,e av.2)
  have hC : Measurable C := measurable_treeColoring f
  have hT : Measurable T := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hU : Measurable U := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  change Measure.map U (Measure.map C _) = Measure.map C _
  rw [Measure.map_map hU hC]
  have hc : U ∘ C = C ∘ T := rfl
  rw [hc,← Measure.map_map hC hT,uniformTreeCoverLaw_invariant G hN e]

end GaussianWave.BS
