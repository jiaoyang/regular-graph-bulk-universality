import GeneralizedBulk.LocalLaw.StarTreeNormalization
import LocalLaw.SourceLocalLawIdentifiers

/-! The exact source pair-neighborhood reference on an acyclic rooted star. -/
noncomputable section
open scoped Classical

namespace GeneralizedBulk.LocalLawBridge
open LocalLaw GeneralizedBulk.KestenMcKay

def normalizedStarReference (d : ℕ) (m z : ℂ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  let M := kestenMcKayTransform d m z
  let t := -m*treeEdgeWeight d
  fun i j => Fin.cases (Fin.cases M (fun _ => M*t) j)
    (fun a => Fin.cases (M*t) (fun b => if a=b then M else M*t^2) j) i

theorem normalizedStarReference_scaled (d : ℕ) (hd : 3≤d)
    (z : ℂ) (hz : 0<z.im) (i j : Fin (d+1)) :
    (Real.sqrt ((d : ℝ)-1) : ℂ)⁻¹ *
      normalizedStarReference d
        (semicircleRoot (z/(Real.sqrt ((d : ℝ)-1) : ℂ)))
        (z/(Real.sqrt ((d : ℝ)-1) : ℂ)) i j =
      treeGreenStar d (by exact_mod_cast hd) z i j := by
  have hdiag := source_diagonal_scaled d hd z hz
  have hedge := source_edgeWeight_scaled d hd z hz
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  · exact hdiag
  · simpa only [normalizedStarReference, treeGreenStar, cavityStar, Fin.cases_zero,
      Fin.cases_succ, hedge,mul_neg,←mul_assoc,hdiag]
  · simpa only [normalizedStarReference, treeGreenStar, cavityStar, Fin.cases_zero,
      Fin.cases_succ, hedge,mul_neg,←mul_assoc,hdiag]
  · by_cases hab : a=b
    · simpa only [normalizedStarReference,treeGreenStar,cavityStar,Fin.cases_succ,if_pos hab]
        using hdiag
    · simp only [normalizedStarReference,treeGreenStar,cavityStar,Fin.cases_succ,if_neg hab,
        hedge,neg_sq,←mul_assoc,hdiag]

private theorem star_pair_acyclic {N d : ℕ} (g : LocalLaw.RegularGraph N d)
    (root : Fin N) (neighbor : Fin d → Fin N)
    (hadj : ∀ a,g.graph.Adj root (neighbor a))
    (r R : ℕ) (hmargin : r+1≤R) (htree : (graphBall g.graph root R).IsTree)
    (i j : Fin (d+1)) :
    (g.pairModel (Fin.cases root neighbor i) (Fin.cases root neighbor j) r).graph.IsAcyclic := by
  let vertex : Fin (d+1) → Fin N := Fin.cases root neighbor
  have hc (a : Fin (d+1)) : g.graph.edist root (vertex a) ≤ (1 : ℕ∞) := by
    refine Fin.cases ?_ (fun b => ?_) a
    · simp [vertex]
    · simpa only [vertex,Fin.cases_succ] using (SimpleGraph.edist_eq_one_iff_adj.mpr (hadj b)).le
  let B := pairBallVertices g.graph (vertex i) (vertex j) r
  have hb : B ⊆ graphBallVertices g.graph root R := by
    intro v hv
    have go (a : Fin (d+1)) (hv : g.graph.edist (vertex a) v ≤ (r : ℕ∞)) :
        v ∈ graphBallVertices g.graph root R := by
      change g.graph.edist root v ≤ (R : ℕ∞)
      calc
        _ ≤ g.graph.edist root (vertex a)+g.graph.edist (vertex a) v := g.graph.edist_triangle
        _ ≤ (1 : ℕ∞)+(r : ℕ∞) := add_le_add (hc a) hv
        _ ≤ (R : ℕ∞) := by exact_mod_cast (show 1+r≤R by omega)
    rcases hv with hv|hv
    · exact go i hv
    · exact go j hv
  let f : (g.graph.induce B) →g graphBall g.graph root R := {
    toFun := fun v => ⟨v.val,hb v.property⟩
    map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    exact congrArg (fun x : graphBallVertices g.graph root R => x.val) h
  intro v p hp
  exact htree.IsAcyclic (p.map f) (hp.map hf)

/-- The source's finite-core infinite extension agrees with the explicit
homogeneous tree matrix on every physical star entry. -/
theorem source_pairModel_star_reference {N d : ℕ} (g : LocalLaw.RegularGraph N d)
    (hd : 3≤d) (root : Fin N) (neighbor : Fin d → Fin N)
    (hadj : ∀ a,g.graph.Adj root (neighbor a))
    (hne : ∀ a,neighbor a≠root) (hinj : Function.Injective neighbor)
    (r R : ℕ) (hr : 1≤r) (hmargin : r+1≤R)
    (htree : (graphBall g.graph root R).IsTree)
    (z : ℂ) (hz : 0<z.im) (i j : Fin (d+1)) :
    (g.pairModel (Fin.cases root neighbor i) (Fin.cases root neighbor j) r).treeExtensionGreen
      (by omega) z
      (pairBallLeft g.graph (Fin.cases root neighbor i) (Fin.cases root neighbor j) r)
      (pairBallRight g.graph (Fin.cases root neighbor i) (Fin.cases root neighbor j) r) =
      normalizedStarReference d (semicircleRoot z) z i j := by
  have forest := star_pair_acyclic g root neighbor hadj r R hmargin htree
  have hm := semicircleRoot_equation z
  have hi := (semicircleRoot_im_pos hz).le
  simp_rw [DeficientGraph.treeExtensionGreen_eq_extensionGreen _ hd z hz]
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  · simpa only [normalizedStarReference,Fin.cases_zero] using
      (g.pairModel root root r).extensionGreen_zero_deficit_forest_diagonal hd
        (g.pairModel_zero_deficit root root r) (forest 0 0)
        (pairBallLeft g.graph root root r) (semicircleRoot z) z hm hz hi
  · simpa only [normalizedStarReference,Fin.cases_zero,Fin.cases_succ] using
      (g.pairModel root (neighbor b) r).extensionGreen_zero_deficit_forest_adjacent hd
        (g.pairModel_zero_deficit root (neighbor b) r) (forest 0 b.succ)
        (pairBallLeft g.graph root (neighbor b) r) (pairBallRight g.graph root (neighbor b) r)
        (hadj b) (semicircleRoot z) z hm hz hi
  · simpa only [normalizedStarReference,Fin.cases_zero,Fin.cases_succ] using
      (g.pairModel (neighbor a) root r).extensionGreen_zero_deficit_forest_adjacent hd
        (g.pairModel_zero_deficit (neighbor a) root r) (forest a.succ 0)
        (pairBallLeft g.graph (neighbor a) root r) (pairBallRight g.graph (neighbor a) root r)
        (hadj a).symm (semicircleRoot z) z hm hz hi
  · by_cases hab : a=b
    · subst b
      simpa only [normalizedStarReference,Fin.cases_succ,if_pos rfl] using
        (g.pairModel (neighbor a) (neighbor a) r).extensionGreen_zero_deficit_forest_diagonal hd
          (g.pairModel_zero_deficit (neighbor a) (neighbor a) r) (forest a.succ a.succ)
          (pairBallLeft g.graph (neighbor a) (neighbor a) r) (semicircleRoot z) z hm hz hi
    · let B := pairBallVertices g.graph (neighbor a) (neighbor b) r
      let H := pairBallGraph g.graph (neighbor a) (neighbor b) r
      let u : B := pairBallLeft g.graph (neighbor a) (neighbor b) r
      let v : B := pairBallRight g.graph (neighbor a) (neighbor b) r
      let o : B := ⟨root,Or.inl ((SimpleGraph.edist_eq_one_iff_adj.mpr (hadj a).symm).le.trans
        (by exact_mod_cast hr))⟩
      have huo : H.Adj u o := (hadj a).symm
      have hov : H.Adj o v := hadj b
      let p : H.Walk u v := .cons huo (.cons hov .nil)
      have hp : p.IsPath := by
        change (SimpleGraph.Walk.cons huo (.cons hov .nil)).IsPath
        rw [SimpleGraph.Walk.cons_isPath_iff,SimpleGraph.Walk.cons_isPath_iff]
        refine ⟨⟨.nil,?_⟩,?_⟩
        · simp only [SimpleGraph.Walk.support_nil,List.mem_singleton]
          intro h
          exact hne b (congrArg (fun x : B => x.val) h).symm
        · simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
            List.mem_cons,List.mem_singleton,not_or]
          constructor
          · intro h
            exact hne a (congrArg (fun x : B => x.val) h)
          · refine ⟨?_,by simp⟩
            intro h
            exact hab (hinj (congrArg (fun x : B => x.val) h))
      have hdistance : H.dist u v=2 := by
        have h := acyclic_path_length_eq_dist (forest a.succ b.succ) p hp
        simpa only [p,SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_nil] using h.symm
      have hh := (g.pairModel (neighbor a) (neighbor b) r).extensionGreen_zero_deficit_forest_column hd
        (g.pairModel_zero_deficit (neighbor a) (neighbor b) r) (forest a.succ b.succ)
        v (semicircleRoot z) z hm hz hi u
      change _ = forestKernelColumn H v _ _ u at hh
      simp only [forestKernelColumn,if_pos p.reachable,hdistance] at hh
      simpa only [normalizedStarReference,Fin.cases_succ,if_neg hab,forestKernelColumn,
        if_pos p.reachable,hdistance] using hh

end GeneralizedBulk.LocalLawBridge
