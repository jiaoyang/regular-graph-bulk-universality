import GaussianWave.BS.Lower.PathNeighborhoodCode

/-! Distinct labels glue actual overlapping path-neighborhood codes. The
result is a literal finite graph automorphism fixing every specified center,
not an assumed orbit-recovery statement. -/
noncomputable section
open scoped Classical
set_option maxHeartbeats 1200000
namespace GaussianWave.BS.Lower

variable {V A I : Type*}

def PathCoveredVertex (H : SimpleGraph V) (R : ℕ) (center : I → V) (v : V) : Prop :=
  ∃ (i : I) (n : Fin (R+1)) (p : Fin (n.val+1) → V),p 0=center i ∧
    (∀ j : Fin n.val,H.Adj (p j.castSucc) (p j.succ)) ∧ ∃ j,p j=v

def PathCoveredEdge (H : SimpleGraph V) (R : ℕ) (center : I → V) (u v : V) : Prop :=
  (∃ i j,center i=u ∧ center j=v) ∨
  ∃ (i : I) (n : Fin (R+1)) (p : Fin (n.val+1) → V),p 0=center i ∧
    (∀ j : Fin n.val,H.Adj (p j.castSucc) (p j.succ)) ∧
    ∃ j : Fin n.val,(p j.castSucc=u ∧ p j.succ=v) ∨ (p j.castSucc=v ∧ p j.succ=u)

theorem pathCoveredVertex_of_edist (H : SimpleGraph V) (R : ℕ) (center : I → V) (v : V)
    (hv : ∃ i,H.edist (center i) v ≤ (R : ℕ∞)) : PathCoveredVertex H R center v := by
  obtain ⟨i,hi⟩ := hv
  obtain ⟨p,hp⟩ := H.exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by simp) hi)
  have hlen : p.length ≤ R := by exact_mod_cast hp.trans_le hi
  refine ⟨i,⟨p.length,by omega⟩,fun j => p.getVert j.val,by simp,fun j => p.adj_getVert_succ j.isLt,?_⟩
  exact ⟨Fin.last p.length,by simp⟩

theorem PathCoveredEdge.symm (H : SimpleGraph V) (R : ℕ) (center : I → V) (u v : V)
    (h : PathCoveredEdge H R center u v) : PathCoveredEdge H R center v u := by
  rcases h with ⟨i,j,hi,hj⟩ | ⟨i,n,p,hp0,hp,j,hj⟩
  · exact Or.inl ⟨j,i,hj,hi⟩
  · exact Or.inr ⟨i,n,p,hp0,hp,j,hj.symm⟩

theorem pathCoveredEdge_of_short_edist (H : SimpleGraph V) (R : ℕ) (center : I → V)
    (u v : V) (huv : H.Adj u v)
    (hu : ∃ i,H.edist (center i) u+1 ≤ (R : ℕ∞)) : PathCoveredEdge H R center u v := by
  obtain ⟨i,hi⟩ := hu
  have hdist : H.edist (center i) u ≤ (R : ℕ∞) := (le_add_right le_rfl).trans hi
  obtain ⟨p,hp⟩ := H.exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by simp) hdist)
  let w := p.concat huv
  have hlen : w.length ≤ R := by
    change (p.concat huv).length ≤ R
    rw [SimpleGraph.Walk.length_concat]
    exact_mod_cast (show (p.length : ℕ∞)+1 ≤ (R : ℕ∞) by rw [hp]; exact hi)
  have hwu : w.getVert p.length=u := by simp [w,SimpleGraph.Walk.concat,SimpleGraph.Walk.getVert_append]
  have hwv : w.getVert (p.length+1)=v := by
    have h := w.getVert_length
    simpa only [w,SimpleGraph.Walk.length_concat] using h
  refine Or.inr ⟨i,⟨w.length,by omega⟩,fun j => w.getVert j.val,by simp,
    fun j => w.adj_getVert_succ j.isLt,⟨p.length,by simp [w]⟩,Or.inl ⟨hwu,hwv⟩⟩

theorem pathNeighborhoodCode_transport (H : SimpleGraph V) (R : ℕ)
    (color color' : V → A) (o : V)
    (hcode : pathNeighborhoodCode H R color' o=pathNeighborhoodCode H R color o)
    (n : Fin (R+1)) (p : Fin (n.val+1) → V) (hp0 : p 0=o)
    (hp : ∀ j : Fin n.val,H.Adj (p j.castSucc) (p j.succ)) :
    ∃ p' : Fin (n.val+1) → V,p' 0=o ∧
      (∀ j : Fin n.val,H.Adj (p' j.castSucc) (p' j.succ)) ∧ ∀ j,color' (p' j)=color (p j) := by
  let word : BoundedColorWord A R := ⟨n,fun j => color (p j)⟩
  have hs : pathNeighborhoodCode H R color o word=true :=
    (pathNeighborhoodCode_true_iff H R color o word).mpr ⟨p,hp0,hp,fun _ => rfl⟩
  rw [← hcode] at hs
  exact (pathNeighborhoodCode_true_iff H R color' o word).mp hs

/-- A finite adjacency-preserving permutation is an actual graph isomorphism:
reflection follows from surjectivity on the finite set of adjacent pairs. -/
def graphIsoOfAdjacencyPreservingPerm [Fintype V] (H : SimpleGraph V)
    (e : Equiv.Perm V) (he : ∀ u v,H.Adj u v → H.Adj (e u) (e v)) : H ≃g H where
  toEquiv := e
  map_rel_iff' := by
    intro u v
    constructor
    · intro h
      let D := {z : V × V // H.Adj z.1 z.2}
      let f (z : D) : D := ⟨(e z.1.1,e z.1.2),he _ _ z.2⟩
      have hf : Function.Injective f := by
        intro z w hzw
        apply Subtype.ext
        have hh := congrArg Subtype.val hzw
        exact Prod.ext (e.injective (congrArg Prod.fst hh)) (e.injective (congrArg Prod.snd hh))
      obtain ⟨z,hz⟩ := Finite.surjective_of_injective hf (⟨(e u,e v),h⟩ : D)
      have hh := congrArg Subtype.val hz
      have hu : z.1.1=u := e.injective (congrArg Prod.fst hh)
      have hv : z.1.2=v := e.injective (congrArg Prod.snd hh)
      simpa only [hu,hv] using z.2
    · exact he u v

/-- If the chosen neighborhoods cover every vertex and every edge, equality
of all center codes for an injective source labeling forces a genuine graph
automorphism fixing those centers. The comparison labeling need not be
assumed injective. -/
theorem pathCode_gluing_graphIso [Fintype V] (H : SimpleGraph V) (R : ℕ)
    (center : I → V)
    (hvertices : ∀ v,PathCoveredVertex H R center v)
    (hedges : ∀ u v,H.Adj u v → PathCoveredEdge H R center u v)
    (color color' : V → A) (hinj : Function.Injective color)
    (hcodes : ∀ i,pathNeighborhoodCode H R color' (center i)=pathNeighborhoodCode H R color (center i)) :
    ∃ e : H ≃g H,(∀ i,e (center i)=center i) ∧ ∀ v,color' (e v)=color v := by
  have hex (v : V) : ∃ v' : V,color' v'=color v := by
    obtain ⟨i,n,p,hp0,hp,j,hj⟩ := hvertices v
    obtain ⟨p',_,_,hc⟩ := pathNeighborhoodCode_transport H R color color' (center i) (hcodes i) n p hp0 hp
    exact ⟨p' j,(hc j).trans (congrArg color hj)⟩
  let f (v : V) := (hex v).choose
  have hf (v : V) : color' (f v)=color v := (hex v).choose_spec
  have hfinj : Function.Injective f := by
    intro v w hvw
    exact hinj ((hf v).symm.trans ((congrArg color' hvw).trans (hf w)))
  have hfsurj := Finite.surjective_of_injective hfinj
  let e : Equiv.Perm V := Equiv.ofBijective f ⟨hfinj,hfsurj⟩
  have hcolor'inj : Function.Injective color' := by
    intro v' w' hcw
    obtain ⟨v,rfl⟩ := hfsurj v'
    obtain ⟨w,rfl⟩ := hfsurj w'
    exact congrArg f (hinj ((hf v).symm.trans (hcw.trans (hf w))))
  have hfixed (i : I) : f (center i)=center i := by
    apply hcolor'inj
    have hc0 : color (center i)=color' (center i) := by
      apply (pathNeighborhoodCode_zero_iff H R color' (center i) _).mp
      rw [hcodes]
      exact (pathNeighborhoodCode_zero_iff H R color (center i) _).mpr rfl
    exact (hf _).trans hc0
  have hmap (u v : V) (huv : H.Adj u v) : H.Adj (f u) (f v) := by
    rcases hedges u v huv with hcentral | ⟨i,n,p,hp0,hp,j,hj⟩
    · obtain ⟨i,l,hi,hl⟩ := hcentral
      rw [← hi,← hl,hfixed,hfixed]
      simpa only [hi,hl] using huv
    · obtain ⟨p',_,hp',hc⟩ := pathNeighborhoodCode_transport H R color color' (center i) (hcodes i) n p hp0 hp
      have heq (a : Fin (n.val+1)) : p' a=f (p a) := hcolor'inj ((hc a).trans (hf (p a)).symm)
      have hh := hp' j
      rw [heq,heq] at hh
      rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hh
      · exact H.symm hh
  exact ⟨graphIsoOfAdjacencyPreservingPerm H e hmap,hfixed,hf⟩

def centerPathCodes (H : SimpleGraph V) (R : ℕ) (center : I → V) (color : V → A) :
    I → PathNeighborhoodCode A R := fun i => pathNeighborhoodCode H R color (center i)

theorem centerPathCodes_graphIso (H : SimpleGraph V) (R : ℕ) (center : I → V)
    (e : H ≃g H) (hfixed : ∀ i,e (center i)=center i) (color : V → A) :
    centerPathCodes H R center (color ∘ e.symm)=centerPathCodes H R center color := by
  funext i
  have h := pathNeighborhoodCode_graphIso e R color (center i)
  simpa only [hfixed] using h

/-- A concrete center stabilizer action turns the gluing theorem into the
Good-label orbit-recovery property used in marker entropy cancellation.
The completeness premise here is solely finite graph geometry. -/
theorem centerPathCodes_recover_orbit {G : Type*} [Group G] [MulAction G V] [Fintype V]
    (H : SimpleGraph V) (R : ℕ) (center : I → V)
    (hvertices : ∀ v,PathCoveredVertex H R center v)
    (hedges : ∀ u v,H.Adj u v → PathCoveredEdge H R center u v)
    (hcomplete : ∀ e : H ≃g H,(∀ i,e (center i)=center i) → ∃ g : G,∀ v,g • v=e v)
    (color color' : V → A) (hinj : Function.Injective color)
    (hcodes : centerPathCodes H R center color'=centerPathCodes H R center color) :
    letI : MulAction G (V → A) := arrowAction
    color' ∈ MulAction.orbit G color := by
  letI : MulAction G (V → A) := arrowAction
  obtain ⟨e,hfixed,hmatch⟩ := pathCode_gluing_graphIso H R center hvertices hedges color color' hinj
    (fun i => congrFun hcodes i)
  obtain ⟨g,hg⟩ := hcomplete e hfixed
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨g,?_⟩
  funext v
  have h := hmatch (g⁻¹ • v)
  rw [← hg,smul_inv_smul] at h
  exact h.symm

theorem centerPathCodes_action_invariant {G : Type*} [Group G] [MulAction G V]
    (H : SimpleGraph V) (R : ℕ) (center : I → V)
    (actionIso : G → H ≃g H) (hact : ∀ g v,actionIso g v=g • v)
    (hfixed : ∀ (g : G) (i : I),g • center i=center i) (g : G) (color : V → A) :
    centerPathCodes H R center (fun v => color (g⁻¹ • v))=centerPathCodes H R center color := by
  have hinv (v : V) : (actionIso g).symm v=g⁻¹ • v := by
    apply (actionIso g).injective
    rw [(actionIso g).apply_symm_apply,hact,smul_inv_smul]
  have h := centerPathCodes_graphIso H R center (actionIso g) (fun i => by rw [hact,hfixed]) color
  have heq : color ∘ (actionIso g).symm=(fun v => color (g⁻¹ • v)) := by
    funext v
    rw [Function.comp_apply,hinv]
  rw [heq] at h
  exact h

theorem centerPathCodes_recover_of_injective_markers {G F M : Type*}
    [Group G] [MulAction G V] [Fintype V]
    (H : SimpleGraph V) (R : ℕ) (center : I → V)
    (hvertices : ∀ v,PathCoveredVertex H R center v)
    (hedges : ∀ u v,H.Adj u v → PathCoveredEdge H R center u v)
    (hcomplete : ∀ e : H ≃g H,(∀ i,e (center i)=center i) → ∃ g : G,∀ v,g • v=e v)
    (color color' : V → F × M) (hmarkers : Function.Injective (fun v => (color v).2))
    (hcodes : centerPathCodes H R center color'=centerPathCodes H R center color) :
    letI : MulAction G (V → F × M) := arrowAction
    color' ∈ MulAction.orbit G color :=
  centerPathCodes_recover_orbit H R center hvertices hedges hcomplete color color'
    (fun u v huv => hmarkers (congrArg Prod.snd huv)) hcodes

end GaussianWave.BS.Lower
