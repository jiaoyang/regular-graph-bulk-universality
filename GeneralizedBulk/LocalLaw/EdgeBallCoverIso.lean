import GeneralizedBulk.Graph.FiniteTreeBall
import GaussianWave.BS.Lower.LocalCoverCycles
import GaussianWave.BS.InfiniteCoverPathLifting

/-! A locally surjective graph cover, injective on a slightly larger ball,
identifies the literal induced vertex and edge balls. -/
noncomputable section
open scoped Classical
namespace GeneralizedBulk.Graph

variable {V W : Type*} {H : SimpleGraph V} {G : SimpleGraph W}

def geometryBall (H : SimpleGraph V) (a : V) (R : ℕ) : Set V :=
  {v | H.edist a v ≤ (R : ℕ∞)}

theorem cover_lift_walk_edist (F : H →g G)
    (hsurj : ∀ v y, G.Adj (F v) y → ∃ w, H.Adj v w ∧ F w = y)
    {a b : W} (p : G.Walk a b) (x : V) (hx : F x = a) :
    ∃ y, F y = b ∧ H.edist x y ≤ (p.length : ℕ∞) := by
  induction p generalizing x with
  | nil => exact ⟨x,hx,by simp⟩
  | @cons a b c hab p ih =>
    obtain ⟨w,hw,hFw⟩ := hsurj x b (by simpa only [hx] using hab)
    obtain ⟨y,hy,hxy⟩ := ih w hFw
    refine ⟨y,hy,?_⟩
    have he : H.edist x w = 1 := SimpleGraph.edist_eq_one_iff_adj.mpr hw
    calc
      H.edist x y ≤ H.edist x w + H.edist w y := H.edist_triangle
      _ ≤ 1 + (p.length : ℕ∞) := by rw [he]; exact add_le_add_left hxy _
      _ = _ := by simp [SimpleGraph.Walk.length_cons,Nat.cast_add,add_comm]

theorem cover_lift_ball (F : H →g G)
    (hsurj : ∀ v y, G.Adj (F v) y → ∃ w, H.Adj v w ∧ F w = y)
    (a : V) (R : ℕ) (v : W) (hv : G.edist (F a) v ≤ (R : ℕ∞)) :
    ∃ x, F x = v ∧ H.edist a x ≤ (R : ℕ∞) := by
  obtain ⟨p,hp⟩ := G.exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by simp) hv)
  obtain ⟨x,hx,hd⟩ := cover_lift_walk_edist F hsurj p a rfl
  exact ⟨x,hx,hd.trans (hp.trans_le hv)⟩

theorem edgeBall_edist_le (a b : V) (hab : H.Adj a b) (R : ℕ)
    {x : V} (hx : x ∈ graphEdgeBall H a b R) :
    H.edist a x ≤ ((R+1 : ℕ) : ℕ∞) := by
  rcases hx with hx | hx
  · exact hx.trans (by exact_mod_cast Nat.le_succ R)
  · calc
      _ ≤ H.edist a b + H.edist b x := H.edist_triangle
      _ ≤ 1 + (R : ℕ∞) := by
        rw [SimpleGraph.edist_eq_one_iff_adj.mpr hab]
        exact add_le_add_left hx _
      _ = _ := by simp [Nat.cast_add,add_comm]

/-- No extra edges occur between images of the smaller ball. The lift of
an adjacent image remains in the larger ball, where the cover is injective. -/
theorem cover_adj_iff (F : H →g G)
    (hsurj : ∀ v y, G.Adj (F v) y → ∃ w, H.Adj v w ∧ F w = y)
    (a : V) (R : ℕ) (hinj : Set.InjOn F (geometryBall H a (R+1)))
    {x y : V} (hx : H.edist a x ≤ (R : ℕ∞)) (hy : H.edist a y ≤ (R : ℕ∞)) :
    G.Adj (F x) (F y) ↔ H.Adj x y := by
  constructor
  · intro h
    obtain ⟨w,hw,hFw⟩ := hsurj x (F y) h
    have hw' : w ∈ geometryBall H a (R+1) := by
      change H.edist a w ≤ ((R+1 : ℕ) : ℕ∞)
      calc
        _ ≤ H.edist a x + H.edist x w := H.edist_triangle
        _ ≤ (R : ℕ∞) + 1 := by
          rw [SimpleGraph.edist_eq_one_iff_adj.mpr hw]
          exact add_le_add_right hx _
        _ = _ := by simp
    have hy' : y ∈ geometryBall H a (R+1) :=
      hy.trans (by exact_mod_cast Nat.le_succ R)
    have he : w = y := hinj hw' hy' hFw
    simpa only [he] using hw
  · exact F.map_adj

def coverVertexBallIso (F : H →g G)
    (hsurj : ∀ v y, G.Adj (F v) y → ∃ w, H.Adj v w ∧ F w = y)
    (a : V) (R : ℕ) (hinj : Set.InjOn F (geometryBall H a (R+1))) :
    H.induce (geometryBall H a R) ≃g G.induce (geometryBall G (F a) R) where
  toEquiv := Equiv.ofBijective (fun x : geometryBall H a R => (⟨F x.val,
    (GaussianWave.BS.Lower.graphHom_edist_le F a x.val).trans x.property⟩ :
      geometryBall G (F a) R))
    ⟨by
      intro x y h
      apply Subtype.ext
      have hx : x.val ∈ geometryBall H a (R+1) :=
        x.property.trans (show (R : ℕ∞) ≤ ((R+1 : ℕ) : ℕ∞) by exact_mod_cast Nat.le_succ R)
      have hy : y.val ∈ geometryBall H a (R+1) :=
        y.property.trans (show (R : ℕ∞) ≤ ((R+1 : ℕ) : ℕ∞) by exact_mod_cast Nat.le_succ R)
      exact hinj hx hy (congrArg Subtype.val h),by
      intro v
      obtain ⟨x,hx,hd⟩ := cover_lift_ball F hsurj a R v.val v.property
      exact ⟨⟨x,hd⟩,Subtype.ext hx⟩⟩
  map_rel_iff' := by
    intro x y
    exact cover_adj_iff F hsurj a R hinj x.property y.property

def coverEdgeBallIso (F : H →g G)
    (hsurj : ∀ v y, G.Adj (F v) y → ∃ w, H.Adj v w ∧ F w = y)
    (a b : V) (hab : H.Adj a b) (R : ℕ)
    (hinj : Set.InjOn F (geometryBall H a (R+2))) :
    H.induce (graphEdgeBall H a b R) ≃g G.induce (graphEdgeBall G (F a) (F b) R) where
  toEquiv := Equiv.ofBijective (fun x : graphEdgeBall H a b R => (⟨F x.val,by
    rcases x.property with hx | hx
    · exact Or.inl ((GaussianWave.BS.Lower.graphHom_edist_le F a x.val).trans hx)
    · exact Or.inr ((GaussianWave.BS.Lower.graphHom_edist_le F b x.val).trans hx)⟩ :
      graphEdgeBall G (F a) (F b) R))
    ⟨by
      intro x y h
      apply Subtype.ext
      exact hinj ((edgeBall_edist_le a b hab R x.property).trans (by exact_mod_cast Nat.le_succ (R+1)))
        ((edgeBall_edist_le a b hab R y.property).trans (by exact_mod_cast Nat.le_succ (R+1)))
        (congrArg Subtype.val h),by
      intro v
      rcases v.property with hv | hv
      · obtain ⟨x,hx,hd⟩ := cover_lift_ball F hsurj a R v.val hv
        exact ⟨⟨x,Or.inl hd⟩,Subtype.ext hx⟩
      · obtain ⟨x,hx,hd⟩ := cover_lift_ball F hsurj b R v.val hv
        exact ⟨⟨x,Or.inr hd⟩,Subtype.ext hx⟩⟩
  map_rel_iff' := by
    intro x y
    exact cover_adj_iff F hsurj a (R+1) hinj
      (edgeBall_edist_le a b hab R x.property)
      (edgeBall_edist_le a b hab R y.property)

theorem acyclic_of_injective_hom (h : H.IsAcyclic) (F : G →g H)
    (hinj : Function.Injective F) : G.IsAcyclic := by
  intro v p hp
  exact h (p.map F) (hp.map hinj)

end GeneralizedBulk.Graph
