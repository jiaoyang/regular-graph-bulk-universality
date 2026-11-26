import Mathlib
import GaussianWave.BS.RegularTree
import GaussianWave.BS.TreeBallEmbedding

/-! Exact distance and radial-neighbor geometry of the actual regular word
tree. Shortest paths and sphere counts are proved from its constructed graph. -/
noncomputable section
open scoped BigOperators Classical
namespace GaussianWave.BS

variable {V : Type*} {G : SimpleGraph V}

/-- Every simple path in a tree is a shortest path. -/
theorem tree_path_length_eq_dist (hT : G.IsTree) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q, hq, hqd⟩ := hT.isConnected.exists_path_of_dist u v
  have he : p = q := congrArg Subtype.val (hT.IsAcyclic.path_unique ⟨p, hp⟩ ⟨q, hq⟩)
  rw [he]
  exact hqd

/-- A neighbor of the initial vertex that lies along a simple tree path is
its first step. -/
theorem tree_adj_mem_path_eq_first (hT : G.IsTree) {u w v z : V}
    (huw : G.Adj u w) (p : G.Walk w v) (hp : (SimpleGraph.Walk.cons huw p).IsPath)
    (huz : G.Adj u z) (hz : z ∈ (SimpleGraph.Walk.cons huw p).support) : z = w := by
  let q := SimpleGraph.Walk.cons huw p
  have hq : q.IsPath := hp
  have he : q.takeUntil z hz = SimpleGraph.Walk.cons huz SimpleGraph.Walk.nil :=
    congrArg Subtype.val (hT.IsAcyclic.path_unique ⟨_, hq.takeUntil hz⟩
      ⟨_, SimpleGraph.Walk.IsPath.nil.cons (by simpa using huz.ne)⟩)
  have hg := congrArg (fun r : G.Walk u z => r.getVert 1) he
  change (q.takeUntil z hz).getVert 1 = (SimpleGraph.Walk.cons huz SimpleGraph.Walk.nil).getVert 1 at hg
  have hget := q.getVert_takeUntil hz (show 1 ≤ (q.takeUntil z hz).length by simp [he])
  rw [hget] at hg
  simpa [q] using hg.symm

/-- Exactly one neighbor points inward toward a distinct target; every
other neighbor is one step farther from that target. -/
theorem tree_neighbor_distances (hT : G.IsTree) (u v : V) (hne : u ≠ v) :
    ∃ w : V, G.Adj u w ∧ G.dist w v + 1 = G.dist u v ∧
      ∀ z, G.Adj u z → z ≠ w → G.dist z v = G.dist u v + 1 := by
  obtain ⟨p, hp, hpd⟩ := hT.isConnected.exists_path_of_dist u v
  cases p with
  | nil => exact False.elim (hne rfl)
  | @cons u w v huw p =>
    refine ⟨w, huw, ?_, ?_⟩
    · rw [← tree_path_length_eq_dist hT p hp.of_cons, ← hpd]
      rfl
    · intro z huz hzw
      have hz : z ∉ (SimpleGraph.Walk.cons huw p).support := by
        intro hz
        exact hzw (tree_adj_mem_path_eq_first hT huw p hp huz hz)
      have hpp := hp.cons hz (h := huz.symm)
      have hlen := tree_path_length_eq_dist hT (SimpleGraph.Walk.cons huz.symm (SimpleGraph.Walk.cons huw p)) hpp
      simpa only [SimpleGraph.Walk.length_cons, hpd] using hlen.symm

/-- Every edge changes word depth by exactly one. -/
theorem regularTree_adj_depth {d : ℕ} {u v : RegularTreeVertex d}
    (h : (regularWordTree d).Adj u v) :
    regularTreeDepth u+1=regularTreeDepth v ∨ regularTreeDepth v+1=regularTreeDepth u := by
  rcases h with ⟨hu, hpu⟩ | ⟨hv, hpv⟩
  · right
    cases u with
    | none => exact False.elim (hu rfl)
    | some aw => simpa only [hpu] using regularTreeDepth_parent aw.1 aw.2
  · left
    cases v with
    | none => exact False.elim (hv rfl)
    | some aw => simpa only [hpv] using regularTreeDepth_parent aw.1 aw.2

/-- The depth difference is bounded by every walk length. -/
theorem regularTreeDepth_le_walk {d : ℕ} {u v : RegularTreeVertex d}
    (p : (regularWordTree d).Walk u v) : regularTreeDepth v ≤ regularTreeDepth u+p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rcases regularTree_adj_depth h with h | h <;>
      simp only [SimpleGraph.Walk.length_cons] <;> omega

/-- A constructed parent walk has length exactly the word depth. -/
def regularTreeParentWalk (d : ℕ) : (v : RegularTreeVertex d) → (regularWordTree d).Walk v none
  | none => .nil
  | some (a, []) => .cons (regularTreeNeighbor_adj (some (a, [])) none) .nil
  | some (a, b::w) => .cons (regularTreeNeighbor_adj (some (a, b::w)) none)
      (regularTreeParentWalk d (some (a,w)))

@[simp] theorem regularTreeParentWalk_length (d : ℕ) (v : RegularTreeVertex d) :
    (regularTreeParentWalk d v).length = regularTreeDepth v := by
  cases v with
  | none => simp [regularTreeParentWalk, regularTreeDepth]
  | some aw =>
    rcases aw with ⟨a,w⟩
    induction w with
    | nil => simp [regularTreeParentWalk, regularTreeDepth]
    | cons b w ih => simpa [regularTreeParentWalk, regularTreeDepth] using ih

/-- Word depth is the actual graph distance from the root. -/
theorem regularTree_dist_root (d : ℕ) (v : RegularTreeVertex d) :
    (regularWordTree d).dist none v = regularTreeDepth v := by
  apply le_antisymm
  · have h := (regularWordTree d).dist_le (regularTreeParentWalk d v).reverse
    simpa using h
  · obtain ⟨p, hp, hpd⟩ := (regularWordTree_connected d).exists_path_of_dist none v
    have h := regularTreeDepth_le_walk p
    simpa only [regularTreeDepth, zero_add, hpd] using h


/-- Adjacency sums of radial functions on a regular tree have the exact
one-inward, `d-1`-outward form. -/
theorem tree_sum_neighbor_radial [G.LocallyFinite] (hT : G.IsTree) (d : ℕ)
    (hd : G.IsRegularOfDegree d) (f : ℕ → ℝ) (u v : V) :
    (∑ z : G.neighborSet u, f (G.dist z v)) =
      if u=v then (d : ℝ)*f 1 else
        f (G.dist u v-1)+((d : ℝ)-1)*f (G.dist u v+1) := by
  have hc : Fintype.card (G.neighborSet u)=d :=
    (SimpleGraph.card_neighborSet_eq_degree G u).trans (hd u)
  by_cases huv : u=v
  · subst v
    rw [if_pos rfl]
    have he (z : G.neighborSet u) : G.dist z u=1 :=
      SimpleGraph.dist_eq_one_iff_adj.2 z.property.symm
    simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  · rw [if_neg huv]
    obtain ⟨w, huw, hdist, hout⟩ := tree_neighbor_distances hT u v huv
    let wi : G.neighborSet u := ⟨w, huw⟩
    have he (z : G.neighborSet u) : f (G.dist z v) =
        (if z=wi then f (G.dist w v)-f (G.dist u v+1) else 0)+f (G.dist u v+1) := by
      by_cases hz : z=wi
      · subst z
        simp [wi]
      · have hz' : (z : V) ≠ w := by
          intro hz'
          exact hz (Subtype.ext hz')
        rw [hout z z.property hz', if_neg hz]
        simp
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, hc]
    have hd' : G.dist w v=G.dist u v-1 := by omega
    rw [hd']
    ring

/-- Each nonroot shell is the literal finite set of `d` first letters and
`n` subsequent letters, with no counting hypothesis. -/
def regularTreeRootSphereSuccEquiv (d n : ℕ) :
    {v : RegularTreeVertex d // regularTreeDepth v=n+1} ≃
      Fin d × List.Vector (Fin (d-1)) n where
  toFun v := by
    rcases v with ⟨v,hv⟩
    cases v with
    | none => simp [regularTreeDepth] at hv
    | some aw =>
      exact ⟨aw.1, ⟨aw.2, by simpa only [regularTreeDepth, Nat.add_right_cancel_iff] using hv⟩⟩
  invFun p := ⟨some (p.1,p.2.val), by simp [regularTreeDepth, p.2.property]⟩
  left_inv v := by
    rcases v with ⟨v,hv⟩
    cases v with
    | none => simp [regularTreeDepth] at hv
    | some aw => rfl
  right_inv p := by rcases p with ⟨a,⟨w,hw⟩⟩; rfl

def regularTreeRootSphereZeroEquiv (d : ℕ) :
    {v : RegularTreeVertex d // regularTreeDepth v=0} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨none,rfl⟩
  left_inv v := by
    rcases v with ⟨v,hv⟩
    cases v with
    | none => rfl
    | some aw => simp [regularTreeDepth] at hv
  right_inv u := by cases u; rfl

instance regularTreeRootSphereFintype (d n : ℕ) :
    Fintype {v : RegularTreeVertex d // regularTreeDepth v=n} := by
  cases n with
  | zero => exact Fintype.ofEquiv Unit (regularTreeRootSphereZeroEquiv d).symm
  | succ n =>
    exact Fintype.ofEquiv (Fin d × List.Vector (Fin (d-1)) n)
      (regularTreeRootSphereSuccEquiv d n).symm

theorem regularTreeRootSphere_card (d n : ℕ) :
    Fintype.card {v : RegularTreeVertex d // regularTreeDepth v=n+1} = d*(d-1)^n := by
  rw [Fintype.card_congr (regularTreeRootSphereSuccEquiv d n), Fintype.card_prod,
    Fintype.card_fin, Fintype.card_congr (Equiv.vectorEquivFin (Fin (d-1)) n)]
  simp

/-- Every distance ball is actually finite, including balls centered away
from the distinguished word root. -/
theorem regularTree_ball_finite (d : ℕ) (u : RegularTreeVertex d) (n : ℕ) :
    {v | (regularWordTree d).dist u v ≤ n}.Finite := by
  apply (Set.finite_range (vertexBallEmbedding d (regularTreeDepth u+n))).subset
  intro v hv
  rw [vertexBallEmbedding_range]
  have ht := (regularWordTree_connected d).dist_triangle (u := none) (v := u) (w := v)
  rw [regularTree_dist_root d u, regularTree_dist_root d v] at ht
  dsimp only [Set.mem_setOf_eq] at hv ⊢
  omega

instance regularTreeSphereFintype (d : ℕ) (u : RegularTreeVertex d) (n : ℕ) :
    Fintype {v | (regularWordTree d).dist u v=n} :=
  (regularTree_ball_finite d u n |>.subset (by intro v hv; exact le_of_eq hv)).fintype


/-- The inward neighbor is unique as an actual graph vertex. -/
theorem tree_inward_neighbor_unique (hT : G.IsTree) (u v : V) (hne : u ≠ v) :
    ∃! w, G.Adj u w ∧ G.dist w v+1=G.dist u v := by
  obtain ⟨w, huw, hdist, hout⟩ := tree_neighbor_distances hT u v hne
  refine ⟨w, ⟨huw, hdist⟩, ?_⟩
  intro z hz
  by_contra hzw
  have h := hout z hz.1 hzw
  omega

/-- Outward neighbors, as a finite subtype of the actual neighbor set. -/
def TreeForwardNeighbor (G : SimpleGraph V) (u v : V) :=
  {z : G.neighborSet u // G.dist z v=G.dist u v+1}

instance treeForwardNeighborFintype [G.LocallyFinite] (u v : V) :
    Fintype (TreeForwardNeighbor G u v) := inferInstanceAs (Fintype {z : G.neighborSet u // _})

theorem tree_forward_neighbor_card [G.LocallyFinite] (hT : G.IsTree) (d : ℕ)
    (hd : G.IsRegularOfDegree d) (u v : V) (hne : u ≠ v) :
    Fintype.card (TreeForwardNeighbor G u v)=d-1 := by
  obtain ⟨w, huw, hdist, hout⟩ := tree_neighbor_distances hT u v hne
  let wi : G.neighborSet u := ⟨w,huw⟩
  have he (z : G.neighborSet u) : G.dist z v=G.dist u v+1 ↔ z ≠ wi := by
    constructor
    · intro hz heq
      have hval : (z : V)=w := congrArg Subtype.val heq
      rw [hval] at hz
      omega
    · intro hz
      apply hout z z.property
      intro heq
      exact hz (Subtype.ext heq)
  change Fintype.card {z : G.neighborSet u // G.dist z v=G.dist u v+1}=_
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he),
    Fintype.card_subtype_compl (fun z : G.neighborSet u => z=wi), Fintype.card_subtype_eq,
    SimpleGraph.card_neighborSet_eq_degree G u, hd u]

/-- At the center, every actual neighbor points outward. -/
def treeForwardRootEquiv (G : SimpleGraph V) (u : V) :
    TreeForwardNeighbor G u u ≃ G.neighborSet u where
  toFun z := z.val
  invFun z := ⟨z, by
    rw [SimpleGraph.dist_self, zero_add]
    exact SimpleGraph.dist_eq_one_iff_adj.2 z.property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev RegularTreeSphere (d : ℕ) (u : RegularTreeVertex d) (n : ℕ) :=
  {v : RegularTreeVertex d // (regularWordTree d).dist v u=n}

instance regularTreeSphereIncomingFintype (d : ℕ) (u : RegularTreeVertex d) (n : ℕ) :
    Fintype (RegularTreeSphere d u n) := by
  apply Fintype.ofEquiv {v : RegularTreeVertex d | (regularWordTree d).dist u v=n}
  exact Equiv.subtypeEquivRight (fun v => by
    change (regularWordTree d).dist u v=n ↔ (regularWordTree d).dist v u=n
    rw [SimpleGraph.dist_comm])

/-- Every vertex on the next sphere has one and only one inward parent.
This actual bijection supplies sphere counts at every possible center. -/
def regularTreeOutwardSphereEquiv (d : ℕ) (u : RegularTreeVertex d) (n : ℕ) :
    (Σ x : RegularTreeSphere d u n, TreeForwardNeighbor (regularWordTree d) x u) ≃
      RegularTreeSphere d u (n+1) := by
  let F : (Σ x : RegularTreeSphere d u n, TreeForwardNeighbor (regularWordTree d) x u) →
      RegularTreeSphere d u (n+1) :=
    fun z => ⟨z.2.val.val, by rw [z.2.property, z.1.property]⟩
  apply Equiv.ofBijective F
  constructor
  · intro a b hab
    rcases a with ⟨a,az⟩
    rcases b with ⟨b,bz⟩
    have hy : az.val.val=bz.val.val := congrArg Subtype.val hab
    have hdista : (regularWordTree d).dist az.val.val u=n+1 := by rw [az.property, a.property]
    have hne : az.val.val ≠ u := by intro he; simp [he, SimpleGraph.dist_self] at hdista
    obtain ⟨w, hw, huniq⟩ := tree_inward_neighbor_unique (regularWordTree_isTree d) az.val.val u hne
    have hpa : (regularWordTree d).Adj az.val.val a.val ∧
        (regularWordTree d).dist a.val u+1=(regularWordTree d).dist az.val.val u :=
      ⟨az.val.property.symm, az.property.symm⟩
    have hpb : (regularWordTree d).Adj az.val.val b.val ∧
        (regularWordTree d).dist b.val u+1=(regularWordTree d).dist az.val.val u := by
      rw [hy]
      exact ⟨bz.val.property.symm,bz.property.symm⟩
    have hab' : a=b := Subtype.ext ((huniq a.val hpa).trans (huniq b.val hpb).symm)
    subst b
    have haz : az=bz := Subtype.ext (Subtype.ext hy)
    subst bz
    rfl
  · intro y
    have hne : y.val ≠ u := by intro he; have h := y.property; simp [he, SimpleGraph.dist_self] at h
    obtain ⟨w, hw, hdist, hout⟩ := tree_neighbor_distances (regularWordTree_isTree d) y.val u hne
    have hwlevel : (regularWordTree d).dist w u=n := by have h := y.property; omega
    refine ⟨⟨⟨w,hwlevel⟩,⟨⟨y.val,hw.symm⟩,hdist.symm⟩⟩,?_⟩
    rfl

/-- Sphere zero consists of its actual center. -/
theorem regularTreeSphere_zero_card (d : ℕ) (u : RegularTreeVertex d) :
    Fintype.card (RegularTreeSphere d u 0)=1 := by
  apply Fintype.card_eq_one_iff.2
  refine ⟨⟨u,SimpleGraph.dist_self⟩,?_⟩
  intro y
  apply Subtype.ext
  exact (regularWordTree_connected d).dist_eq_zero_iff.1 y.property

/-- Exact sphere cardinality, independent of the chosen center. -/
theorem regularTreeSphere_card (d : ℕ) (hd : 1 ≤ d) (u : RegularTreeVertex d) (n : ℕ) :
    Fintype.card (RegularTreeSphere d u (n+1))=d*(d-1)^n := by
  have hstep (k : ℕ) : Fintype.card (RegularTreeSphere d u (k+1))=
      Fintype.card (RegularTreeSphere d u k)*(if k=0 then d else d-1) := by
    rw [← Fintype.card_congr (regularTreeOutwardSphereEquiv d u k), Fintype.card_sigma]
    have hc (x : RegularTreeSphere d u k) :
        Fintype.card (TreeForwardNeighbor (regularWordTree d) x u)=(if k=0 then d else d-1) := by
      by_cases hk : k=0
      · have hx : x.val=u := (regularWordTree_connected d).dist_eq_zero_iff.1 (by simpa [hk] using x.property)
        simp only [hk, ↓reduceIte]
        rw [hx, Fintype.card_congr (treeForwardRootEquiv (regularWordTree d) u),
          SimpleGraph.card_neighborSet_eq_degree, regularWordTree_regular d hd u]
      · rw [if_neg hk]
        apply tree_forward_neighbor_card (regularWordTree_isTree d) d (regularWordTree_regular d hd)
        intro hx
        have h := x.property
        simp only [hx, SimpleGraph.dist_self] at h
        exact hk h.symm
    simp [hc, Finset.sum_const]
  induction n with
  | zero => rw [hstep, regularTreeSphere_zero_card]; simp
  | succ n ih => rw [hstep, ih]; simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      ↓reduceIte, pow_succ]; ring


abbrev RegularTreeBall (d : ℕ) (u : RegularTreeVertex d) (R : ℕ) :=
  {v : RegularTreeVertex d // (regularWordTree d).dist v u ≤ R}

instance regularTreeBallFintype (d : ℕ) (u : RegularTreeVertex d) (R : ℕ) :
    Fintype (RegularTreeBall d u R) := by
  letI : Fintype {v : RegularTreeVertex d | (regularWordTree d).dist u v ≤ R} :=
    (regularTree_ball_finite d u R).fintype
  apply Fintype.ofEquiv {v : RegularTreeVertex d | (regularWordTree d).dist u v ≤ R}
  exact Equiv.subtypeEquivRight (fun v => by
    change (regularWordTree d).dist u v ≤ R ↔ (regularWordTree d).dist v u ≤ R
    rw [SimpleGraph.dist_comm])

/-- The actual finite ball is the disjoint union of its distance spheres. -/
def regularTreeBallSphereEquiv (d : ℕ) (u : RegularTreeVertex d) (R : ℕ) :
    RegularTreeBall d u R ≃ Σ n : Fin (R+1), RegularTreeSphere d u n.val where
  toFun v := ⟨⟨(regularWordTree d).dist v u, by have h := v.property; omega⟩,⟨v.val,rfl⟩⟩
  invFun z := ⟨z.2.val,by rw [z.2.property]; exact Nat.le_of_lt_succ z.1.isLt⟩
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨⟨n,hn⟩,⟨v,hv⟩⟩
    dsimp only at hv
    subst n
    rfl

/-- Exact radial summation on every actual finite ball. -/
theorem regularTree_sum_ball_radial (d : ℕ) (hd : 1 ≤ d) (u : RegularTreeVertex d)
    (R : ℕ) (f : ℕ → ℝ) :
    (∑ z : RegularTreeBall d u R, f ((regularWordTree d).dist z u)) =
      f 0 + ∑ n ∈ Finset.range R, (d : ℝ)*((d-1 : ℕ) : ℝ)^n*f (n+1) := by
  have he := Equiv.sum_comp (regularTreeBallSphereEquiv d u R)
    (fun z : Σ n : Fin (R+1), RegularTreeSphere d u n.val => f z.1.val)
  change (∑ z : RegularTreeBall d u R, f ((regularWordTree d).dist z u)) =
      ∑ z : Σ n : Fin (R+1), RegularTreeSphere d u n.val, f z.1.val at he
  rw [he, Fintype.sum_sigma, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    regularTreeSphere_zero_card, regularTreeSphere_card d hd, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_one, one_mul]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun n => (d : ℝ)*((d-1 : ℕ) : ℝ)^n*f (n+1)) R


/-- Every finite distance occurs on the actual infinite regular tree. -/
theorem regularTreeSphere_nonempty (d : ℕ) (hd : 2 ≤ d) (u : RegularTreeVertex d) (n : ℕ) :
    Nonempty (RegularTreeSphere d u n) := by
  cases n with
  | zero => exact ⟨⟨u,SimpleGraph.dist_self⟩⟩
  | succ n =>
    apply Fintype.card_pos_iff.1
    rw [regularTreeSphere_card d (by omega)]
    apply Nat.mul_pos (by omega)
    exact pow_pos (by omega) _

end GaussianWave.BS
