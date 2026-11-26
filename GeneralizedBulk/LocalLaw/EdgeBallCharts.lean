import GeneralizedBulk.Graph.FiniteTreeBall
import GaussianWave.BS.Lower.PathEdgeComparison

/-! Identify the bulk project's finite word edge tree with an induced ball
of the actual regular word tree used by the constructive BS cover. -/
noncomputable section
open scoped Classical
namespace GeneralizedBulk.Graph
open GaussianWave.BS

def edgeSideBool : Fin 2 ≃ Bool where
  toFun i := i = 1
  invFun b := if b then 1 else 0
  left_inv i := by fin_cases i <;> rfl
  right_inv b := by cases b <;> rfl

def boundedWordList (q R : ℕ) : (Σ k : Fin (R+1), Fin k.val → Fin q) → List (Fin q) :=
  fun k => List.ofFn k.2

theorem boundedWordList_injective (q R : ℕ) : Function.Injective (boundedWordList q R) := by
  rintro ⟨i,f⟩ ⟨j,g⟩ h
  have hij : i = j := Fin.ext (by simpa [boundedWordList] using congrArg List.length h)
  subst j
  have hfg : f = g := List.ofFn_injective h
  cases hfg
  rfl

theorem boundedWordList_exists (q R : ℕ) (w : List (Fin q)) (hw : w.length ≤ R) :
    ∃ v, boundedWordList q R v = w := by
  exact ⟨⟨⟨w.length,by omega⟩,w.get⟩,List.ofFn_get w⟩

def edgeWordEmbedding (m R : ℕ) (v : EdgeTreeVertex (m+2) R) : RegularTreeVertex (m+2) :=
  treeHalfDecode (m+1) (edgeSideBool v.1,edgeTreeWord v)

theorem edgeWordEmbedding_injective (m R : ℕ) : Function.Injective (edgeWordEmbedding m R) := by
  intro v w h
  have hp := (treeHalfEquiv (m+1)).symm.injective h
  apply Prod.ext
  · exact edgeSideBool.injective (congrArg Prod.fst hp)
  · exact boundedWordList_injective (m+1) R (congrArg Prod.snd hp)

@[simp] theorem edgeTreeWord_nil_iff {d R : ℕ} (v : EdgeTreeVertex d R) :
    edgeTreeWord v = [] ↔ v.2.1.val = 0 := by simp [edgeTreeWord]

@[simp] theorem edgeWordEmbedding_root_zero (m R : ℕ) :
    edgeWordEmbedding m R (edgeTreeRoot (m+2) R 0) = none := by
  simp [edgeWordEmbedding,edgeTreeRoot,edgeTreeWord,edgeSideBool,treeHalfDecode]

@[simp] theorem edgeWordEmbedding_root_one (m R : ℕ) :
    edgeWordEmbedding m R (edgeTreeRoot (m+2) R 1) = some (0,[]) := by
  simp [edgeWordEmbedding,edgeTreeRoot,edgeTreeWord,edgeSideBool,treeHalfDecode]

theorem treeHalfDecode_adj_true (q : ℕ) (w z : List (Fin q)) :
    (regularWordTree (q+1)).Adj (treeHalfDecode q (true,w)) (treeHalfDecode q (true,z)) ↔
      (∃ a, w = a::z) ∨ (∃ a, z = a::w) := by
  cases w <;> cases z <;>
    simp [treeHalfDecode,regularWordTree,regularTreeParent,List.cons.injEq]

theorem treeHalfDecode_adj_same (q : ℕ) (b : Bool) (w z : List (Fin q)) :
    (regularWordTree (q+1)).Adj (treeHalfDecode q (b,w)) (treeHalfDecode q (b,z)) ↔
      (∃ a, w = a::z) ∨ (∃ a, z = a::w) := by
  cases b with
  | true => exact treeHalfDecode_adj_true q w z
  | false =>
    have hw : regularTreeEdgeFlip q (treeHalfDecode q (true,w)) = treeHalfDecode q (false,w) := by
      change treeHalfDecode q (boolFlipEquiv.prodCongr (Equiv.refl _) ((treeHalfEquiv q)
        ((treeHalfEquiv q).symm (true,w)))) = _
      rw [(treeHalfEquiv q).apply_symm_apply]
      rfl
    have hz : regularTreeEdgeFlip q (treeHalfDecode q (true,z)) = treeHalfDecode q (false,z) := by
      change treeHalfDecode q (boolFlipEquiv.prodCongr (Equiv.refl _) ((treeHalfEquiv q)
        ((treeHalfEquiv q).symm (true,z)))) = _
      rw [(treeHalfEquiv q).apply_symm_apply]
      rfl
    rw [← hw,← hz,(regularTreeEdgeFlip q).map_rel_iff]
    exact treeHalfDecode_adj_true q w z

theorem treeHalfDecode_adj_cross (q : ℕ) (w z : List (Fin q)) :
    (regularWordTree (q+1)).Adj (treeHalfDecode q (false,w)) (treeHalfDecode q (true,z)) ↔
      w = [] ∧ z = [] := by
  induction w using List.reverseRecOn with
  | nil => cases z <;> simp [treeHalfDecode,regularWordTree,regularTreeParent]
  | append_singleton w a ih =>
    rw [treeHalfDecode_false_append]
    cases w <;> cases z <;>
      simp [treeHalfDecode,regularWordTree,regularTreeParent,Fin.succ_ne_zero,
        Ne.symm (Fin.succ_ne_zero a)]

theorem edgeWordEmbedding_adj (m R : ℕ) (v w : EdgeTreeVertex (m+2) R) :
    (regularWordTree (m+2)).Adj (edgeWordEmbedding m R v) (edgeWordEmbedding m R w) ↔
      (finiteEdgeTreeBall (m+2) R).Adj v w := by
  rcases v with ⟨a,v⟩
  rcases w with ⟨b,w⟩
  have hv : edgeTreeWord (a,v) = [] ↔ v.1.val = 0 := by simp [edgeTreeWord]
  have hw : edgeTreeWord (b,w) = [] ↔ w.1.val = 0 := by simp [edgeTreeWord]
  fin_cases a <;> fin_cases b
  · simpa [edgeWordEmbedding,edgeSideBool,finiteEdgeTreeBall,edgeTreeWord] using
      treeHalfDecode_adj_same (m+1) false (edgeTreeWord (0,v)) (edgeTreeWord (0,w))
  · simpa [edgeWordEmbedding,edgeSideBool,finiteEdgeTreeBall,edgeTreeWord] using
      treeHalfDecode_adj_cross (m+1) (edgeTreeWord (0,v)) (edgeTreeWord (1,w))
  · have h := treeHalfDecode_adj_cross (m+1) (edgeTreeWord (0,w)) (edgeTreeWord (1,v))
    rw [(regularWordTree (m+2)).adj_comm]
    simpa [edgeWordEmbedding,edgeSideBool,finiteEdgeTreeBall,edgeTreeWord,and_comm] using h
  · simpa [edgeWordEmbedding,edgeSideBool,finiteEdgeTreeBall] using
      treeHalfDecode_adj_same (m+1) true (edgeTreeWord (1,v)) (edgeTreeWord (1,w))

theorem edgeWordEmbedding_range (m R : ℕ) :
    Set.range (edgeWordEmbedding m R) = {v | regularTreeEdgeDepth m v ≤ R} := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    unfold regularTreeEdgeDepth edgeWordEmbedding
    have he := (treeHalfEquiv (m+1)).apply_symm_apply (edgeSideBool w.1,edgeTreeWord w)
    change treeHalfEncode (m+1) (treeHalfDecode (m+1) (edgeSideBool w.1,edgeTreeWord w)) =
      (edgeSideBool w.1,edgeTreeWord w) at he
    change (treeHalfEncode (m+1) (treeHalfDecode (m+1) _)).2.length ≤ R
    rw [he]
    simp only [edgeTreeWord,List.length_ofFn]
    exact Nat.le_of_lt_succ w.2.1.isLt
  · intro hv
    let bw := treeHalfEncode (m+1) v
    have hlen : bw.2.length ≤ R := hv
    obtain ⟨w,hw⟩ := boundedWordList_exists (m+1) R bw.2 hlen
    refine ⟨(edgeSideBool.symm bw.1,w),?_⟩
    change treeHalfDecode (m+1) (edgeSideBool (edgeSideBool.symm bw.1),boundedWordList (m+1) R w) = v
    rw [edgeSideBool.apply_symm_apply,hw]
    exact (treeHalfEquiv (m+1)).symm_apply_apply v

theorem regularTree_edist_le_of_dist_le (d : ℕ) (a b : RegularTreeVertex d) (R : ℕ)
    (h : (regularWordTree d).dist a b ≤ R) :
    (regularWordTree d).edist a b ≤ (R : ℕ∞) := by
  obtain ⟨p,hp⟩ := (regularWordTree_connected d).exists_walk_length_eq_dist a b
  exact p.edist_le.trans (by exact_mod_cast hp.trans_le h)

theorem wordTreeEdgeBall_eq_depth (m R : ℕ) :
    graphEdgeBall (regularWordTree (m+2)) none (some (0,[])) R =
      {v | regularTreeEdgeDepth m v ≤ R} := by
  ext v
  constructor
  · intro hv
    rw [← edgeBallEmbedding_range]
    rcases hv with hv | hv
    · exact GaussianWave.BS.Lower.edgeBall_endpoint_ball_subset m R false v
        (by simpa using hv)
    · exact GaussianWave.BS.Lower.edgeBall_endpoint_ball_subset m R true v
        (by simpa using hv)
  · intro hv
    obtain ⟨⟨b,w⟩,rfl⟩ := (Set.ext_iff.mp (edgeBallEmbedding_range m R) v).mpr hv
    have hd : (regularWordTree (m+2)).dist
        (edgeBallEmbedding m R (edgeBallRoot m R b))
        (edgeBallEmbedding m R (b,w)) ≤ R := by
      have he := (edgeBallParentClosedTree m R).dist_embedding (edgeBallRoot m R b) (b,w)
      change (edgeBallGraph m R).dist (edgeBallRoot m R b) (b,w) = _ at he
      exact he.symm.trans_le ((GaussianWave.BS.Lower.edgeBallGraph_dist_root_half m R b w).trans_le
        (branchDepth_le (m+1) R w))
    have he := regularTree_edist_le_of_dist_le (m+2) _ _ R hd
    cases b
    · exact Or.inl (by simpa using he)
    · exact Or.inr (by simpa using he)

def edgeWordBallIso (m R : ℕ) :
    finiteEdgeTreeBall (m+2) R ≃g
      (regularWordTree (m+2)).induce
        (graphEdgeBall (regularWordTree (m+2)) none (some (0,[])) R) where
  toEquiv := Equiv.ofBijective (fun v : EdgeTreeVertex (m+2) R =>
    (⟨edgeWordEmbedding m R v,by
      rw [wordTreeEdgeBall_eq_depth,← edgeWordEmbedding_range]
      exact ⟨v,rfl⟩⟩ : graphEdgeBall (regularWordTree (m+2)) none (some (0,[])) R))
    ⟨by
      intro v w h
      exact edgeWordEmbedding_injective m R (congrArg Subtype.val h),by
      intro v
      have hv := (Set.ext_iff.mp (wordTreeEdgeBall_eq_depth m R) v.val).mp v.property
      have hv := (Set.ext_iff.mp (edgeWordEmbedding_range m R) v.val).mpr hv
      obtain ⟨w,hw⟩ := hv
      exact ⟨w,Subtype.ext hw⟩⟩
  map_rel_iff' := by intro a b; exact edgeWordEmbedding_adj m R a b

end GeneralizedBulk.Graph
