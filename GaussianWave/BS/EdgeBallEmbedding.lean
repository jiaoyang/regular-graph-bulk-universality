import GaussianWave.BS.EdgeCoverSampling

/-! Literal edge balls embedded in the actual word tree. Edge reversal is
the actual root-edge-flip isomorphism, and these edge balls exhaust the tree. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS

/-- Decode the two endpoint branches using the actual edge-half chart. -/
def edgeBallEmbedding (m k : ℕ) (v : EdgeBallVertex (m+2) k) : RegularTreeVertex (m+2) :=
  treeHalfDecode (m+1) (v.1,(branchPath (m+1) k v.2).reverse)

theorem edgeBallEmbedding_injective (m k : ℕ) : Function.Injective (edgeBallEmbedding m k) := by
  intro v w h
  have hh := (treeHalfEquiv (m+1)).symm.injective h
  apply Prod.ext
  · exact congrArg (fun z : Bool × List (Fin (m+1)) => z.1) hh
  · apply branchPath_injective (m+1) k
    apply List.reverse_injective
    exact congrArg Prod.snd hh

/-- The edge flip swaps the two actual embedded branch coordinates. -/
theorem edgeBallEmbedding_reverse (m k : ℕ) (v : EdgeBallVertex (m+2) k) :
    regularTreeEdgeFlip (m+1) (edgeBallEmbedding m k v)=
      edgeBallEmbedding m k (edgeBallReverse m k v) := by
  change (treeHalfEquiv (m+1)).symm
    ((boolFlipEquiv.prodCongr (Equiv.refl _))
      ((treeHalfEquiv (m+1)) ((treeHalfEquiv (m+1)).symm
        (v.1,(branchPath (m+1) k v.2).reverse))))=_
  rw [Equiv.apply_symm_apply]
  rfl

/-- Actual distance from the nearer endpoint, represented by the edge-half
word length. -/
def regularTreeEdgeDepth (m : ℕ) (v : RegularTreeVertex (m+2)) : ℕ :=
  (treeHalfEncode (m+1) v).2.length

theorem edgeBallEmbedding_edgeDepth (m k : ℕ) (v : EdgeBallVertex (m+2) k) :
    regularTreeEdgeDepth m (edgeBallEmbedding m k v)≤k := by
  unfold regularTreeEdgeDepth edgeBallEmbedding
  have he : treeHalfEncode (m+1) (treeHalfDecode (m+1)
      (v.1,(branchPath (m+1) k v.2).reverse)) =
      (v.1,(branchPath (m+1) k v.2).reverse) :=
    (treeHalfEquiv (m+1)).apply_symm_apply (v.1,(branchPath (m+1) k v.2).reverse)
  change (treeHalfEncode (m+1) (treeHalfDecode (m+1) _)).2.length≤k
  rw [he]
  simpa only [List.length_reverse] using branchPath_length_le (m+1) k v.2

theorem edgeBallEmbedding_range (m k : ℕ) :
    Set.range (edgeBallEmbedding m k)={v | regularTreeEdgeDepth m v≤k} := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    exact edgeBallEmbedding_edgeDepth m k w
  · intro hv
    let bw := treeHalfEncode (m+1) v
    have he : treeHalfDecode (m+1) bw=v := (treeHalfEquiv (m+1)).symm_apply_apply v
    have hw : bw.2.reverse.length≤k := by simpa only [bw,regularTreeEdgeDepth,List.length_reverse] using hv
    obtain ⟨z,hz⟩ := branchPath_exists (m+1) k bw.2.reverse hw
    refine ⟨(bw.1,z),?_⟩
    simp only [edgeBallEmbedding,hz,List.reverse_reverse]
    exact he

theorem edgeBallEmbedding_exhausts (m : ℕ) (v : RegularTreeVertex (m+2)) :
    ∃ k, v ∈ Set.range (edgeBallEmbedding m k) := by
  refine ⟨regularTreeEdgeDepth m v,?_⟩
  rw [edgeBallEmbedding_range]
  change regularTreeEdgeDepth m v≤regularTreeEdgeDepth m v
  exact le_refl _

/-- The coordinate inclusion of the edge ball into the same-index vertex
ball; only the unused left-branch last layer is omitted. -/
def edgeToVertexBall (m : ℕ) : (k : ℕ) → EdgeBallVertex (m+2) k → VertexBallVertex (m+2) k
  | k,(true,v) => Sum.inr (0,v)
  | 0,(false,_) => Sum.inl ()
  | k+1,(false,Sum.inl _) => Sum.inl ()
  | k+1,(false,Sum.inr (a,v)) => Sum.inr (a.succ,branchVertexInclusion (m+1) k v)

theorem edgeToVertexBall_embedding (m k : ℕ) (v : EdgeBallVertex (m+2) k) :
    vertexBallEmbedding (m+2) k (edgeToVertexBall m k v)=edgeBallEmbedding m k v := by
  rcases v with ⟨b,v⟩
  cases b with
  | true => simp [vertexBallEmbedding,edgeToVertexBall,edgeBallEmbedding,treeHalfDecode]
  | false =>
    cases k with
    | zero => cases v; rfl
    | succ k =>
      cases v with
      | inl u => rfl
      | inr av =>
        change some (av.1.succ,(branchPath (m+1) (k+1) (branchVertexInclusion (m+1) k av.2)).reverse)=_
        rw [branchPath_inclusion]
        simp only [edgeBallEmbedding,branchPath,List.reverse_cons,treeHalfDecode_false_append]


/-- A finite collection of sites is contained in one actual E-ball. -/
def finiteEdgeDepth (m : ℕ) (S : Finset (RegularTreeVertex (m+2))) : ℕ :=
  S.sup (regularTreeEdgeDepth m)

theorem edgeDepth_le_finiteEdgeDepth (m : ℕ) (S : Finset (RegularTreeVertex (m+2)))
    (v : S) : regularTreeEdgeDepth m v.val≤finiteEdgeDepth m S :=
  Finset.le_sup v.property

/-- An actual finite-ball coordinate of a site proved to lie in it. -/
def edgeBallIndexOfDepth (m k : ℕ) (v : RegularTreeVertex (m+2))
    (h : regularTreeEdgeDepth m v≤k) : EdgeBallVertex (m+2) k :=
  Classical.choose (show v ∈ Set.range (edgeBallEmbedding m k) by
    rw [edgeBallEmbedding_range]
    exact h)

theorem edgeBallIndexOfDepth_spec (m k : ℕ) (v : RegularTreeVertex (m+2))
    (h : regularTreeEdgeDepth m v≤k) :
    edgeBallEmbedding m k (edgeBallIndexOfDepth m k v h)=v :=
  Classical.choose_spec (show v ∈ Set.range (edgeBallEmbedding m k) by
    rw [edgeBallEmbedding_range]
    exact h)

end GaussianWave.BS
