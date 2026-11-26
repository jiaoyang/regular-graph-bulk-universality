import GaussianWave.BS.RegularTree
import GaussianWave.BS.GaussianBallConsistency

/-! Concrete finite word-tree balls embed into the countable tree and
exhaust it. These are actual coordinate inclusions for process laws. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS

def branchPath (q : ℕ) : (k : ℕ) → BranchVertex q k → List (Fin q)
  | 0, _ => []
  | _ + 1, Sum.inl _ => []
  | k + 1, Sum.inr (a, v) => a :: branchPath q k v

theorem branchPath_length_le (q k : ℕ) (v : BranchVertex q k) : (branchPath q k v).length ≤ k := by
  induction k with
  | zero => cases v; rfl
  | succ k ih =>
      cases v with
      | inl u => simp [branchPath]
      | inr av => simpa only [branchPath, List.length_cons, Nat.succ_le_succ_iff] using ih av.2

theorem branchPath_injective (q k : ℕ) : Function.Injective (branchPath q k) := by
  induction k with
  | zero => intro v w h; cases v; cases w; rfl
  | succ k ih =>
      intro v w h
      cases v with
      | inl u => cases w with
        | inl z => cases u; cases z; rfl
        | inr aw => exact False.elim (List.noConfusion h)
      | inr av => cases w with
        | inl z => exact False.elim (List.noConfusion h)
        | inr aw =>
            have hh := List.cons.inj h
            have ha := hh.1
            have hv := ih hh.2
            cases av; cases aw
            simp_all

theorem branchPath_exists (q k : ℕ) (w : List (Fin q)) (hw : w.length ≤ k) :
    ∃ v : BranchVertex q k, branchPath q k v = w := by
  induction k generalizing w with
  | zero =>
      have he : w = [] := List.length_eq_zero.mp (Nat.eq_zero_of_le_zero hw)
      exact ⟨(), he.symm⟩
  | succ k ih =>
      cases w with
      | nil => exact ⟨Sum.inl (), rfl⟩
      | cons a w =>
          obtain ⟨v, hv⟩ := ih w (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using hw)
          exact ⟨Sum.inr (a, v), congrArg (List.cons a) hv⟩

theorem branchPath_inclusion (q k : ℕ) (v : BranchVertex q k) :
    branchPath q (k + 1) (branchVertexInclusion q k v) = branchPath q k v := by
  induction k with
  | zero => cases v; rfl
  | succ k ih =>
      cases v with
      | inl u => rfl
      | inr av => exact congrArg (List.cons av.1) (ih av.2)

def vertexBallEmbedding (d k : ℕ) : VertexBallVertex d k → RegularTreeVertex d
  | Sum.inl _ => none
  | Sum.inr (a, v) => some (a, (branchPath (d - 1) k v).reverse)

theorem vertexBallEmbedding_injective (d k : ℕ) : Function.Injective (vertexBallEmbedding d k) := by
  intro v w h
  cases v with
  | inl u => cases w with
    | inl z => cases u; cases z; rfl
    | inr aw => exact False.elim (Option.noConfusion h)
  | inr av => cases w with
    | inl z => exact False.elim (Option.noConfusion h)
    | inr aw =>
        have hh := Option.some.inj h
        have ha := congrArg Prod.fst hh
        have hv := branchPath_injective (d - 1) k
          (List.reverse_injective (congrArg Prod.snd hh))
        cases av; cases aw
        simp_all

theorem vertexBallEmbedding_depth (d k : ℕ) (v : VertexBallVertex d k) :
    regularTreeDepth (vertexBallEmbedding d k v) ≤ k + 1 := by
  cases v with
  | inl u => simp [vertexBallEmbedding, regularTreeDepth]
  | inr av =>
      simpa only [vertexBallEmbedding, regularTreeDepth, List.length_reverse, Nat.succ_le_succ_iff]
        using branchPath_length_le (d - 1) k av.2

theorem vertexBallEmbedding_range (d k : ℕ) :
    Set.range (vertexBallEmbedding d k) = {v | regularTreeDepth v ≤ k + 1} := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact vertexBallEmbedding_depth d k w
  · intro hv
    cases v with
    | none => exact ⟨Sum.inl (), rfl⟩
    | some aw =>
        change aw.2.length + 1 ≤ k + 1 at hv
        have hw : aw.2.reverse.length ≤ k := by
          simpa only [regularTreeDepth, List.length_reverse, Nat.succ_le_succ_iff] using hv
        obtain ⟨w, he⟩ := branchPath_exists (d - 1) k aw.2.reverse hw
        refine ⟨Sum.inr (aw.1, w), ?_⟩
        simp only [vertexBallEmbedding, he, List.reverse_reverse, Prod.mk.eta]

theorem vertexBallEmbedding_inclusion (m k : ℕ) (v : VertexBallVertex (m + 2) k) :
    vertexBallEmbedding (m + 2) (k + 1) (vertexBallInclusion m k v) =
      vertexBallEmbedding (m + 2) k v := by
  cases v with
  | inl u => rfl
  | inr av =>
      exact congrArg (fun w => some (av.1, w.reverse)) (branchPath_inclusion (m + 1) k av.2)

theorem vertexBallEmbedding_exhausts (d : ℕ) (v : RegularTreeVertex d) :
    ∃ k, v ∈ Set.range (vertexBallEmbedding d k) := by
  refine ⟨regularTreeDepth v, ?_⟩
  rw [vertexBallEmbedding_range]
  exact Nat.le_succ _

end GaussianWave.BS
