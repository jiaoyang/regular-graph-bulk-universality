import GaussianWave.BS.RealProcessExtension
import GaussianWave.BS.TreeBallEmbedding

/-! Consistent concrete regular-tree ball laws extend to an actual process
law on the countable regular tree. -/
noncomputable section
open MeasureTheory Set
open scoped Topology Classical
namespace GaussianWave.BS

def treeBallIndexOfDepth (d k : ℕ) (v : RegularTreeVertex d)
    (h : regularTreeDepth v ≤ k + 1) : VertexBallVertex d k :=
  Classical.choose (show v ∈ Set.range (vertexBallEmbedding d k) from by
    rw [vertexBallEmbedding_range d k]
    exact h)

theorem treeBallIndexOfDepth_spec (d k : ℕ) (v : RegularTreeVertex d)
    (h : regularTreeDepth v ≤ k + 1) :
    vertexBallEmbedding d k (treeBallIndexOfDepth d k v h) = v :=
  Classical.choose_spec (show v ∈ Set.range (vertexBallEmbedding d k) from by
    rw [vertexBallEmbedding_range d k]
    exact h)

def finiteTreeDepth {d : ℕ} (S : Finset (RegularTreeVertex d)) : ℕ :=
  S.sup regularTreeDepth - 1

theorem depth_le_finiteTreeDepth {d : ℕ} (S : Finset (RegularTreeVertex d))
    (v : S) : regularTreeDepth v.val ≤ finiteTreeDepth S + 1 := by
  have h := Finset.le_sup (f := regularTreeDepth) v.property
  dsimp only [finiteTreeDepth]
  omega

theorem finiteTreeDepth_le_of_embedding (d n : ℕ) (S : Finset (RegularTreeVertex d))
    (hS : ∀ v ∈ S, v ∈ Set.range (vertexBallEmbedding d n)) : finiteTreeDepth S ≤ n := by
  have hmax : S.sup regularTreeDepth ≤ n + 1 := by
    apply Finset.sup_le
    intro v hv
    rw [vertexBallEmbedding_range] at hS
    exact hS v hv
  dsimp only [finiteTreeDepth]
  omega

def treeFiniteRestriction (m : ℕ) (S : Finset (RegularTreeVertex (m + 2)))
    (n : ℕ) (h : finiteTreeDepth S ≤ n) (x : VertexBallVertex (m + 2) n → ℝ) : S → ℝ :=
  fun v => x (treeBallIndexOfDepth (m + 2) n v.val
    ((depth_le_finiteTreeDepth S v).trans (Nat.add_le_add_right h 1)))

theorem continuous_treeFiniteRestriction (m : ℕ) (S : Finset (RegularTreeVertex (m + 2)))
    (n : ℕ) (h : finiteTreeDepth S ≤ n) : Continuous (treeFiniteRestriction m S n h) :=
  continuous_pi (fun _ => continuous_apply _)

theorem treeFiniteRestriction_succ (m : ℕ) (S : Finset (RegularTreeVertex (m + 2)))
    (n : ℕ) (hn : finiteTreeDepth S ≤ n) (x : VertexBallVertex (m + 2) (n + 1) → ℝ) :
    treeFiniteRestriction m S (n + 1) (hn.trans (Nat.le_succ n)) x =
      treeFiniteRestriction m S n hn (fun v => x (vertexBallInclusion m n v)) := by
  funext v
  apply congrArg x
  apply vertexBallEmbedding_injective (m + 2) (n + 1)
  rw [treeBallIndexOfDepth_spec, vertexBallEmbedding_inclusion, treeBallIndexOfDepth_spec]

def finiteMarginalOfBallFamily (m : ℕ)
    (P : ∀ n, ProbabilityMeasure (VertexBallVertex (m + 2) n → ℝ))
    (S : Finset (RegularTreeVertex (m + 2))) : ProbabilityMeasure (S → ℝ) :=
  (P (finiteTreeDepth S)).map
    (continuous_treeFiniteRestriction m S (finiteTreeDepth S) le_rfl).measurable.aemeasurable

theorem finiteMarginalOfBallFamily_eq_of_le (m : ℕ)
    (P : ∀ n, ProbabilityMeasure (VertexBallVertex (m + 2) n → ℝ))
    (hP : ∀ n, Measure.map (fun x : VertexBallVertex (m + 2) (n + 1) → ℝ =>
      fun v => x (vertexBallInclusion m n v)) (P (n + 1) : Measure _) = (P n : Measure _))
    (S : Finset (RegularTreeVertex (m + 2))) (n : ℕ) (hn : finiteTreeDepth S ≤ n) :
    Measure.map (treeFiniteRestriction m S n hn) (P n : Measure _) =
      (finiteMarginalOfBallFamily m P S : Measure _) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      have hstep := treeFiniteRestriction_succ m S n hn
      have hcont : Measurable (fun x : VertexBallVertex (m + 2) (n + 1) → ℝ =>
          fun v => x (vertexBallInclusion m n v)) := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
      rw [show treeFiniteRestriction m S (n + 1) _ = treeFiniteRestriction m S n hn ∘
          (fun x : VertexBallVertex (m + 2) (n + 1) → ℝ => fun v => x (vertexBallInclusion m n v))
          from funext hstep,
        ← Measure.map_map (continuous_treeFiniteRestriction m S n hn).measurable hcont, hP n]
      exact ih

theorem finiteMarginalOfBallFamily_consistent (m : ℕ)
    (P : ∀ n, ProbabilityMeasure (VertexBallVertex (m + 2) n → ℝ))
    (hP : ∀ n, Measure.map (fun x : VertexBallVertex (m + 2) (n + 1) → ℝ =>
      fun v => x (vertexBallInclusion m n v)) (P (n + 1) : Measure _) = (P n : Measure _))
    (S T : Finset (RegularTreeVertex (m + 2))) (hST : S ⊆ T) :
    Measure.map (finiteSubrestriction (A := ℝ) hST) (finiteMarginalOfBallFamily m P T : Measure _) =
      (finiteMarginalOfBallFamily m P S : Measure _) := by
  have hdepth : finiteTreeDepth S ≤ finiteTreeDepth T :=
    Nat.sub_le_sub_right (Finset.sup_mono hST) 1
  change Measure.map (finiteSubrestriction (A := ℝ) hST)
    (Measure.map (treeFiniteRestriction m T (finiteTreeDepth T) le_rfl) (P (finiteTreeDepth T) : Measure _)) = _
  have hsub : Measurable (finiteSubrestriction (A := ℝ) hST) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  rw [Measure.map_map hsub (continuous_treeFiniteRestriction m T _ le_rfl).measurable]
  have he : finiteSubrestriction (A := ℝ) hST ∘ treeFiniteRestriction m T (finiteTreeDepth T) le_rfl =
      treeFiniteRestriction m S (finiteTreeDepth T) hdepth := by
    funext x v
    rfl
  rw [he]
  exact finiteMarginalOfBallFamily_eq_of_le m P hP S (finiteTreeDepth T) hdepth

theorem exists_tree_processLaw_of_ball_marginals (m : ℕ)
    (P : ∀ n, ProbabilityMeasure (VertexBallVertex (m + 2) n → ℝ))
    (hP : ∀ n, Measure.map (fun x : VertexBallVertex (m + 2) (n + 1) → ℝ =>
      fun v => x (vertexBallInclusion m n v)) (P (n + 1) : Measure _) = (P n : Measure _)) :
    ∃ Q : ProbabilityMeasure (RegularTreeVertex (m + 2) → ℝ), ∀ n,
      Measure.map (fun x : RegularTreeVertex (m + 2) → ℝ =>
        fun v => x (vertexBallEmbedding (m + 2) n v)) (Q : Measure _) = (P n : Measure _) := by
  obtain ⟨Q, hQ⟩ := exists_real_processLaw_of_finite_marginals
    (finiteMarginalOfBallFamily m P) (finiteMarginalOfBallFamily_consistent m P hP)
  refine ⟨Q, ?_⟩
  intro n
  let S : Finset (RegularTreeVertex (m + 2)) := Finset.univ.image (vertexBallEmbedding (m + 2) n)
  have hS (v) (hv : v ∈ S) : v ∈ Set.range (vertexBallEmbedding (m + 2) n) := by
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hv
    exact ⟨w, hw⟩
  have hdepth := finiteTreeDepth_le_of_embedding (m + 2) n S hS
  let e : VertexBallVertex (m + 2) n → S := fun v =>
    ⟨vertexBallEmbedding (m + 2) n v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩
  let back := fun x : S → ℝ => fun v => x (e v)
  have hback : Measurable back := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have he : (fun x : RegularTreeVertex (m + 2) → ℝ =>
      fun v => x (vertexBallEmbedding (m + 2) n v)) = back ∘ finiteRestriction (A := ℝ) S := rfl
  rw [he, ← Measure.map_map hback (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)), hQ S]
  rw [← finiteMarginalOfBallFamily_eq_of_le m P hP S n hdepth,
    Measure.map_map hback (continuous_treeFiniteRestriction m S n hdepth).measurable]
  have hcomp : back ∘ treeFiniteRestriction m S n hdepth = id := by
    funext x v
    apply congrArg x
    apply vertexBallEmbedding_injective (m + 2) n
    exact treeBallIndexOfDepth_spec _ _ _ _
  rw [hcomp, Measure.map_id]

end GaussianWave.BS
