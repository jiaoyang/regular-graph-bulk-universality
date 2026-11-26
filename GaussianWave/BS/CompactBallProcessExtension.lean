import GaussianWave.BS.BallProcessExtension

/-! Compact-valued version of the proved cofinal ball extension. The
coordinate proof is the same as BallProcessExtension; its last step uses
the independently proved compact-state extension theorem. -/
noncomputable section
open MeasureTheory Set
open scoped Topology Classical
namespace GaussianWave.BS
variable {A : Type*} [MetricSpace A] [CompactSpace A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A] [Inhabited A]

def compactTreeFiniteRestriction (m : ℕ) (S : Finset (RegularTreeVertex (m + 2)))
    (n : ℕ) (h : finiteTreeDepth S ≤ n) (x : VertexBallVertex (m + 2) n → A) : S → A :=
  fun v => x (treeBallIndexOfDepth (m + 2) n v.val
    ((depth_le_finiteTreeDepth S v).trans (Nat.add_le_add_right h 1)))

theorem continuous_compactTreeFiniteRestriction (m : ℕ) (S : Finset (RegularTreeVertex (m + 2)))
    (n : ℕ) (h : finiteTreeDepth S ≤ n) : Continuous (compactTreeFiniteRestriction (A := A) m S n h) :=
  continuous_pi (fun _ => continuous_apply _)

theorem compactTreeFiniteRestriction_succ (m : ℕ) (S : Finset (RegularTreeVertex (m + 2)))
    (n : ℕ) (hn : finiteTreeDepth S ≤ n) (x : VertexBallVertex (m + 2) (n + 1) → A) :
    compactTreeFiniteRestriction (A := A) m S (n + 1) (hn.trans (Nat.le_succ n)) x =
      compactTreeFiniteRestriction (A := A) m S n hn (fun v => x (vertexBallInclusion m n v)) := by
  funext v
  apply congrArg x
  apply vertexBallEmbedding_injective (m + 2) (n + 1)
  rw [treeBallIndexOfDepth_spec, vertexBallEmbedding_inclusion, treeBallIndexOfDepth_spec]

def compactFiniteMarginalOfBallFamily (m : ℕ)
    (P : ∀ n, ProbabilityMeasure (VertexBallVertex (m + 2) n → A))
    (S : Finset (RegularTreeVertex (m + 2))) : ProbabilityMeasure (S → A) :=
  (P (finiteTreeDepth S)).map
    (continuous_compactTreeFiniteRestriction (A := A) m S (finiteTreeDepth S) le_rfl).measurable.aemeasurable

theorem compactFiniteMarginalOfBallFamily_eq_of_le (m : ℕ)
    (P : ∀ n, ProbabilityMeasure (VertexBallVertex (m + 2) n → A))
    (hP : ∀ n, Measure.map (fun x : VertexBallVertex (m + 2) (n + 1) → A =>
      fun v => x (vertexBallInclusion m n v)) (P (n + 1) : Measure _) = (P n : Measure _))
    (S : Finset (RegularTreeVertex (m + 2))) (n : ℕ) (hn : finiteTreeDepth S ≤ n) :
    Measure.map (compactTreeFiniteRestriction (A := A) m S n hn) (P n : Measure _) =
      (compactFiniteMarginalOfBallFamily m P S : Measure _) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      have hstep := compactTreeFiniteRestriction_succ (A := A) m S n hn
      have hcont : Measurable (fun x : VertexBallVertex (m + 2) (n + 1) → A =>
          fun v => x (vertexBallInclusion m n v)) := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
      rw [show compactTreeFiniteRestriction (A := A) m S (n + 1) _ = compactTreeFiniteRestriction (A := A) m S n hn ∘
          (fun x : VertexBallVertex (m + 2) (n + 1) → A => fun v => x (vertexBallInclusion m n v))
          from funext hstep,
        ← Measure.map_map (continuous_compactTreeFiniteRestriction (A := A) m S n hn).measurable hcont, hP n]
      exact ih

theorem compactFiniteMarginalOfBallFamily_consistent (m : ℕ)
    (P : ∀ n, ProbabilityMeasure (VertexBallVertex (m + 2) n → A))
    (hP : ∀ n, Measure.map (fun x : VertexBallVertex (m + 2) (n + 1) → A =>
      fun v => x (vertexBallInclusion m n v)) (P (n + 1) : Measure _) = (P n : Measure _))
    (S T : Finset (RegularTreeVertex (m + 2))) (hST : S ⊆ T) :
    Measure.map (finiteSubrestriction (A := A) hST) (compactFiniteMarginalOfBallFamily m P T : Measure _) =
      (compactFiniteMarginalOfBallFamily m P S : Measure _) := by
  have hdepth : finiteTreeDepth S ≤ finiteTreeDepth T :=
    Nat.sub_le_sub_right (Finset.sup_mono hST) 1
  change Measure.map (finiteSubrestriction (A := A) hST)
    (Measure.map (compactTreeFiniteRestriction (A := A) m T (finiteTreeDepth T) le_rfl) (P (finiteTreeDepth T) : Measure _)) = _
  have hsub : Measurable (finiteSubrestriction (A := A) hST) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  rw [Measure.map_map hsub (continuous_compactTreeFiniteRestriction (A := A) m T _ le_rfl).measurable]
  have he : finiteSubrestriction (A := A) hST ∘ compactTreeFiniteRestriction (A := A) m T (finiteTreeDepth T) le_rfl =
      compactTreeFiniteRestriction (A := A) m S (finiteTreeDepth T) hdepth := by
    funext x v
    rfl
  rw [he]
  exact compactFiniteMarginalOfBallFamily_eq_of_le m P hP S (finiteTreeDepth T) hdepth

theorem exists_compact_tree_processLaw_of_ball_marginals (m : ℕ)
    (P : ∀ n, ProbabilityMeasure (VertexBallVertex (m + 2) n → A))
    (hP : ∀ n, Measure.map (fun x : VertexBallVertex (m + 2) (n + 1) → A =>
      fun v => x (vertexBallInclusion m n v)) (P (n + 1) : Measure _) = (P n : Measure _)) :
    ∃ Q : ProbabilityMeasure (RegularTreeVertex (m + 2) → A), ∀ n,
      Measure.map (fun x : RegularTreeVertex (m + 2) → A =>
        fun v => x (vertexBallEmbedding (m + 2) n v)) (Q : Measure _) = (P n : Measure _) := by
  obtain ⟨Q, hQ⟩ := exists_processLaw_of_compact_finite_marginals
    (compactFiniteMarginalOfBallFamily m P) (compactFiniteMarginalOfBallFamily_consistent m P hP)
  refine ⟨Q, ?_⟩
  intro n
  let S : Finset (RegularTreeVertex (m + 2)) := Finset.univ.image (vertexBallEmbedding (m + 2) n)
  have hS (v) (hv : v ∈ S) : v ∈ Set.range (vertexBallEmbedding (m + 2) n) := by
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hv
    exact ⟨w, hw⟩
  have hdepth := finiteTreeDepth_le_of_embedding (m + 2) n S hS
  let e : VertexBallVertex (m + 2) n → S := fun v =>
    ⟨vertexBallEmbedding (m + 2) n v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩
  let back := fun x : S → A => fun v => x (e v)
  have hback : Measurable back := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have he : (fun x : RegularTreeVertex (m + 2) → A =>
      fun v => x (vertexBallEmbedding (m + 2) n v)) = back ∘ finiteRestriction (A := A) S := rfl
  rw [he, ← Measure.map_map hback (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)), hQ S]
  rw [← compactFiniteMarginalOfBallFamily_eq_of_le m P hP S n hdepth,
    Measure.map_map hback (continuous_compactTreeFiniteRestriction (A := A) m S n hdepth).measurable]
  have hcomp : back ∘ compactTreeFiniteRestriction (A := A) m S n hdepth = id := by
    funext x v
    apply congrArg x
    apply vertexBallEmbedding_injective (m + 2) n
    exact treeBallIndexOfDepth_spec _ _ _ _
  rw [hcomp, Measure.map_id]

end GaussianWave.BS
