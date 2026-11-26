import GaussianWave.BS.ProcessEigenrelations
import GaussianWave.BS.TreeBallEmbedding
import GaussianWave.BS.EdgeBallEmbedding
import GaussianWave.BS.EdgeCoverGeometry

/-! Actual global tree eigen-equations restrict to the literal recursive
finite-ball equations and therefore to the proved intrinsic eigensolution
subspaces. This is the finite-window support bridge for process limits. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

theorem regularTree_sum_neighbor_root (d : ℕ) (f : RegularTreeVertex d → ℝ) :
    (∑ z : (regularWordTree d).neighborSet none, f z.val)=∑ j : Fin d, f (some (j,[])) :=
  (Equiv.sum_comp (regularTreeNeighborEquiv d none) (fun z => f z.val)).symm

theorem regularTree_sum_neighbor_some (m : ℕ) (a : Fin (m+2)) (w : List (Fin (m+1)))
    (f : RegularTreeVertex (m+2) → ℝ) :
    (∑ z : (regularWordTree (m+2)).neighborSet (some (a,w)), f z.val)=
      f (regularTreeParent (some (a,w)))+∑ j : Fin (m+1), f (some (a,j::w)) := by
  rw [← Equiv.sum_comp (regularTreeNeighborEquiv (m+2) (some (a,w))) (fun z => f z.val)]
  change (∑ j : Option (Fin (m+1)), f (regularTreeNeighbor (some (a,w)) j))=_
  rw [Fintype.sum_option]
  rfl

/-- Every branch restriction satisfies every literal interior equation;
its parent is the actual tree parent just outside the branch. -/
theorem branchEigenrelation_of_tree_equations (m : ℕ) (energy : ℝ)
    (f : RegularTreeVertex (m+2) → ℝ)
    (hf : ∀ u, (∑ z : (regularWordTree (m+2)).neighborSet u, f z.val)=energy*f u)
    (k : ℕ) (a : Fin (m+2)) (stem : List (Fin (m+1))) :
    BranchEigenrelation m k energy (f (regularTreeParent (some (a,stem.reverse))))
      (fun v => f (some (a,(stem++branchPath (m+1) k v).reverse))) := by
  induction k generalizing stem with
  | zero => trivial
  | succ k ih =>
    constructor
    · have h := hf (some (a,stem.reverse))
      rw [regularTree_sum_neighbor_some] at h
      change (∑ j : Fin (m+1), f (some (a,(stem++(j::branchPath (m+1) k (branchRoot (m+1) k))).reverse)))=
        energy*f (some (a,(stem++[]).reverse))-f (regularTreeParent (some (a,stem.reverse)))
      have hr : branchPath (m+1) k (branchRoot (m+1) k)=[] := by cases k <;> rfl
      simp only [hr,List.reverse_append,List.reverse_cons,List.reverse_nil,
        List.nil_append,List.append_nil,List.singleton_append]
      linarith
    · intro j
      have h := ih (stem++[j])
      have hparent : regularTreeParent (some (a,(stem++[j]).reverse))=some (a,stem.reverse) := by
        simp [List.reverse_append,regularTreeParent]
      rw [hparent] at h
      simpa only [branchPath,List.append_nil,List.append_assoc,List.singleton_append] using h

/-- The full C-ball restriction has its actual recursive eigensolution
relations, at every radius. -/
theorem vertexBallEigenrelation_of_tree_equations (m k : ℕ) (energy : ℝ)
    (f : RegularTreeVertex (m+2) → ℝ)
    (hf : ∀ u, (∑ z : (regularWordTree (m+2)).neighborSet u, f z.val)=energy*f u) :
    VertexBallEigenrelation m k energy (fun v => f (vertexBallEmbedding (m+2) k v)) := by
  constructor
  · have h := hf none
    rw [regularTree_sum_neighbor_root] at h
    change (∑ a : Fin (m+2), f (some (a,(branchPath (m+1) k (branchRoot (m+1) k)).reverse)))=energy*f none
    have hr : branchPath (m+1) k (branchRoot (m+1) k)=[] := by cases k <;> rfl
    simpa only [hr,List.reverse_nil] using h
  · intro a
    have h := branchEigenrelation_of_tree_equations m energy f hf k a []
    simpa only [List.reverse_nil,regularTreeParent,List.nil_append,vertexBallEmbedding,vertexBallRoot] using h

/-- Actual joint process tree eigenrelations yield actual finite-ball
support, including all channel dependence. -/
theorem vertexBallEigenrelation_of_treeResidual_zero (m k r : ℕ) (energy : Fin r → ℝ)
    (x : (Fin r × RegularTreeVertex (m+2)) → ℝ)
    (hx : ∀ a u, treeEigenResidual (m+2) r energy a u x=0) (a : Fin r) :
    VertexBallEigenrelation m k (energy a)
      (fun v => x (a,vertexBallEmbedding (m+2) k v)) := by
  apply vertexBallEigenrelation_of_tree_equations m k (energy a) (fun u => x (a,u))
  intro u
  exact sub_eq_zero.mp (hx a u)

/-- The finite-window eigenrelation support set is genuinely measurable,
using the actual finite-dimensional submodule and its literal equivalence. -/
theorem measurableSet_joint_vertexBallEigenSpace (m k r : ℕ) (energy : Fin r → ℝ) :
    MeasurableSet {x : (Fin r × VertexBallVertex (m+2) k) → ℝ |
      ∀ a, (fun v => x (a,v))∈vertexBallEigenSpace m k (energy a)} := by
  have h (a : Fin r) : MeasurableSet {x : (Fin r × VertexBallVertex (m+2) k) → ℝ |
      (fun v => x (a,v))∈vertexBallEigenSpace m k (energy a)} := by
    exact (Submodule.closed_of_finiteDimensional (vertexBallEigenSpace m k (energy a))).measurableSet.preimage
      (measurable_pi_lambda _ (fun v => measurable_pi_apply (a,v)))
  simpa only [Set.setOf_forall] using MeasurableSet.iInter h

/-- Every actual finite marginal of an eigenprocess is supported on the
proved intrinsic eigensolution subspace. No support contract is assumed. -/
theorem map_vertexBall_ae_eigenSpace (m k r : ℕ) (energy : Fin r → ℝ)
    (henergy : ∀ a, energy a ≠ (m+2 : ℝ))
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hμ : ∀ᵐ x ∂μ, ∀ a u, treeEigenResidual (m+2) r energy a u x=0) :
    ∀ᵐ y ∂Measure.map (fun x : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
      fun av : Fin r × VertexBallVertex (m+2) k => x (av.1,vertexBallEmbedding (m+2) k av.2)) μ,
      ∀ a, (fun v => y (a,v))∈vertexBallEigenSpace m k (energy a) := by
  apply (ae_map_iff (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).aemeasurable
    (measurableSet_joint_vertexBallEigenSpace m k r energy)).2
  filter_upwards [hμ] with x hx
  intro a
  apply (mem_vertexBallEigenSpace_iff m k (energy a) (henergy a) _).2
  exact vertexBallEigenrelation_of_treeResidual_zero m k r energy x hx a


private theorem edgeToVertexBall_eq_edgeInVertexCover (m k : ℕ) :
    edgeToVertexBall m (k+1)=edgeInVertexCover m k 0 := by
  funext v
  rcases v with ⟨b,v⟩
  cases b with
  | true => rfl
  | false =>
    cases v with
    | inl u => rfl
    | inr av => simp [edgeToVertexBall,edgeInVertexCover,Fin.succAbove_zero]

/-- The literal E-ball restriction also satisfies all its recursive
interior equations, obtained from the proved actual C-ball restriction. -/
theorem edgeBallEigenrelation_of_tree_equations (m k : ℕ) (energy : ℝ)
    (f : RegularTreeVertex (m+2) → ℝ)
    (hf : ∀ u, (∑ z : (regularWordTree (m+2)).neighborSet u, f z.val)=energy*f u) :
    EdgeBallEigenrelation m k energy (fun v => f (edgeBallEmbedding m k v)) := by
  cases k with
  | zero => intro b; trivial
  | succ k =>
    have hC := vertexBallEigenrelation_of_tree_equations m (k+1) energy f hf
    have hE := edgeInVertexCover_eigenrelation m k energy _ hC 0
    rw [← edgeToVertexBall_eq_edgeInVertexCover] at hE
    simpa only [edgeToVertexBall_embedding] using hE

theorem edgeBallEigenrelation_of_treeResidual_zero (m k r : ℕ) (energy : Fin r → ℝ)
    (x : (Fin r × RegularTreeVertex (m+2)) → ℝ)
    (hx : ∀ a u, treeEigenResidual (m+2) r energy a u x=0) (a : Fin r) :
    EdgeBallEigenrelation m k (energy a)
      (fun v => x (a,edgeBallEmbedding m k v)) := by
  apply edgeBallEigenrelation_of_tree_equations m k (energy a) (fun u => x (a,u))
  intro u
  exact sub_eq_zero.mp (hx a u)

theorem measurableSet_joint_edgeBallEigenSpace (m k r : ℕ) (energy : Fin r → ℝ) :
    MeasurableSet {x : (Fin r × EdgeBallVertex (m+2) k) → ℝ |
      ∀ a, (fun v => x (a,v))∈edgeBallEigenSpace m k (energy a)} := by
  have h (a : Fin r) : MeasurableSet {x : (Fin r × EdgeBallVertex (m+2) k) → ℝ |
      (fun v => x (a,v))∈edgeBallEigenSpace m k (energy a)} := by
    exact (Submodule.closed_of_finiteDimensional (edgeBallEigenSpace m k (energy a))).measurableSet.preimage
      (measurable_pi_lambda _ (fun v => measurable_pi_apply (a,v)))
  simpa only [Set.setOf_forall] using MeasurableSet.iInter h

/-- Every actual finite E-marginal is supported on the proved intrinsic
edge eigensolution subspace. This does not exclude the constant energy. -/
theorem map_edgeBall_ae_eigenSpace (m k r : ℕ) (energy : Fin r → ℝ)
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hμ : ∀ᵐ x ∂μ, ∀ a u, treeEigenResidual (m+2) r energy a u x=0) :
    ∀ᵐ y ∂Measure.map (fun x : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
      fun av : Fin r × EdgeBallVertex (m+2) k => x (av.1,edgeBallEmbedding m k av.2)) μ,
      ∀ a, (fun v => y (a,v))∈edgeBallEigenSpace m k (energy a) := by
  apply (ae_map_iff (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).aemeasurable
    (measurableSet_joint_edgeBallEigenSpace m k r energy)).2
  filter_upwards [hμ] with x hx
  intro a
  apply (mem_edgeBallEigenSpace_iff m k (energy a) _).2
  exact edgeBallEigenrelation_of_treeResidual_zero m k r energy x hx a


/-- Coordinate L2 control gives genuine finite second moment for every
actual finite marginal, in any finite coordinate indexing. -/
theorem integrable_finiteWindow_sum_sq {I J : Type*} [Fintype J]
    (μ : Measure (I → ℝ)) (hi : ∀ i, Integrable (fun x => x i^2) μ) (site : J → I) :
    Integrable (fun y : J → ℝ => ∑ j, y j^2)
      (Measure.map (fun x : I → ℝ => fun j => x (site j)) μ) := by
  have hT : Measurable (fun x : I → ℝ => fun j => x (site j)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  have hf : Continuous (fun y : J → ℝ => ∑ j, y j^2) :=
    continuous_finset_sum _ (fun j hj => (continuous_apply j).pow 2)
  apply (integrable_map_measure hf.aestronglyMeasurable hT.aemeasurable).2
  exact integrable_finset_sum _ (fun j hj => hi (site j))

/-- The second moment of an actual finite marginal is the sum of its
actual coordinate moments, before or after taking a process limit. -/
theorem integral_finiteWindow_sum_sq {I J : Type*} [Fintype J]
    (μ : Measure (I → ℝ)) (hi : ∀ i, Integrable (fun x => x i^2) μ) (site : J → I) :
    (∫ y : J → ℝ, ∑ j, y j^2 ∂Measure.map (fun x : I → ℝ => fun j => x (site j)) μ)=
      ∑ j, ∫ x, x (site j)^2 ∂μ := by
  have hT : Measurable (fun x : I → ℝ => fun j => x (site j)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  have hf : Continuous (fun y : J → ℝ => ∑ j, y j^2) :=
    continuous_finset_sum _ (fun j hj => (continuous_apply j).pow 2)
  rw [integral_map hT.aemeasurable hf.aestronglyMeasurable]
  exact integral_finset_sum _ (fun j hj => hi (site j))

/-- Explicit finite-window second-moment bound derived only from the
coordinate bounds proved by weak lower semicontinuity. -/
theorem integral_finiteWindow_sum_sq_le {I J : Type*} [Fintype J]
    (μ : Measure (I → ℝ)) (hi : ∀ i, Integrable (fun x => x i^2) μ)
    (M : I → ℝ) (hM : ∀ i, (∫ x, x i^2 ∂μ)≤M i) (site : J → I) :
    (∫ y : J → ℝ, ∑ j, y j^2 ∂Measure.map (fun x : I → ℝ => fun j => x (site j)) μ)≤
      ∑ j, M (site j) := by
  rw [integral_finiteWindow_sum_sq μ hi site]
  exact Finset.sum_le_sum (fun j hj => hM (site j))

end GaussianWave.BS
