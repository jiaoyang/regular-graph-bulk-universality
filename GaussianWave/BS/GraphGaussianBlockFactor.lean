import GaussianWave.BS.GaussianBlockFactor
import GaussianWave.BS.InfiniteCoverPathLifting

/-! The tree Gaussian block rule is an actual adjacency-polynomial rule on
every finite regular graph. Locally bijective covers intertwine this rule
pointwise. The label field is the literal independent Gaussian field. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

section Intertwining
variable {V W : Type*} {H : SimpleGraph V} {G : SimpleGraph W}
  [H.LocallyFinite] [G.LocallyFinite]

/-- A graph cover induces a bijection on each actual neighbor set. -/
def IsLocallyBijective (F : H →g G) : Prop :=
  ∀ v, Function.Bijective (fun z : H.neighborSet v =>
    (⟨F z.val,F.map_rel z.property⟩ : G.neighborSet (F v)))

/-- Pushing coefficient rows through a cover commutes with adjacency. -/
theorem mapDomain_finiteAdjacency (F : H →g G) (hF : IsLocallyBijective F)
    (a : V →₀ ℝ) :
    Finsupp.mapDomain F (finiteAdjacency H a) =
      finiteAdjacency G (Finsupp.mapDomain F a) := by
  let T := Finsupp.lmapDomain ℝ ℝ F
  change T (finiteAdjacency H a)=finiteAdjacency G (T a)
  refine Finsupp.induction_linear a ?_ ?_ ?_
  · simp
  · intro a b ha hb
    simp only [map_add,ha,hb]
  · intro v c
    have hrow : T (finiteAdjacency H (Finsupp.single v 1)) =
        finiteAdjacency G (Finsupp.single (F v) 1) := by
      rw [finiteAdjacency_single_sum,finiteAdjacency_single_sum,map_sum]
      simp only [T,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
      exact (Equiv.ofBijective _ (hF v)).sum_comp
        (fun z : G.neighborSet (F v) => Finsupp.single z.val (1 : ℝ))
    have he : Finsupp.single v c=c • Finsupp.single v (1 : ℝ) := by simp
    rw [he,map_smul,map_smul,hrow,map_smul]
    simp only [T,Finsupp.lmapDomain_apply,Finsupp.mapDomain_smul,Finsupp.mapDomain_single,map_smul]

/-- Every evaluated sphere polynomial, not only adjacency, intertwines. -/
theorem mapDomain_radialSphereOperator (F : H →g G) (hF : IsLocallyBijective F)
    (d : ℝ) (n : ℕ) (a : V →₀ ℝ) :
    Finsupp.mapDomain F (radialSphereOperator (finiteAdjacency H) d n a) =
      radialSphereOperator (finiteAdjacency G) d n (Finsupp.mapDomain F a) := by
  let T := Finsupp.lmapDomain ℝ ℝ F
  change T (radialSphereOperator (finiteAdjacency H) d n a)=
    radialSphereOperator (finiteAdjacency G) d n (T a)
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => exact mapDomain_finiteAdjacency F hF a
  | more n hn hn1 =>
    simp only [radialSphereOperator,LinearMap.sub_apply,Module.End.mul_apply,
      LinearMap.smul_apply,map_sub,map_smul]
    rw [show T (finiteAdjacency H (radialSphereOperator (finiteAdjacency H) d (n+1) a))=
      finiteAdjacency G (T (radialSphereOperator (finiteAdjacency H) d (n+1) a)) from
      mapDomain_finiteAdjacency F hF _,hn1,hn]

/-- Every finite radial polynomial intertwines, including the wave filter. -/
theorem mapDomain_radialFilterOperator (F : H →g G) (hF : IsLocallyBijective F)
    (d : ℝ) (R : ℕ) (f : ℕ → ℝ) (a : V →₀ ℝ) :
    Finsupp.mapDomain F (radialFilterOperator (finiteAdjacency H) d R f a) =
      radialFilterOperator (finiteAdjacency G) d R f (Finsupp.mapDomain F a) := by
  change (Finsupp.lmapDomain ℝ ℝ F) (_) = _
  simp only [radialFilterOperator,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finsupp.lmapDomain_apply,mapDomain_radialSphereOperator F hF]

/-- A pushed coefficient vector samples the original vector against the
pulled-back labels. This needs no injectivity of the global cover. -/
theorem finiteSupportGaussianSample_mapDomain (F : V → W) (a : V →₀ ℝ) (ξ : W → ℝ) :
    (Finsupp.mapDomain F a).sum (fun v c => c*ξ v) = a.sum (fun v c => c*ξ (F v)) := by
  exact Finsupp.sum_mapDomain_index (by simp) (by intros; ring)
end Intertwining

/-- The same finite Gaussian-wave filter, evaluated on an arbitrary graph. -/
def graphRadialGaussianCoefficient {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (d : ℕ) (x : ℝ) (b : ℕ) (u : V) : V →₀ ℝ :=
  (Real.sqrt (radialVertexExceptional ((d : ℝ)-1) x b))⁻¹ •
    radialFilterOperator (finiteAdjacency G) d (b+1)
      (sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x)) (Finsupp.single u 1)

/-- The graph noise is a literal local Gaussian factor of independent vertex labels. -/
def graphRadialGaussianLaw {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (d : ℕ) (x : ℝ) (b : ℕ) : Measure (V → ℝ) :=
  finiteSupportGaussianLaw (graphRadialGaussianCoefficient G d x b)

instance graphRadialGaussianLaw_probability {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (d : ℕ) (x : ℝ) (b : ℕ) : IsProbabilityMeasure (graphRadialGaussianLaw G d x b) :=
  finiteSupportGaussianLaw_isProbability _

/-- On the actual infinite tree this rule is exactly the already constructed
Gaussian-wave block factor, including its exact normalization. -/
theorem graphRadialGaussianCoefficient_tree (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (b : ℕ)
    (u : RegularTreeVertex d) :
    graphRadialGaussianCoefficient (regularWordTree d) d x b u =
      radialGaussianBlockCoefficient d x b u := by
  unfold graphRadialGaussianCoefficient radialGaussianBlockCoefficient
  congr 1
  ext v
  rw [radialFilterOperator_single_apply (regularWordTree_isTree d) d
    (regularWordTree_regular d hd),regularTreeRadialFinsupp_apply]

/-- The actual finite-seed extension is a locally bijective cover. -/
theorem infiniteVertexGraphHom_isLocallyBijective {N m : ℕ}
    (G : RegularGraph N (m+2)) (k : ℕ) (seed : VertexCoverSeed N m k) :
    IsLocallyBijective (infiniteVertexGraphHom G k seed) := by
  intro v
  constructor
  · intro a b hab
    apply Subtype.ext
    exact infiniteVertexGraphCover_local_injective G k seed v a.property b.property
      (congrArg Subtype.val hab)
  · intro y
    obtain ⟨w,hw,he⟩ := infiniteVertexGraphCover_neighbor_surjective G k seed v y.val y.property
    exact ⟨⟨w,hw⟩,Subtype.ext he⟩

/-- Exact coefficient intertwining for the actual graph-cover sampler. -/
theorem graphRadialGaussianCoefficient_cover {N m : ℕ}
    (G : RegularGraph N (m+2)) (k : ℕ) (seed : VertexCoverSeed N m k)
    (x : ℝ) (b : ℕ) (u : RegularTreeVertex (m+2)) :
    Finsupp.mapDomain (infiniteVertexGraphCover G k seed)
      (radialGaussianBlockCoefficient (m+2) x b u) =
      graphRadialGaussianCoefficient G.val (m+2) x b (infiniteVertexGraphCover G k seed u) := by
  rw [← graphRadialGaussianCoefficient_tree (m+2) (by omega)]
  unfold graphRadialGaussianCoefficient
  rw [Finsupp.mapDomain_smul]
  congr 1
  have h := mapDomain_radialFilterOperator (infiniteVertexGraphHom G k seed)
    (infiniteVertexGraphHom_isLocallyBijective G k seed) ((m+2 : ℕ) : ℝ) (b+1)
    (sphericalCovariance (m+2) (2*Real.sqrt (((m+2 : ℕ) : ℝ)-1)*x)) (Finsupp.single u 1)
  simpa only [infiniteVertexGraphHom,Finsupp.mapDomain_single] using h

/-- Pointwise rule compatibility holds even when the finite graph has cycles.
Injectivity is only needed later to identify the pulled-back noise law. -/
theorem graphRadialGaussianSample_cover {N m : ℕ}
    (G : RegularGraph N (m+2)) (k : ℕ) (seed : VertexCoverSeed N m k)
    (x : ℝ) (b : ℕ) (ξ : Fin N → ℝ) (u : RegularTreeVertex (m+2)) :
    finiteSupportGaussianSample (graphRadialGaussianCoefficient G.val (m+2) x b) ξ
      (infiniteVertexGraphCover G k seed u) =
    finiteSupportGaussianSample (radialGaussianBlockCoefficient (m+2) x b)
      (ξ ∘ infiniteVertexGraphCover G k seed) u := by
  unfold finiteSupportGaussianSample
  rw [← graphRadialGaussianCoefficient_cover G k seed]
  exact finiteSupportGaussianSample_mapDomain _ _ _

end GaussianWave.BS
