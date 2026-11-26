import GaussianWave.BS.JointGraphGaussianConcentration
import GaussianWave.BS.GraphGaussianLocality
import GaussianWave.BS.JointGraphGaussianBlockFactor
import GaussianWave.BS.GraphGaussianWindowMean
import GaussianWave.BS.LiftedCoverFiniteWindows

/-! Finite-cover tests of actual Gaussian-perturbed graph marks are bounded
local functions of actual iid labels. Their variance estimate is derived. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph Lower

def VertexCoverFiber (m L : ℕ) :=
  Equiv.Perm (Fin (m+2)) × (Fin (m+2) → BranchCoverOrdering (m+1) L)

instance (m L : ℕ) : Fintype (VertexCoverFiber m L) := by unfold VertexCoverFiber; infer_instance
instance (m L : ℕ) : Inhabited (VertexCoverFiber m L) := by unfold VertexCoverFiber; infer_instance

/-- The actual deterministic graph marks after drawing the Gaussian labels. -/
def graphGaussianPerturbedMark {N m : ℕ} (G : RegularGraph N (m+2)) (r : ℕ)
    (x : ℝ) (b : ℕ) (f : Fin r → Fin N → ℝ) (η : ℝ)
    (ξ : (Fin r × Fin N) → ℝ) (a : Fin r) (v : Fin N) : ℝ :=
  f a v+η*finiteSupportGaussianSample (jointGraphGaussianCoefficient G r x b) ξ (a,v)

/-- Average over the actual local neighbor-order choices at a fixed root. -/
def graphGaussianRootTest {N m : ℕ} (G : RegularGraph N (m+2)) (r L : ℕ)
    (x : ℝ) (b : ℕ) (f : Fin r → Fin N → ℝ) (η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ)
    (v : Fin N) (ξ : (Fin r × Fin N) → ℝ) : ℝ :=
  (Fintype.card (VertexCoverFiber m L) : ℝ)⁻¹*
    ∑ θ : VertexCoverFiber m L,F (fun aj : Fin r × J =>
      graphGaussianPerturbedMark G r x b f η ξ aj.1
        (infiniteVertexGraphCover G L (v,θ) (site aj.2)))

/-- A graph cover does not increase the root depth of a site. -/
theorem infiniteVertexGraphCover_root_edist {N m : ℕ} (G : RegularGraph N (m+2))
    (L : ℕ) (seed : VertexCoverSeed N m L) (u : RegularTreeVertex (m+2)) :
    G.val.edist seed.1 (infiniteVertexGraphCover G L seed u) ≤ (regularTreeDepth u : ℕ∞) := by
  have h := (((regularTreeParentWalk (m+2) u).reverse).map
    (infiniteVertexGraphHom G L seed)).edist_le
  simpa only [SimpleGraph.Walk.length_map,SimpleGraph.Walk.length_reverse,
    regularTreeParentWalk_length,infiniteVertexGraphHom,infiniteVertexGraphCover] using h

theorem measurable_graphGaussianRootTest {N m : ℕ} (G : RegularGraph N (m+2))
    (r L : ℕ) (x : ℝ) (b : ℕ) (f : Fin r → Fin N → ℝ) (η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ) (v : Fin N) :
    Measurable (graphGaussianRootTest G r L x b f η site F v) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro θ hθ
  apply F.continuous.measurable.comp
  apply measurable_pi_lambda
  intro aj
  exact measurable_const.add (((measurable_pi_apply
    (aj.1,infiniteVertexGraphCover G L (v,θ) (site aj.2))).comp
      (measurable_finiteSupportGaussianSample (jointGraphGaussianCoefficient G r x b))).const_mul η)

/-- Every root observation uses labels in the explicitly enlarged graph
ball. This locality is proved from the polynomial rule and actual cover. -/
theorem graphGaussianRootTest_local {N m : ℕ} (G : RegularGraph N (m+2))
    (r L k : ℕ) (x : ℝ) (b : ℕ) (f : Fin r → Fin N → ℝ) (η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ k+1)
    (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ)
    (v : Fin N) (ξ ζ : (Fin r × Fin N) → ℝ)
    (he : ∀ a w,G.val.edist v w ≤ (k+b+2 : ℕ) → ξ (a,w)=ζ (a,w)) :
    graphGaussianRootTest G r L x b f η site F v ξ =
      graphGaussianRootTest G r L x b f η site F v ζ := by
  unfold graphGaussianRootTest
  congr 1
  apply Finset.sum_congr rfl
  intro θ hθ
  congr 1
  funext aj
  unfold graphGaussianPerturbedMark
  congr 1
  congr 1
  rw [jointGraphGaussianSample_channel,jointGraphGaussianSample_channel]
  apply graphRadialGaussianSample_local
  intro w hw
  apply he aj.1 w
  calc
    _ ≤ G.val.edist v (infiniteVertexGraphCover G L (v,θ) (site aj.2))+
        G.val.edist (infiniteVertexGraphCover G L (v,θ) (site aj.2)) w := SimpleGraph.edist_triangle
    _ ≤ ((k+1 : ℕ) : ℕ∞)+((b+1 : ℕ) : ℕ∞) :=
      add_le_add ((infiniteVertexGraphCover_root_edist G L (v,θ) (site aj.2)).trans
        (by exact_mod_cast hsite aj.2)) hw
    _ = _ := by norm_cast; omega

/-- The actual root observations lie in [0,1] whenever the test does. -/
theorem graphGaussianRootTest_bounds {N m : ℕ} (G : RegularGraph N (m+2))
    (r L : ℕ) (x : ℝ) (b : ℕ) (f : Fin r → Fin N → ℝ) (η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ)
    (hF0 : ∀ z,0 ≤ F z) (hF1 : ∀ z,F z ≤ 1) (v : Fin N) (ξ : (Fin r × Fin N) → ℝ) :
    0 ≤ graphGaussianRootTest G r L x b f η site F v ξ ∧
      graphGaussianRootTest G r L x b f η site F v ξ ≤ 1 := by
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => hF0 _))
  · have hc : (Fintype.card (VertexCoverFiber m L) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    change _*∑ θ : VertexCoverFiber m L,F _ ≤ 1
    have hs := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (s := Finset.univ) (fun θ _ => hF1
        (fun aj : Fin r × J => graphGaussianPerturbedMark G r x b f η ξ aj.1
          (infiniteVertexGraphCover G L (v,θ) (site aj.2)))))
      (show 0 ≤ (Fintype.card (VertexCoverFiber m L) : ℝ)⁻¹ by positivity)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hs
    change _ ≤ (Fintype.card (VertexCoverFiber m L) : ℝ)⁻¹*
      (Fintype.card (VertexCoverFiber m L) : ℝ) at hs
    exact hs.trans_eq (inv_mul_cancel₀ hc)

/-- Actual local Gaussian perturbations satisfy the needed finite-window
variance bound; locality and independence are both discharged here. -/
theorem graphGaussianRootTest_average_variance {N m : ℕ} (G : RegularGraph N (m+2))
    (hN : 0 < N) (r L k : ℕ) (x : ℝ) (b : ℕ) (f : Fin r → Fin N → ℝ) (η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ k+1)
    (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ)
    (hF0 : ∀ z,0 ≤ F z) (hF1 : ∀ z,F z ≤ 1) :
    (∫ ξ,((N : ℝ)⁻¹*∑ v,graphGaussianRootTest G r L x b f η site F v ξ-
      ∫ ζ,(N : ℝ)⁻¹*∑ v,graphGaussianRootTest G r L x b f η site F v ζ
        ∂gaussianLabelLaw (Fin r × Fin N))^2 ∂gaussianLabelLaw (Fin r × Fin N)) ≤
      (regularBallBound (m+2) (2*(k+b+2)) : ℝ)/(N : ℝ) := by
  exact jointGraphGaussianAverage_variance_of_local G hN r (k+b+2)
    (graphGaussianRootTest G r L x b f η site F)
    (measurable_graphGaussianRootTest G r L x b f η site F)
    (fun v ξ => (graphGaussianRootTest_bounds G r L x b f η site F hF0 hF1 v ξ).1)
    (fun v ξ => (graphGaussianRootTest_bounds G r L x b f η site F hF0 hF1 v ξ).2)
    (fun v ξ ζ he => graphGaussianRootTest_local G r L k x b f η site hsite F v ξ ζ he)

/-- The actual cover-law observation of the perturbed graph marks is the
empirical average of the explicitly local root tests. -/
theorem integral_uniformLifted_perturbed_window {N m : ℕ} (G : RegularGraph N (m+2))
    (hN : 0 < N) (r L : ℕ) (x : ℝ) (b : ℕ) (f : Fin r → Fin N → ℝ) (η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ L+1)
    (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ)
    (ξ : (Fin r × Fin N) → ℝ) :
    (∫ z,F (fun aj : Fin r × J => z (aj.1,site aj.2))
      ∂uniformLiftedTreeLaw G hN (graphGaussianPerturbedMark G r x b f η ξ)) =
      (N : ℝ)⁻¹*∑ v,graphGaussianRootTest G r L x b f η site F v ξ := by
  let W := fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
    fun aj : Fin r × J => z (aj.1,site aj.2)
  have hW : Measurable W := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  rw [← integral_map hW.aemeasurable F.continuous.aestronglyMeasurable,
    uniformLiftedTreeLaw_window_atomic G hN _ L site hsite,
    integral_uniformAtomicLaw_boundedTest]
  simp only [graphGaussianRootTest,VertexCoverSeed,VertexCoverFiber,
    Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp only [mul_inv_rev]
  ring

end GaussianWave.BS
