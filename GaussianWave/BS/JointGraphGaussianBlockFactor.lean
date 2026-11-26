import GaussianWave.BS.GaussianChannelSampler
import GaussianWave.BS.GraphGaussianEnergy
import GaussianWave.BS.JointGaussianBlockFactor

/-! Actual joint finite-graph Gaussian block samplers, driven by independent
channel-times-vertex labels. Window laws and energy bounds hold jointly. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph Lower

/-- Finite output restriction of an actual finitely supported sampler. -/
theorem finiteSupportGaussianLaw_window {V I J : Type*} (a : I → V →₀ ℝ) (site : J → I) :
    Measure.map (fun z : I → ℝ => fun j => z (site j)) (finiteSupportGaussianLaw a) =
      finiteSupportGaussianLaw (fun j => a (site j)) := by
  rw [finiteSupportGaussianLaw,Measure.map_map
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))
    (measurable_finiteSupportGaussianSample a)]
  rfl

def jointGraphGaussianCoefficient {N m : ℕ} (G : RegularGraph N (m+2))
    (r : ℕ) (x : ℝ) (b : ℕ) (av : Fin r × Fin N) : (Fin r × Fin N) →₀ ℝ :=
  channelFinsupp av.1 (graphRadialGaussianCoefficient G.val (m+2) x b av.2)

def jointGraphGaussianLaw {N m : ℕ} (G : RegularGraph N (m+2))
    (r : ℕ) (x : ℝ) (b : ℕ) : Measure ((Fin r × Fin N) → ℝ) :=
  finiteSupportGaussianLaw (jointGraphGaussianCoefficient G r x b)

instance jointGraphGaussianLaw_probability {N m : ℕ} (G : RegularGraph N (m+2))
    (r : ℕ) (x : ℝ) (b : ℕ) : IsProbabilityMeasure (jointGraphGaussianLaw G r x b) :=
  finiteSupportGaussianLaw_isProbability _

/-- Actual product identity for the complete graph-noise law. -/
theorem jointGraphGaussianLaw_product {N m : ℕ} (G : RegularGraph N (m+2))
    (r : ℕ) (x : ℝ) (b : ℕ) :
    jointGraphGaussianLaw G r x b =
      independentChannelLaw (fun _ : Fin r => graphRadialGaussianLaw G.val (m+2) x b) :=
  finiteSupportGaussianLaw_channels _

/-- The true good enlarged cover window has exactly the joint iid tree
blockfactor law; channel independence is obtained from the actual label field. -/
theorem jointGraphGaussianLaw_window_of_good {N m : ℕ}
    (G : RegularGraph N (m+2)) (r k b : ℕ)
    (seed : VertexCoverSeed N m (k+b+1)) (x : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ k+1)
    (hgood : GoodVertexCoverRoot G (k+b+1) seed.1) :
    Measure.map (fun z : (Fin r × Fin N) → ℝ => fun aj : Fin r × J =>
      z (aj.1,infiniteVertexGraphCover G (k+b+1) seed (site aj.2)))
      (jointGraphGaussianLaw G r x b) =
    Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
      fun aj : Fin r × J => z (aj.1,site aj.2))
      (jointRadialGaussianBlockLaw r (m+2) x b) := by
  rw [jointGraphGaussianLaw_product,jointRadialGaussianBlockLaw]
  have hleft := independentChannelLaw_window
    (fun _ : Fin r => graphRadialGaussianLaw G.val (m+2) x b)
    (fun j => infiniteVertexGraphCover G (k+b+1) seed (site j))
  rw [hleft,independentChannelLaw_window]
  change independentChannelLaw (fun _ : Fin r => Measure.map _
      (finiteSupportGaussianLaw (graphRadialGaussianCoefficient G.val (m+2) x b))) =
    independentChannelLaw (fun _ : Fin r => Measure.map _
      (finiteSupportGaussianLaw (radialGaussianBlockCoefficient (m+2) x b)))
  simp_rw [finiteSupportGaussianLaw_window]
  rw [graphRadialGaussianLaw_window_of_good G k b seed x site hsite hgood]

/-- Every channel of the actual joint graph sampler is the scalar rule on
its own independently sampled channel field. -/
theorem jointGraphGaussianSample_channel {N m : ℕ} (G : RegularGraph N (m+2))
    (r : ℕ) (x : ℝ) (b : ℕ) (ξ : (Fin r × Fin N) → ℝ) (a : Fin r) (v : Fin N) :
    finiteSupportGaussianSample (jointGraphGaussianCoefficient G r x b) ξ (a,v) =
      finiteSupportGaussianSample (graphRadialGaussianCoefficient G.val (m+2) x b)
        (fun w => ξ (a,w)) v := finiteSupportGaussianSample_channels _ ξ a v

/-- The total expected empirical root energy of r actual channels is r
times the scalar value, including on graphs with collisions. -/
theorem integral_jointGraphGaussianRootEnergy {N m : ℕ} (G : RegularGraph N (m+2))
    (r : ℕ) (x : ℝ) (b : ℕ) :
    (∫ ξ,(N : ℝ)⁻¹*∑ a : Fin r,∑ v : Fin N,
      (finiteSupportGaussianSample (jointGraphGaussianCoefficient G r x b) ξ (a,v))^2
      ∂gaussianLabelLaw (Fin r × Fin N)) =
      (r : ℝ)*(∫ ξ,(N : ℝ)⁻¹*∑ v : Fin N,
        (finiteSupportGaussianSample (graphRadialGaussianCoefficient G.val (m+2) x b) ξ v)^2
        ∂gaussianLabelLaw (Fin N)) := by
  have hi (a : Fin r) (v : Fin N) := integrable_finiteSupportGaussianSample_pow
    (jointGraphGaussianCoefficient G r x b) (a,v) 2
  have hs (v : Fin N) := integrable_finiteSupportGaussianSample_pow
    (graphRadialGaussianCoefficient G.val (m+2) x b) v 2
  rw [integral_const_mul,integral_finset_sum _ (fun a _ =>
    integrable_finset_sum _ (fun v _ => hi a v))]
  simp_rw [integral_finset_sum _ (fun v _ => hi _ v)]
  simp only [integral_finiteSupportGaussianSample_sq,
    jointGraphGaussianCoefficient,finsuppPairing_channelFinsupp,if_pos rfl]
  rw [integral_const_mul,integral_finset_sum _ (fun v _ => hs v)]
  simp_rw [integral_finiteSupportGaussianSample_sq]
  simp only [ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- A root-energy estimate uniform in graph size, with the exact factor r. -/
theorem integral_jointGraphGaussianRootEnergy_le {N m : ℕ} (G : RegularGraph N (m+2))
    (hN : 0 < N) (r : ℕ) (x : ℝ) (b : ℕ) :
    (∫ ξ,(N : ℝ)⁻¹*∑ a : Fin r,∑ v : Fin N,
      (finiteSupportGaussianSample (jointGraphGaussianCoefficient G r x b) ξ (a,v))^2
      ∂gaussianLabelLaw (Fin r × Fin N)) ≤
      (r : ℝ)*(1+radialGraphCollisionBound (m+2) x b*
        ((N : ℝ)⁻¹*badVertexCoverRootCount G (b+1))) := by
  rw [integral_jointGraphGaussianRootEnergy]
  exact mul_le_mul_of_nonneg_left (integral_graphRadialGaussianRootEnergy_le G hN x b)
    (by positivity)

end GaussianWave.BS
