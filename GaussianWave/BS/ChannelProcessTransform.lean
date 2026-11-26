import GaussianWave.BS.InvariantProcessMoments
import GaussianWave.BS.ActualSecondMomentMatrix
import GaussianWave.BS.RankSupportReduction

/-! Pointwise channel linear maps of actual process laws preserve the
ordinary invariance, L2, and common-energy eigenprocess properties. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

def channelProcessMap {r s d : ℕ} (A : Matrix (Fin s) (Fin r) ℝ)
    (x : (Fin r × RegularTreeVertex d) → ℝ) : (Fin s × RegularTreeVertex d) → ℝ :=
  fun av => ∑ b,A av.1 b*x (b,av.2)

theorem continuous_channelProcessMap {r s d : ℕ} (A : Matrix (Fin s) (Fin r) ℝ) :
    Continuous (channelProcessMap (d := d) A) := by
  apply continuous_pi
  intro av
  exact continuous_finset_sum _ (fun b _ => continuous_const.mul (continuous_apply (b,av.2)))

theorem channelProcessMap_mul {r s t d : ℕ} (A : Matrix (Fin t) (Fin s) ℝ)
    (B : Matrix (Fin s) (Fin r) ℝ) (x : (Fin r × RegularTreeVertex d) → ℝ) :
    channelProcessMap A (channelProcessMap B x)=channelProcessMap (A*B) x := by
  funext av
  change A.mulVec (B.mulVec (fun b => x (b,av.2))) av.1=(A*B).mulVec (fun b => x (b,av.2)) av.1
  rw [Matrix.mulVec_mulVec]

theorem channelProcessMap_invariant {r s d : ℕ} (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (hμ : ChannelTreeInvariant μ) (A : Matrix (Fin s) (Fin r) ℝ) :
    ChannelTreeInvariant (Measure.map (channelProcessMap A) μ) := by
  intro e
  have hA := (continuous_channelProcessMap (d := d) A).measurable
  have hR := measurable_channelTreeRelabel (r := r) e
  have hS := measurable_channelTreeRelabel (r := s) e
  rw [Measure.map_map hS hA]
  have hc : channelTreeRelabel e ∘ channelProcessMap A = channelProcessMap A ∘ channelTreeRelabel e := rfl
  rw [hc,← Measure.map_map hA hR,hμ e]

theorem channelProcessMap_integrable_sq {r s d : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (A : Matrix (Fin s) (Fin r) ℝ)
    (av : Fin s × RegularTreeVertex d) :
    Integrable (fun x => x av^2) (Measure.map (channelProcessMap A) μ) := by
  apply (integrable_map_measure ((measurable_pi_apply av).pow_const 2).aestronglyMeasurable
    (continuous_channelProcessMap A).measurable.aemeasurable).mpr
  have hcoord (b : Fin r) : MemLp (fun x : (Fin r × RegularTreeVertex d) → ℝ => x (b,av.2)) 2 μ :=
    (memLp_two_iff_integrable_sq (measurable_pi_apply (b,av.2)).aestronglyMeasurable).2 (hi (b,av.2))
  have hsum := memLp_finset_sum (Finset.univ : Finset (Fin r)) (fun b _ => (hcoord b).const_mul (A av.1 b))
  exact (memLp_two_iff_integrable_sq
    (((continuous_apply av).comp (continuous_channelProcessMap A)).measurable.aestronglyMeasurable)).1 hsum

theorem rootChannelLaw_channelProcessMap {r s d : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ)) (A : Matrix (Fin s) (Fin r) ℝ) :
    rootChannelLaw (Measure.map (channelProcessMap A) μ) = Measure.map A.mulVec (rootChannelLaw μ) := by
  rw [rootChannelLaw,rootChannelLaw,Measure.map_map measurable_rootChannel
    (continuous_channelProcessMap A).measurable,
    Measure.map_map (measurable_finiteMatrixAction A) measurable_rootChannel]
  rfl

theorem channelProcessMap_eigenrelations {r s d : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ)) (energy : ℝ)
    (hE : ∀ᵐ x ∂μ,∀ a v,treeEigenResidual d r (fun _ => energy) a v x=0)
    (A : Matrix (Fin s) (Fin r) ℝ) (a : Fin s) (v : RegularTreeVertex d) :
    ∀ᵐ x ∂Measure.map (channelProcessMap A) μ,treeEigenResidual d s (fun _ => energy) a v x=0 := by
  apply (ae_map_iff (continuous_channelProcessMap A).measurable.aemeasurable
    (measurableSet_eq_fun (continuous_treeEigenResidual d s (fun _ => energy) a v).measurable measurable_const)).2
  filter_upwards [hE] with x hx
  have he (b : Fin r) : (∑ z : (regularWordTree d).neighborSet v,x (b,z.val))=energy*x (b,v) :=
    sub_eq_zero.mp (hx b v)
  unfold treeEigenResidual channelProcessMap
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,he]
  rw [Finset.mul_sum]
  have hterm (b : Fin r) : A a b*(energy*x (b,v))=energy*(A a b*x (b,v)) := by ring
  simp_rw [hterm]
  exact sub_self _

end GaussianWave.BS
