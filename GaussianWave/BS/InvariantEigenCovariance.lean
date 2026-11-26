import GaussianWave.BS.InvariantProcessMoments
import GaussianWave.Covariance

/-! The covariance of any invariant finite-L2 tree eigenprocess is the
spherical kernel times its actual root mixed-second-moment matrix. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

theorem treeMixedMoment_neighbor_sum {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (energy : ℝ) (a b : Fin r)
    (v : RegularTreeVertex (m+2))
    (hE : ∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) b v x=0) :
    (∑ z : (regularWordTree (m+2)).neighborSet v,treeMixedMoment μ a b none z.val)=
      energy*treeMixedMoment μ a b none v := by
  have hsum := integral_finset_sum (Finset.univ : Finset ((regularWordTree (m+2)).neighborSet v))
    (fun z _ => integrable_treeCoordinate_product_of_second μ hi (a,none) (b,z.val))
  calc
    _ = ∫ x,∑ z : (regularWordTree (m+2)).neighborSet v,x (a,none)*x (b,z.val) ∂μ := hsum.symm
    _ = ∫ x,energy*(x (a,none)*x (b,v)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hE] with x hx
      have hh : (∑ z : (regularWordTree (m+2)).neighborSet v,x (b,z.val))=energy*x (b,v) := sub_eq_zero.mp hx
      rw [← Finset.mul_sum,hh]
      ring
    _ = _ := integral_const_mul _ _

theorem treeMixedMoment_radial_recurrence {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hμ : ChannelTreeInvariant μ) (hi : ∀ av,Integrable (fun x => x av^2) μ)
    (energy : ℝ) (a b : Fin r)
    (hE : ∀ v,∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) b v x=0) :
    let c := fun n => treeMixedMoment μ a b none (regularTreeRay m n)
    ((m+2 : ℕ) : ℝ)*c 1=energy*c 0 ∧
      ∀ n,c n+(((m+2 : ℕ) : ℝ)-1)*c (n+2)=energy*c (n+1) := by
  let c := fun n => treeMixedMoment μ a b none (regularTreeRay m n)
  have hrad (z : RegularTreeVertex (m+2)) :
      treeMixedMoment μ a b none z=c ((regularWordTree (m+2)).dist z none) := by
    rw [SimpleGraph.dist_comm]
    exact treeMixedMoment_radial_root μ hμ a b z
  have hsum (v : RegularTreeVertex (m+2)) :
      (∑ z : (regularWordTree (m+2)).neighborSet v,c ((regularWordTree (m+2)).dist z.val none)) =
        energy*treeMixedMoment μ a b none v := by
    simpa only [← hrad] using treeMixedMoment_neighbor_sum μ hi energy a b v (hE v)
  have htree (v : RegularTreeVertex (m+2)) := tree_sum_neighbor_radial (regularWordTree_isTree (m+2))
    (m+2) (regularWordTree_regular (m+2) (by omega)) c v none
  constructor
  · have h := hsum none
    rw [htree none,if_pos rfl] at h
    exact h
  · intro n
    have h := hsum (regularTreeRay m (n+1))
    rw [htree (regularTreeRay m (n+1)),if_neg (by exact Option.some_ne_none _)] at h
    have hd : (regularWordTree (m+2)).dist (regularTreeRay m (n+1)) none=n+1 := by
      rw [SimpleGraph.dist_comm,regularTreeRay_dist]
    rw [hd,Nat.add_sub_cancel] at h
    exact h

theorem treeMixedMoment_eq_spherical {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hμ : ChannelTreeInvariant μ) (hi : ∀ av,Integrable (fun x => x av^2) μ)
    (energy : ℝ) (hE : ∀ b v,∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) b v x=0)
    (a b : Fin r) (u v : RegularTreeVertex (m+2)) :
    treeMixedMoment μ a b u v=treeMixedMoment μ a b none none *
      sphericalCovariance (m+2) energy ((regularWordTree (m+2)).dist u v) := by
  obtain ⟨hone,hrec⟩ := treeMixedMoment_radial_recurrence μ hμ hi energy a b (hE b)
  have hd0 : ((m+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hd1 : ((m+2 : ℕ) : ℝ)-1 ≠ 0 := by
    norm_num only [Nat.cast_add,Nat.cast_ofNat]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h := covariance_eq_scaled_spherical (m+2) energy (treeMixedMoment μ a b none none)
    hd0 hd1
    (fun n => treeMixedMoment μ a b none (regularTreeRay m n)) rfl hone hrec
  rw [treeMixedMoment_radial μ hμ]
  exact h _

end GaussianWave.BS
