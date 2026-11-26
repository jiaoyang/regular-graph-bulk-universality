import GaussianWave.BS.WholeCoverInvariance
import GaussianWave.BS.TreeHomogeneity
import GaussianWave.BS.ProcessEigenrelations
import GaussianWave.Transport

/-! Stationary means and radial mixed second moments follow from literal
tree symmetries and coordinate L2 bounds. No Gaussianity is used. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

def channelTreeRelabel {r d : ℕ} (e : regularWordTree d ≃g regularWordTree d)
    (x : (Fin r × RegularTreeVertex d) → ℝ) : (Fin r × RegularTreeVertex d) → ℝ :=
  fun av => x (av.1,e av.2)

def ChannelTreeInvariant {r d : ℕ} (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ)) : Prop :=
  ∀ e : regularWordTree d ≃g regularWordTree d,Measure.map (channelTreeRelabel e) μ=μ

theorem measurable_channelTreeRelabel {r d : ℕ} (e : regularWordTree d ≃g regularWordTree d) :
    Measurable (channelTreeRelabel (r := r) e) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

def treeChannelMean {r d : ℕ} (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (a : Fin r) (v : RegularTreeVertex d) : ℝ := ∫ x,x (a,v) ∂μ

def treeMixedMoment {r d : ℕ} (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (a b : Fin r) (u v : RegularTreeVertex d) : ℝ := ∫ x,x (a,u)*x (b,v) ∂μ

theorem treeChannelMean_invariant {r d : ℕ} (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (hμ : ChannelTreeInvariant μ) (e : regularWordTree d ≃g regularWordTree d)
    (a : Fin r) (v : RegularTreeVertex d) : treeChannelMean μ a (e v)=treeChannelMean μ a v := by
  have h := integral_map (μ := μ) (measurable_channelTreeRelabel e).aemeasurable
    (measurable_pi_apply (a,v)).aestronglyMeasurable
  rw [hμ e] at h
  exact h.symm

theorem treeMixedMoment_invariant {r d : ℕ} (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (hμ : ChannelTreeInvariant μ) (e : regularWordTree d ≃g regularWordTree d)
    (a b : Fin r) (u v : RegularTreeVertex d) :
    treeMixedMoment μ a b (e u) (e v)=treeMixedMoment μ a b u v := by
  have h := integral_map (μ := μ) (measurable_channelTreeRelabel e).aemeasurable
    (((measurable_pi_apply (a,u)).mul (measurable_pi_apply (b,v))).aestronglyMeasurable)
  rw [hμ e] at h
  exact h.symm

theorem treeChannelMean_constant {r m : ℕ} (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hμ : ChannelTreeInvariant μ) (a : Fin r) (v : RegularTreeVertex (m+2)) :
    treeChannelMean μ a v=treeChannelMean μ a none := by
  have h := treeChannelMean_invariant μ hμ (regularTreeReroot (m+1) v) a none
  simpa only [regularTreeReroot_root] using h

theorem integrable_treeCoordinate_of_second {r d : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (av : Fin r × RegularTreeVertex d) :
    Integrable (fun x => x av) μ :=
  integrable_of_integrable_square μ _ (measurable_pi_apply av).aestronglyMeasurable (hi av)

theorem integrable_treeCoordinate_product_of_second {r d : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (av bv : Fin r × RegularTreeVertex d) :
    Integrable (fun x => x av*x bv) μ := by
  have hA := (memLp_two_iff_integrable_sq (measurable_pi_apply av).aestronglyMeasurable).2 (hi av)
  have hB := (memLp_two_iff_integrable_sq (measurable_pi_apply bv).aestronglyMeasurable).2 (hi bv)
  exact hA.integrable_mul hB

theorem treeChannelMean_zero_of_eigenrelation {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ChannelTreeInvariant μ) (hi : ∀ av,Integrable (fun x => x av^2) μ)
    (energy : ℝ) (hne : energy ≠ (m+2 : ℝ)) (a : Fin r)
    (hE : ∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) a none x=0) :
    ∀ v,treeChannelMean μ a v=0 := by
  have hsum := integral_finset_sum (Finset.univ : Finset ((regularWordTree (m+2)).neighborSet none))
    (fun z _ => integrable_treeCoordinate_of_second μ hi (a,z.val))
  have heq : (∫ x,∑ z : (regularWordTree (m+2)).neighborSet none,x (a,z.val) ∂μ) =
      energy*treeChannelMean μ a none := by
    calc
      _ = ∫ x,energy*x (a,none) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hE] with x hx
        exact sub_eq_zero.mp hx
      _ = _ := integral_const_mul _ _
  have hcard : Fintype.card ((regularWordTree (m+2)).neighborSet none)=m+2 := by
    rw [← Fintype.card_congr (regularTreeNeighborEquiv (m+2) none)]
    simp only [RegularTreeNeighborIndex,Fintype.card_fin]
  have hm : (m+2 : ℝ)*treeChannelMean μ a none = energy*treeChannelMean μ a none := by
    rw [hsum] at heq
    change (∑ z : (regularWordTree (m+2)).neighborSet none,treeChannelMean μ a z.val)=_ at heq
    simp_rw [treeChannelMean_constant μ hμ] at heq
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard,Nat.cast_add,Nat.cast_ofNat] using heq
  have hzero : treeChannelMean μ a none=0 := by
    apply (mul_eq_zero.mp (show (energy-(m+2 : ℝ))*treeChannelMean μ a none=0 by nlinarith)).resolve_left
    exact sub_ne_zero.mpr hne
  intro v
  rw [treeChannelMean_constant μ hμ,hzero]

def regularTreeRay (m : ℕ) : ℕ → RegularTreeVertex (m+2)
  | 0 => none
  | n+1 => some (0,List.replicate n (0 : Fin (m+1)))

theorem regularTreeRay_dist (m n : ℕ) : (regularWordTree (m+2)).dist none (regularTreeRay m n)=n := by
  rw [regularTree_dist_root]
  cases n <;> simp [regularTreeRay,regularTreeDepth]

theorem treeMixedMoment_radial_root {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) (hμ : ChannelTreeInvariant μ)
    (a b : Fin r) (v : RegularTreeVertex (m+2)) :
    treeMixedMoment μ a b none v = treeMixedMoment μ a b none
      (regularTreeRay m ((regularWordTree (m+2)).dist none v)) := by
  obtain ⟨e,he,hv⟩ := exists_regularTreeSphereAutomorphism (m+1) none v
    (regularTreeRay m ((regularWordTree (m+2)).dist none v)) (by rw [regularTreeRay_dist])
  have h := treeMixedMoment_invariant μ hμ e a b none v
  rw [he,hv] at h
  exact h.symm

theorem treeMixedMoment_radial {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) (hμ : ChannelTreeInvariant μ)
    (a b : Fin r) (u v : RegularTreeVertex (m+2)) :
    treeMixedMoment μ a b u v = treeMixedMoment μ a b none
      (regularTreeRay m ((regularWordTree (m+2)).dist u v)) := by
  let e := regularTreeReroot (m+1) u
  have he : e none=u := regularTreeReroot_root _ _
  have h := treeMixedMoment_invariant μ hμ e a b none (e.symm v)
  rw [he,e.apply_symm_apply] at h
  have hd := regularTreeIso_dist (m+2) e none (e.symm v)
  rw [he,e.apply_symm_apply] at hd
  rw [h,treeMixedMoment_radial_root μ hμ,← hd]

end GaussianWave.BS
