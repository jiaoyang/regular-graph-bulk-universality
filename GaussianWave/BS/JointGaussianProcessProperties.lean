import GaussianWave.BS.IndependentChannelLaw
import GaussianWave.BS.InvariantProcessMoments
import GaussianWave.BS.GaussianSecondMoments
import GaussianWave.BS.LiftedCoverEigenrelations

/-! Actual invariance, coordinate L2 bounds and common-energy eigenrelations
of the literal independent-channel Gaussian tree process. Gaussianity or
eigenprocess properties are not assumed as certificates. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
set_option maxHeartbeats 1200000
namespace GaussianWave.BS

theorem independentChannelLaw_channel {κ V : Type*} [Fintype κ]
    (Q : κ → Measure (V → ℝ)) [∀ a,IsProbabilityMeasure (Q a)] (a : κ) :
    Measure.map (fun z : (κ × V) → ℝ => fun v => z (a,v)) (independentChannelLaw Q)=Q a := by
  have hC : Measurable (fun z : (κ × V) → ℝ => fun v => z (a,v)) :=
    measurable_pi_lambda _ (fun v => measurable_pi_apply (a,v))
  rw [independentChannelLaw,Measure.map_map hC measurable_flattenChannels]
  change Measure.map (Function.eval a) (Measure.pi Q)=Q a
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply a) hs,
    ← Set.univ_pi_update_univ (α := fun _ : κ => V → ℝ) a s,Measure.pi_pi]
  rw [Finset.prod_eq_single a]
  · simp only [Function.update_same]
  · intro b hb hba
    simp only [Function.update_of_ne hba,measure_univ]
  · simp

theorem jointGaussianTreeProcessLaw_invariant (r m : ℕ) (energy : ℝ)
    (he : |energy| < (m+2 : ℝ)) :
    ChannelTreeInvariant (jointGaussianTreeProcessLaw r m energy) := by
  intro e
  change Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
    fun av : Fin r × RegularTreeVertex (m+2) => z (av.1,e av.2))
      (independentChannelLaw (fun _ : Fin r => (gaussianTreeProcessLaw m energy : Measure _)))=_
  rw [independentChannelLaw_window]
  simp_rw [gaussianTreeProcessLaw_invariant m energy he e]
  rfl

theorem gaussianTreeProcessLaw_coordinate_integrable_square (m : ℕ) (energy : ℝ)
    (he : |energy| < (m+2 : ℝ)) (v : RegularTreeVertex (m+2)) :
    Integrable (fun z : RegularTreeVertex (m+2) → ℝ => z v^2)
      (gaussianTreeProcessLaw m energy : Measure (RegularTreeVertex (m+2) → ℝ)) := by
  let Q : Measure (RegularTreeVertex (m+2) → ℝ) := gaussianTreeProcessLaw m energy
  let W (z : RegularTreeVertex (m+2) → ℝ) : Unit → ℝ := fun _ => z v
  have hW : Measurable W := measurable_pi_lambda _ (fun _ => measurable_pi_apply v)
  letI : IsProbabilityMeasure (Measure.map W Q) := isProbabilityMeasure_map hW.aemeasurable
  have hG := gaussianTreeProcessLaw_finite_wave_kernel m energy he (fun _ : Unit => v)
  have hC : (fun i j : Unit => sphericalCovariance (m+2) energy
      ((regularWordTree (m+2)).dist v v))=(1 : Matrix Unit Unit ℝ) := by
    ext i j
    cases i
    cases j
    simp only [SimpleGraph.dist_self,sphericalCovariance_zero,Matrix.one_apply,ite_true]
  rw [hC] at hG
  have hi := gaussian_coordinate_integrable_square (Measure.map W Q) 1 Matrix.PosSemidef.one hG ()
  exact (integrable_map_measure ((measurable_pi_apply ()).pow_const 2).aestronglyMeasurable hW.aemeasurable).1 hi

theorem jointGaussianTreeProcessLaw_coordinate_integrable_square (r m : ℕ) (energy : ℝ)
    (he : |energy| < (m+2 : ℝ)) (av : Fin r × RegularTreeVertex (m+2)) :
    Integrable (fun z => z av^2) (jointGaussianTreeProcessLaw r m energy) := by
  let C (z : (Fin r × RegularTreeVertex (m+2)) → ℝ) : RegularTreeVertex (m+2) → ℝ :=
    fun v => z (av.1,v)
  have hC : Measurable C := measurable_pi_lambda _ (fun v => measurable_pi_apply (av.1,v))
  have hm : Measure.map C (jointGaussianTreeProcessLaw r m energy)=
      (gaussianTreeProcessLaw m energy : Measure _) := independentChannelLaw_channel _ av.1
  have hi : Integrable (fun z : RegularTreeVertex (m+2) → ℝ => z av.2^2)
      (Measure.map C (jointGaussianTreeProcessLaw r m energy)) := by
    rw [hm]
    exact gaussianTreeProcessLaw_coordinate_integrable_square m energy he av.2
  exact (integrable_map_measure ((measurable_pi_apply av.2).pow_const 2).aestronglyMeasurable hC.aemeasurable).1 hi

theorem gaussianTreeProcessLaw_root_eigenrelation (m : ℕ) (energy : ℝ)
    (hne : energy ≠ (m+2 : ℝ)) :
    ∀ᵐ z : RegularTreeVertex (m+2) → ℝ ∂(gaussianTreeProcessLaw m energy : Measure (RegularTreeVertex (m+2) → ℝ)),
      (∑ j : Fin (m+2),z (some (j,[])))=energy*z none := by
  let E (y : VertexBallVertex (m+2) 0 → ℝ) : Prop :=
    (∑ j : Fin (m+2),y (vertexBallNeighbor (m+2) 0 j))=energy*y (vertexBallRoot (m+2) 0)
  have hE : MeasurableSet {y | E y} :=
    (isClosed_eq (continuous_finset_sum (Finset.univ : Finset (Fin (m+2)))
      (fun j _ => continuous_apply (vertexBallNeighbor (m+2) 0 j)))
      ((continuous_const : Continuous (fun _ : VertexBallVertex (m+2) 0 → ℝ => energy)).mul
        (continuous_apply (vertexBallRoot (m+2) 0)))).measurableSet
  have hAE : ∀ᵐ y ∂vertexGaussianBallLaw m 0 energy,E y := by
    rw [vertexGaussianBallLaw]
    apply (ae_map_iff (vertexGaussianMap m 0 energy).continuous_of_finiteDimensional.measurable.aemeasurable hE).mpr
    exact Filter.Eventually.of_forall (fun z => (vertexGaussianMap_eigenrelation m 0 energy hne z).1)
  rw [← gaussianTreeProcessLaw_ball m 0 energy] at hAE
  have hB : Measurable (fun z : RegularTreeVertex (m+2) → ℝ =>
      fun v : VertexBallVertex (m+2) 0 => z (vertexBallEmbedding (m+2) 0 v)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  exact ae_of_ae_map hB.aemeasurable hAE

theorem jointGaussianTreeProcessLaw_root_eigenrelation (r m : ℕ) (energy : ℝ)
    (hne : energy ≠ (m+2 : ℝ)) (a : Fin r) :
    ∀ᵐ z ∂jointGaussianTreeProcessLaw r m energy,
      treeEigenResidual (m+2) r (fun _ => energy) a none z=0 := by
  let C (z : (Fin r × RegularTreeVertex (m+2)) → ℝ) : RegularTreeVertex (m+2) → ℝ := fun v => z (a,v)
  have hC : Measurable C := measurable_pi_lambda _ (fun v => measurable_pi_apply (a,v))
  have hm : Measure.map C (jointGaussianTreeProcessLaw r m energy)=
      (gaussianTreeProcessLaw m energy : Measure _) := independentChannelLaw_channel _ a
  have hscalar := gaussianTreeProcessLaw_root_eigenrelation m energy hne
  rw [← hm] at hscalar
  have ha := ae_of_ae_map hC.aemeasurable hscalar
  filter_upwards [ha] with z hz
  unfold treeEigenResidual
  rw [tree_root_neighbor_sum]
  exact sub_eq_zero.mpr hz

theorem jointGaussianTreeProcessLaw_eigenrelation (r m : ℕ) (energy : ℝ)
    (he : |energy| < (m+2 : ℝ)) (a : Fin r) (u : RegularTreeVertex (m+2)) :
    ∀ᵐ z ∂jointGaussianTreeProcessLaw r m energy,
      treeEigenResidual (m+2) r (fun _ => energy) a u z=0 := by
  let e := regularTreeReroot (m+1) u
  have hInv := jointGaussianTreeProcessLaw_invariant r m energy he e
  have hr : ∀ᵐ z ∂Measure.map (channelTreeRelabel e) (jointGaussianTreeProcessLaw r m energy),
      treeEigenResidual (m+2) r (fun _ => energy) a none z=0 := by
    rw [hInv]
    exact jointGaussianTreeProcessLaw_root_eigenrelation r m energy
      (ne_of_lt ((le_abs_self _).trans_lt he)) a
  have ha := ae_of_ae_map (measurable_channelTreeRelabel e).aemeasurable hr
  filter_upwards [ha] with z hz
  change treeEigenResidual (m+2) r (fun _ => energy) a none (fun av => z (av.1,e av.2))=0 at hz
  rw [treeEigenResidual_equivariant,regularTreeReroot_root] at hz
  exact hz

theorem jointGaussianTreeProcessLaw_ae_eigenrelations (r m : ℕ) (energy : ℝ)
    (he : |energy| < (m+2 : ℝ)) :
    ∀ᵐ z ∂jointGaussianTreeProcessLaw r m energy,∀ a u,
      treeEigenResidual (m+2) r (fun _ => energy) a u z=0 := by
  apply ae_all_iff.mpr
  intro a
  apply ae_all_iff.mpr
  intro u
  exact jointGaussianTreeProcessLaw_eigenrelation r m energy he a u

theorem jointGaussianTreeProcessLaw_root_identitySecondMoments (r m : ℕ) (energy : ℝ)
    (he : |energy| < (m+2 : ℝ)) :
    HasIdentitySecondMoments (rootChannelLaw (jointGaussianTreeProcessLaw r m energy)) := by
  let W (z : (Fin r × RegularTreeVertex (m+2)) → ℝ) : (Fin r × Unit) → ℝ :=
    fun aj => z (aj.1,none)
  have hW : Measurable W := measurable_pi_lambda _ (fun aj => measurable_pi_apply (aj.1,none))
  letI : IsProbabilityMeasure (Measure.map W (jointGaussianTreeProcessLaw r m energy)) :=
    isProbabilityMeasure_map hW.aemeasurable
  have hG := jointGaussianTreeProcessLaw_finite_wave_kernel r m energy he (fun _ : Unit => none)
  have hC : channelBlockCovariance (fun _ : Fin r => fun i j : Unit => sphericalCovariance (m+2) energy
      ((regularWordTree (m+2)).dist none none))=(1 : Matrix (Fin r × Unit) (Fin r × Unit) ℝ) := by
    ext ⟨a,i⟩ ⟨b,j⟩
    cases i
    cases j
    simp only [channelBlockCovariance,SimpleGraph.dist_self,sphericalCovariance_zero,Matrix.one_apply,Prod.mk.injEq,and_true]
  rw [hC] at hG
  have hmom := gaussian_hasSecondMoments (Measure.map W (jointGaussianTreeProcessLaw r m energy))
    1 Matrix.PosSemidef.one hG
  intro a b
  have h := hmom (a,()) (b,())
  rw [integral_map hW.aemeasurable
    (((measurable_pi_apply (a,())).mul (measurable_pi_apply (b,()))).aestronglyMeasurable)] at h
  rw [rootChannelLaw_integral_product]
  simpa only [W,treeMixedMoment,Matrix.one_apply,Prod.mk.injEq,and_true] using h

theorem jointGaussianTreeProcessLaw_mean_zero (r m : ℕ) (energy : ℝ)
    (he : |energy| < (m+2 : ℝ)) (a : Fin r) (u : RegularTreeVertex (m+2)) :
    treeChannelMean (jointGaussianTreeProcessLaw r m energy) a u=0 :=
  treeChannelMean_zero_of_eigenrelation _ (jointGaussianTreeProcessLaw_invariant r m energy he)
    (jointGaussianTreeProcessLaw_coordinate_integrable_square r m energy he) energy
    (ne_of_lt ((le_abs_self _).trans_lt he)) a (jointGaussianTreeProcessLaw_root_eigenrelation r m energy
      (ne_of_lt ((le_abs_self _).trans_lt he)) a) u

theorem jointGaussianTreeProcessLaw_root_mean_zero (r m : ℕ) (energy : ℝ)
    (he : |energy| < (m+2 : ℝ)) (a : Fin r) :
    (∫ x,x a ∂rootChannelLaw (jointGaussianTreeProcessLaw r m energy))=0 := by
  rw [rootChannelLaw,integral_map measurable_rootChannel.aemeasurable (measurable_pi_apply a).aestronglyMeasurable]
  exact jointGaussianTreeProcessLaw_mean_zero r m energy he a none

theorem jointGaussianTreeProcessLaw_coordinate_second (r m : ℕ) (energy : ℝ)
    (he : |energy| < (m+2 : ℝ)) (av : Fin r × RegularTreeVertex (m+2)) :
    (∫ x,x av^2 ∂jointGaussianTreeProcessLaw r m energy)=1 := by
  have hroot := jointGaussianTreeProcessLaw_root_identitySecondMoments r m energy he av.1 av.1
  rw [rootChannelLaw_integral_product] at hroot
  simp only [if_pos rfl] at hroot
  have hinv := treeMixedMoment_invariant (jointGaussianTreeProcessLaw r m energy)
    (jointGaussianTreeProcessLaw_invariant r m energy he) (regularTreeReroot (m+1) av.2) av.1 av.1 none none
  rw [regularTreeReroot_root] at hinv
  simpa only [treeMixedMoment,pow_two] using hinv.trans hroot

end GaussianWave.BS
