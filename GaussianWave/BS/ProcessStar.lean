import GaussianWave.BS.InvariantEigenCovariance
import GaussianWave.BS.ActualSecondMomentMatrix
import GaussianWave.BS.TreeBallDistances
import GaussianWave.BS.TreeEigenWindowSupport
import GaussianWave.BS.ColoredPhysicalUpperBound

/-! Actual star and whole-edge marginals of an invariant tree eigenprocess.
The covariance, edge reversal, and neighbor permutations used by the heat
flow upper bound are derived from the process, rather than postulated. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

def treeStarSite (d : ℕ) : Fin (d+1) → RegularTreeVertex d :=
  Fin.cases none (fun a => some (a,[]))

def processStar {r d : ℕ} (x : (Fin r × RegularTreeVertex d) → ℝ) :
    (Fin r × Fin (d+1)) → ℝ := fun av => x (av.1,treeStarSite d av.2)

def processStarLaw {r d : ℕ} (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ)) :=
  Measure.map processStar μ

theorem measurable_processStar {r d : ℕ} : Measurable (@processStar r d) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

instance processStarLaw_probability {r d : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (processStarLaw μ) :=
  isProbabilityMeasure_map measurable_processStar.aemeasurable

def processEdgeLaw {r d : ℕ} (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ)) (i : Fin d) :=
  Measure.map (coloredPhysicalEdgeCoordinates i) (processStarLaw μ)

instance processEdgeLaw_probability {r d : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ)) [IsProbabilityMeasure μ] (i : Fin d) :
    IsProbabilityMeasure (processEdgeLaw μ i) :=
  isProbabilityMeasure_map (measurable_coloredPhysicalEdgeCoordinates i).aemeasurable

theorem treeStarSite_dist (d : ℕ) (i j : Fin (d+1)) :
    (regularWordTree d).dist (treeStarSite d i) (treeStarSite d j)=
      RegularEigenData.starDistance d i j := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [treeStarSite,RegularEigenData.starDistance]
    · simp [treeStarSite,RegularEigenData.starDistance,regularTree_dist_root,regularTreeDepth]
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [SimpleGraph.dist_comm]
      simp [treeStarSite,RegularEigenData.starDistance,regularTree_dist_root,regularTreeDepth]
    · by_cases h : i=j
      · subst j
        simp [treeStarSite,RegularEigenData.starDistance]
      · simpa [treeStarSite,RegularEigenData.starDistance,h] using
          regularTree_dist_distinct_branches d i j [] [] h

theorem processStarLaw_secondMoments {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hμ : ChannelTreeInvariant μ) (hi : ∀ av,Integrable (fun x => x av^2) μ)
    (energy : ℝ)
    (hE : ∀ b v,∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) b v x=0)
    (hroot : HasIdentitySecondMoments (rootChannelLaw μ)) :
    HasSecondMoments (processStarLaw μ)
      (coloredPhysicalStarCovariance (m+2) r (energy/(m+2))) := by
  rintro ⟨a,i⟩ ⟨b,j⟩
  rw [processStarLaw,integral_map measurable_processStar.aemeasurable
    (((measurable_pi_apply (a,i)).mul (measurable_pi_apply (b,j))).aestronglyMeasurable)]
  change treeMixedMoment μ a b (treeStarSite (m+2) i) (treeStarSite (m+2) j)=_
  rw [treeMixedMoment_eq_spherical μ hμ hi energy hE,treeStarSite_dist]
  have hroot' : treeMixedMoment μ a b none none=if a=b then 1 else 0 := by
    rw [← rootChannelLaw_integral_product]
    exact hroot a b
  rw [hroot',← RegularEigenData.starWaveCovariance_eq_spherical (m+2) energy (by positivity)]
  have henergy : (m+2 : ℝ)*(energy/(m+2))=energy := by field_simp
  simp only [coloredPhysicalStarCovariance,channelLiftMatrix,henergy]
  by_cases hab : a=b
  · subst b
    simp only [ite_true,one_mul,Nat.cast_add,Nat.cast_ofNat,henergy]
  · simp only [if_neg hab,if_neg (Ne.symm hab),zero_mul]

theorem processStarLaw_permutation {r d : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (hμ : ChannelTreeInvariant μ) (p : Equiv.Perm (Fin d)) :
    Measure.map (coloredPhysicalStarPermutation p) (processStarLaw μ)=processStarLaw μ := by
  rw [processStarLaw,Measure.map_map (measurable_coloredPhysicalStarPermutation p) measurable_processStar]
  have he := congrArg (Measure.map (@processStar r d)) (hμ (regularTreeRootPermutation d p))
  rw [Measure.map_map measurable_processStar (measurable_channelTreeRelabel _)] at he
  convert he using 1
  congr 1
  funext x av
  rcases av with ⟨a,j⟩
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

def regularTreeEdgeSwap (m : ℕ) (i : Fin (m+2)) :
    regularWordTree (m+2) ≃g regularWordTree (m+2) :=
  ((regularTreeRootPermutation (m+2) (Equiv.swap i 0)).trans
    (regularTreeEdgeFlip (m+1))).trans
      (regularTreeRootPermutation (m+2) (Equiv.swap 0 i))

@[simp] theorem regularTreeEdgeSwap_root (m : ℕ) (i : Fin (m+2)) :
    regularTreeEdgeSwap m i none=some (i,[]) := by
  change regularTreeRootPermutation (m+2) (Equiv.swap 0 i)
    (regularTreeEdgeFlip (m+1) (regularTreeRootPermutation (m+2) (Equiv.swap i 0) none))=_
  rw [regularTreeRootPermutation_root]
  change regularTreeRootPermutation (m+2) (Equiv.swap 0 i) (some (0,[]))=_
  rw [regularTreeRootPermutation_some,Equiv.swap_apply_left]

@[simp] theorem regularTreeEdgeSwap_neighbor (m : ℕ) (i : Fin (m+2)) :
    regularTreeEdgeSwap m i (some (i,[]))=none := by
  change regularTreeRootPermutation (m+2) (Equiv.swap 0 i)
    (regularTreeEdgeFlip (m+1) (regularTreeRootPermutation (m+2) (Equiv.swap i 0) (some (i,[]))))=_
  rw [regularTreeRootPermutation_some,Equiv.swap_apply_left]
  change regularTreeRootPermutation (m+2) (Equiv.swap 0 i) none=none
  exact regularTreeRootPermutation_root _ _

theorem processEdgeLaw_reversal {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hμ : ChannelTreeInvariant μ) (i : Fin (m+2)) :
    Measure.map (edgeFlipLinear r) (processEdgeLaw μ i)=processEdgeLaw μ i := by
  let F := fun x : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
    coloredPhysicalEdgeCoordinates i (processStar x)
  have hF : Measurable F := (measurable_coloredPhysicalEdgeCoordinates i).comp measurable_processStar
  have hL : processEdgeLaw μ i=Measure.map F μ :=
    Measure.map_map (measurable_coloredPhysicalEdgeCoordinates i) measurable_processStar
  rw [hL,Measure.map_map (edgeFlipLinear r).continuous.measurable hF]
  have he := congrArg (Measure.map F) (hμ (regularTreeEdgeSwap m i))
  rw [Measure.map_map hF (measurable_channelTreeRelabel _)] at he
  convert he using 1
  congr 1
  funext x ba
  rcases ba with ⟨b,a⟩
  cases b <;> simp only [F,edgeFlipLinear,coordinatePermutation_apply,edgeFlipIndex,
    coloredPhysicalEdgeCoordinates,physicalEdgeCoordinates,processStar,treeStarSite,
    channelTreeRelabel,Function.comp_apply,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false,
    Fin.cases_zero,Fin.cases_succ]
  · exact congrArg (fun v => x (a,v)) (regularTreeEdgeSwap_root m i).symm
  · exact congrArg (fun v => x (a,v)) (regularTreeEdgeSwap_neighbor m i).symm

theorem processStarLaw_ae_hyperplane {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) (energy : ℝ)
    (hE : ∀ a,∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) a none x=0) :
    ∀ᵐ z ∂processStarLaw μ,z∈coloredPhysicalStarHyperplane (m+2) r (energy/(m+2)) := by
  have hclosed := (Submodule.closed_of_finiteDimensional
    (coloredPhysicalStarHyperplane (m+2) r (energy/(m+2)))).measurableSet
  apply (ae_map_iff measurable_processStar.aemeasurable hclosed).2
  have hEall : ∀ᵐ x ∂μ,∀ a,treeEigenResidual (m+2) r (fun _ => energy) a none x=0 :=
    (ae_all_iff).2 hE
  filter_upwards [hEall] with x hx
  intro a
  have h := sub_eq_zero.mp (hx a)
  change (∑ z : (regularWordTree (m+2)).neighborSet none,x (a,z.val))=energy*x (a,none) at h
  rw [regularTree_sum_neighbor_root (m+2) (fun v => x (a,v))] at h
  change (∑ i : Fin (m+2),x (a,some (i,[])))=
    ((m+2 : ℕ) : ℝ)*(energy/(m+2))*x (a,none)
  have henergy : (m+2 : ℝ)*(energy/(m+2))=energy := by field_simp
  rw [Nat.cast_add,Nat.cast_ofNat,henergy]
  exact h

end GaussianWave.BS
