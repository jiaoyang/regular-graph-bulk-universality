import GaussianWave.BS.ProcessStarUpperBound
import GaussianWave.BS.ProcessBallMarginals

/-! Root-neighbor differences are an actual invertible chart of the
eigenrelation star; at C0 they are precisely the raw innovation coordinates. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

def starDifferenceMap (d r : ℕ) :
    ((Fin r × Fin (d+1)) → ℝ) →ₗ[ℝ] ((Fin r × Fin d) → ℝ) where
  toFun z := fun ai => z (ai.1,ai.2.succ)-z (ai.1,0)
  map_add' x y := by ext ai; simp only [Pi.add_apply]; ring
  map_smul' t x := by ext ai; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

theorem starDifferenceMap_injective_on_hyperplane (d r : ℕ) (hd : 2 ≤ d)
    (c : ℝ) (hc : |c|<1) :
    Function.Injective (fun z : coloredPhysicalStarHyperplane d r c => starDifferenceMap d r z) := by
  intro x y hxy
  apply Subtype.ext
  funext ⟨a,j⟩
  have hs := congrArg (fun z : (Fin r × Fin d) → ℝ => ∑ i,z (a,i)) hxy
  change (∑ i : Fin d,(x.val (a,i.succ)-x.val (a,0)))=
    ∑ i : Fin d,(y.val (a,i.succ)-y.val (a,0)) at hs
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib] at hs
  have hx : (∑ i : Fin d,x.val (a,i.succ))=(d : ℝ)*c*x.val (a,0) := x.property a
  have hy : (∑ i : Fin d,y.val (a,i.succ))=(d : ℝ)*c*y.val (a,0) := y.property a
  rw [hx,hy] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hne : (d : ℝ)*c-d ≠ 0 := by
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d≠0)
    have hc1 : c≠1 := ne_of_lt ((le_abs_self c).trans_lt hc)
    intro he
    apply hc1
    apply (mul_left_cancel₀ hd0)
    linarith
  have hr : x.val (a,0)=y.val (a,0) := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show ((d : ℝ)*c-d)*(x.val (a,0)-y.val (a,0))=0 by nlinarith)).resolve_left hne
  refine Fin.cases hr (fun i => ?_) j
  have hh := congrFun hxy (a,i)
  change x.val (a,i.succ)-x.val (a,0)=y.val (a,i.succ)-y.val (a,0) at hh
  linarith

def starDifferenceEquiv (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c|<1) :
    coloredPhysicalStarHyperplane d r c ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ) := by
  let L := (starDifferenceMap d r).comp (coloredPhysicalStarHyperplane d r c).subtype
  have hi : Function.Injective L := starDifferenceMap_injective_on_hyperplane d r hd c hc
  have hdim : Module.finrank ℝ (coloredPhysicalStarHyperplane d r c)=
      Module.finrank ℝ ((Fin r × Fin d) → ℝ) := (coloredPhysicalStarEquiv d r hd c hc).finrank_eq.symm
  exact LinearEquiv.ofBijective L ⟨hi,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩

@[simp] theorem starDifferenceEquiv_apply (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c|<1)
    (z : coloredPhysicalStarHyperplane d r c) : starDifferenceEquiv d r hd c hc z=starDifferenceMap d r z := rfl

def zeroForestInnovationIndex (A : Type*) (q : ℕ) :
    (A ⊕ (A × BranchInnovation q 0)) ≃ A where
  toFun := Sum.elim id (fun aj => Empty.elim aj.2)
  invFun := Sum.inl
  left_inv j := by cases j with | inl a => rfl | inr aj => exact Empty.elim aj.2
  right_inv _ := rfl

def zeroVertexInnovationIndex (r m : ℕ) :
    (Fin r × VertexBallInnovation (m+2) 0) ≃ (Fin r × Fin (m+2)) :=
  (Equiv.refl (Fin r)).prodCongr (zeroForestInnovationIndex (Fin (m+2)) (m+1))

def zeroEdgeInnovationIndex (r m : ℕ) :
    (Fin r × EdgeBallInnovation (m+2) 0) ≃ (Bool × Fin r) :=
  ((Equiv.refl (Fin r)).prodCongr (zeroForestInnovationIndex Bool (m+1))).trans (Equiv.prodComm _ _)

theorem zero_vertex_innovation_law {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) :
    Measure.map (coordinateReindex (zeroVertexInnovationIndex r m)) (jointVertexInnovationProcessLaw μ 0)=
      Measure.map (starDifferenceMap (m+2) r) (processStarLaw μ) := by
  rw [jointVertexInnovationProcessLaw,jointVertexProcessBallLaw,processStarLaw,
    Measure.map_map (measurable_coordinateReindex _) (jointVertexBallExtract (Fin r) m 0).continuous_of_finiteDimensional.measurable,
    Measure.map_map ((measurable_coordinateReindex _).comp
      (jointVertexBallExtract (Fin r) m 0).continuous_of_finiteDimensional.measurable) (measurable_jointTreeWindow _),
    Measure.map_map (starDifferenceMap (m+2) r).continuous_of_finiteDimensional.measurable measurable_processStar]
  rfl

theorem zero_edge_innovation_law {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) :
    Measure.map (coordinateReindex (zeroEdgeInnovationIndex r m)) (jointEdgeInnovationProcessLaw μ 0)=
      processEdgeLaw μ 0 := by
  rw [jointEdgeInnovationProcessLaw,jointEdgeProcessBallLaw,processEdgeLaw,processStarLaw,
    Measure.map_map (measurable_coordinateReindex _) (jointEdgeBallExtract (Fin r) m 0).continuous_of_finiteDimensional.measurable,
    Measure.map_map ((measurable_coordinateReindex _).comp
      (jointEdgeBallExtract (Fin r) m 0).continuous_of_finiteDimensional.measurable) (measurable_jointTreeWindow _),
    Measure.map_map (measurable_coloredPhysicalEdgeCoordinates _) measurable_processStar]
  congr 1
  funext x ⟨b,a⟩
  cases b <;> rfl

theorem processEdgeLaw_eq_zero {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) (hμ : ChannelTreeInvariant μ)
    (i : Fin (m+2)) : processEdgeLaw μ i=processEdgeLaw μ 0 := by
  let p : Equiv.Perm (Fin (m+2)) := Equiv.swap 0 i
  have h := congrArg (Measure.map (coloredPhysicalEdgeCoordinates (0 : Fin (m+2))))
    (processStarLaw_permutation μ hμ p)
  rw [Measure.map_map (measurable_coloredPhysicalEdgeCoordinates _) (measurable_coloredPhysicalStarPermutation p)] at h
  have hf : coloredPhysicalEdgeCoordinates (r := r) (0 : Fin (m+2)) ∘
      coloredPhysicalStarPermutation p=coloredPhysicalEdgeCoordinates i := by
    funext z ⟨b,a⟩
    cases b
    · rfl
    · change z (a,(p 0).succ)=z (a,i.succ)
      rw [show p 0=i by exact Equiv.swap_apply_left 0 i]
  rw [hf] at h
  exact h

end GaussianWave.BS
