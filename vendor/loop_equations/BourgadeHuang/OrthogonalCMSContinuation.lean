import BourgadeHuang.OrthogonalCMSCoordinates
import BourgadeHuang.EntireRatioCMS

/-! Analytic continuation of the actual beta-one CMS system to every numerator
sign and to real numerator values. Only the chosen denominator square-root
branches and genuine coordinate noncollisions remain as domain conditions. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem expectedOrthogonalRatioFunction_CMS_paired {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .one)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (hfree : CMS.CollisionFree (Fin.append u (Fin.append v w)))
    (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) :
    ∀ i, CMS.deformedOperator 1 (OrthogonalCMS.charges q) i
      (expectedOrthogonalRatioFunction ν) (Fin.append u (Fin.append v w)) = 0 := by
  have hf := (CMS.collisionFree_append u (Fin.append v w)).mp hfree
  have hd := (CMS.collisionFree_append v w).mp hf.2.1
  have hcV : CMS.CrossDistinct u v := by
    intro i j
    simpa only [Fin.append_left] using hf.2.2 i (Fin.castAdd q j)
  have hcW : CMS.CrossDistinct u w := by
    intro i j
    simpa only [Fin.append_right] using hf.2.2 i (Fin.natAdd q j)
  intro i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · change CMS.deformedOperator 1 (OrthogonalCMS.charges q) (OrthogonalCMS.numeratorIndex i)
      (OrthogonalCMS.blockFunction (expectedOrthogonalCharacteristicRatios ν)) _ = _
    rw [OrthogonalCMS.deformedOperator_numerator]
    exact expectedOrthogonalCharacteristicRatios_numerator_CMS ν hh ha he u v w huv hwv hf.1 hcV hcW i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · change CMS.deformedOperator 1 (OrthogonalCMS.charges q) (OrthogonalCMS.firstDenominatorIndex i)
        (OrthogonalCMS.blockFunction (expectedOrthogonalCharacteristicRatios ν)) _ = _
      rw [OrthogonalCMS.deformedOperator_firstDenominator]
      exact expectedOrthogonalCharacteristicRatios_firstDenominator_CMS ν hh ha he u v w huv hwv hd.1 hcV hd.2.2 i
    · change CMS.deformedOperator 1 (OrthogonalCMS.charges q) (OrthogonalCMS.secondDenominatorIndex i)
        (OrthogonalCMS.blockFunction (expectedOrthogonalCharacteristicRatios ν)) _ = _
      rw [OrthogonalCMS.deformedOperator_secondDenominator]
      exact expectedOrthogonalCharacteristicRatios_secondDenominator_CMS ν hh ha he u v w huv hwv hd.2.1 hcW
        (fun i j => (hd.2.2 j i).symm) i

/-- A paired numerator tuple can be chosen away from all of the twice-as-many
orthogonal denominator coordinates, with a whole collision-free neighborhood. -/
theorem exists_orthogonal_paired_collisionFree_numerators {q : ℕ} (v w : Fin q → ℂ)
    (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) (hd : Function.Injective (Fin.append v w)) :
    ∃ u : Fin q → ℂ, (∀ j, SameOpenHalfPlane (u j) (v j)) ∧
      CMS.CollisionFree (Fin.append u (Fin.append v w)) := by
  have hoff : ∀ j, (Fin.append v w j).im ≠ 0 := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Fin.append_left] using (hwv i).right_offReal
    · simpa only [Fin.append_right] using (hwv i).left_offReal
  obtain ⟨U,hU,hfree⟩ := exists_paired_collisionFree_numerators (Fin.append v w) hoff hd
  have hf := (CMS.collisionFree_append U (Fin.append v w)).mp hfree
  let u : Fin q → ℂ := fun j => U (Fin.castAdd q j)
  refine ⟨u,fun j => ?_,(CMS.collisionFree_append u (Fin.append v w)).mpr ⟨?_,hd,?_⟩⟩
  · simpa only [u,Fin.append_left] using hU (Fin.castAdd q j)
  · exact hf.1.comp (Fin.castAdd_injective q q)
  · exact fun i j => hf.2.2 (Fin.castAdd q i) j

/-- The hierarchy forces the full deformed CMS equations at arbitrary complex
numerators, including points in the opposite half-plane or on the real line. -/
theorem expectedOrthogonalRatioFunction_CMS {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .one)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (hfree : CMS.CollisionFree (Fin.append u (Fin.append v w)))
    (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) :
    ∀ i, CMS.deformedOperator 1 (OrthogonalCMS.charges q) i
      (expectedOrthogonalRatioFunction ν) (Fin.append u (Fin.append v w)) = 0 := by
  obtain ⟨u₀,hpair,hfree₀⟩ := exists_orthogonal_paired_collisionFree_numerators v w hwv
    ((CMS.collisionFree_append u (Fin.append v w)).mp hfree).2.1
  have hf (t : CMS.Point q) : AnalyticAt ℂ (expectedOrthogonalRatioFunction ν)
      (Fin.append t (Fin.append v w)) :=
    analyticAt_expectedOrthogonalRatioFunction ν ha he _ (fun j => by
      simpa only [OrthogonalCMS.firstDenominatorIndex,OrthogonalCMS.secondDenominatorIndex,
        Fin.append_left,Fin.append_right] using hwv j)
  have hlocal : ∀ᶠ t in nhds u₀, CMS.CollisionFree (Fin.append t (Fin.append v w)) ∧
      ∀i, CMS.deformedOperator 1 (OrthogonalCMS.charges q) i
        (expectedOrthogonalRatioFunction ν) (Fin.append t (Fin.append v w)) = 0 := by
    have hcont := (CMS.analyticAt_append_left (Fin.append v w) u₀).continuousAt.tendsto
    have hp : ∀ᶠ t in nhds u₀, ∀j,SameOpenHalfPlane (t j) (v j) := by
      apply Filter.eventually_all.mpr
      intro j
      exact (continuous_apply j).continuousAt.eventually (sameOpenHalfPlane_nhds (hpair j))
    filter_upwards [hcont.eventually (eventually_collisionFree hfree₀),hp] with t ht htp
    exact ⟨ht,expectedOrthogonalRatioFunction_CMS_paired ν hh ha he t v w ht htp hwv⟩
  exact CMS.deformedOperator_eq_zero_of_local_numerator 1 (OrthogonalCMS.charges q)
    (expectedOrthogonalRatioFunction ν) (Fin.append v w) hf u₀ hlocal u hfree

/-- All three original blocks inherit the continuation, with no numerator
half-plane hypotheses left in the statement. -/
theorem expectedOrthogonalCharacteristicRatios_CMS_all_numerators {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .one)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (hfree : CMS.CollisionFree (Fin.append u (Fin.append v w)))
    (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) :
    (∀i,OrthogonalCMS.numeratorOperator i (expectedOrthogonalCharacteristicRatios ν) u v w = 0) ∧
    (∀i,OrthogonalCMS.firstDenominatorOperator i (expectedOrthogonalCharacteristicRatios ν) u v w = 0) ∧
    (∀i,OrthogonalCMS.secondDenominatorOperator i (expectedOrthogonalCharacteristicRatios ν) u v w = 0) := by
  have h := expectedOrthogonalRatioFunction_CMS ν hh ha he u v w hfree hwv
  refine ⟨fun i => ?_,fun i => ?_,fun i => ?_⟩
  · simpa only [expectedOrthogonalRatioFunction,OrthogonalCMS.deformedOperator_numerator] using h (OrthogonalCMS.numeratorIndex i)
  · simpa only [expectedOrthogonalRatioFunction,OrthogonalCMS.deformedOperator_firstDenominator] using h (OrthogonalCMS.firstDenominatorIndex i)
  · simpa only [expectedOrthogonalRatioFunction,OrthogonalCMS.deformedOperator_secondDenominator] using h (OrthogonalCMS.secondDenominatorIndex i)

end BourgadeHuang
