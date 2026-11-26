import BourgadeHuang.EntireRatioExpectation
import BourgadeHuang.CMS.OriginalContinuation

/-! The actual entire numerator extension satisfies the original CMS equations
for every collision-free tuple with off-real denominators. -/
noncomputable section
open scoped Topology BigOperators
open MeasureTheory Filter
namespace BourgadeHuang

lemma eventually_pairedSameHalf {q : ℕ} {z : CMS.Point (q+q)}
    (hz : ∀ j, SameOpenHalfPlane (z (Fin.castAdd q j)) (z (Fin.natAdd q j))) :
    ∀ᶠ w in nhds z, ∀ j, SameOpenHalfPlane (w (Fin.castAdd q j)) (w (Fin.natAdd q j)) := by
  apply Filter.eventually_all.mpr
  intro j
  have hl : Continuous (fun w : CMS.Point (q+q) => (w (Fin.castAdd q j)).im) :=
    Complex.continuous_im.comp (continuous_apply _)
  have hr : Continuous (fun w : CMS.Point (q+q) => (w (Fin.natAdd q j)).im) :=
    Complex.continuous_im.comp (continuous_apply _)
  have ho : IsOpen {w : CMS.Point (q+q) |
      SameOpenHalfPlane (w (Fin.castAdd q j)) (w (Fin.natAdd q j))} :=
    ((isOpen_lt continuous_const hl).inter (isOpen_lt continuous_const hr)).union
      ((isOpen_lt hl continuous_const).inter (isOpen_lt hr continuous_const))
  exact ho.mem_nhds (hz j)

lemma eventually_collisionFree {d : ℕ} {z : CMS.Point d} (hz : CMS.CollisionFree z) :
    ∀ᶠ w in nhds z, CMS.CollisionFree w := by
  have hpair (i j : Fin d) : ∀ᶠ w in nhds z, i ≠ j → w i ≠ w j := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (by simp [hij])
    · have hn : ∀ᶠ w : CMS.Point d in nhds z, w i ≠ w j :=
        (isOpen_ne_fun (continuous_apply i) (continuous_apply j)).mem_nhds (fun he => hij (hz he))
      exact hn.mono (fun _ hw _ => hw)
  filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hpair i))] with w hw
  intro i j he
  exact Classical.not_not.mp (fun hne => hw i j hne he)

theorem expectedEntireRatioFunction_eventuallyEq {q : ℕ}
    (ν : Measure AnchoredCountingState) {z : CMS.Point (q+q)}
    (hz : ∀ j, SameOpenHalfPlane (z (Fin.castAdd q j)) (z (Fin.natAdd q j))) :
    expectedEntireRatioFunction ν =ᶠ[nhds z] expectedRatioFunction ν := by
  filter_upwards [eventually_pairedSameHalf hz] with w hw
  exact expectedEntireCharacteristicRatios_eq ν _ _ hw

theorem expectedEntireRatioFunction_solvesOriginalAt_paired {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .two)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : CMS.Point q) (hfree : CMS.CollisionFree (Fin.append u v))
    (huv : ∀ j, SameOpenHalfPlane (u j) (v j)) :
    CMS.SolvesOriginalAt (n := q) (m := q) (expectedEntireRatioFunction ν) (Fin.append u v) := by
  have hz : ∀ j, SameOpenHalfPlane (Fin.append u v (Fin.castAdd q j))
      (Fin.append u v (Fin.natAdd q j)) := by
    simpa only [Fin.append_left,Fin.append_right] using huv
  exact CMS.solvesOriginalAt_congr_nhds u v hfree
    (expectedEntireRatioFunction_eventuallyEq ν hz).symm
    (expectedRatioFunction_solvesOriginalAt ν hh ha he _ hfree hz)

/-- Explicit numerator real parts beyond all denominator real parts provide a
nonempty paired neighborhood with every collision excluded. -/
theorem exists_paired_collisionFree_numerators {q : ℕ} (v : CMS.Point q)
    (hv : ∀ j, (v j).im ≠ 0) (hinj : Function.Injective v) :
    ∃ u : CMS.Point q, (∀ j, SameOpenHalfPlane (u j) (v j)) ∧
      CMS.CollisionFree (Fin.append u v) := by
  let A : ℝ := 1+∑ j, |(v j).re|
  let u : CMS.Point q := fun j => (A+j.val : ℝ)+Complex.I*(if 0 < (v j).im then 1 else -1)
  have hure (j : Fin q) : (u j).re = A+j.val := by
    dsimp [u]
    split_ifs <;> simp
  have hpair (j : Fin q) : SameOpenHalfPlane (u j) (v j) := by
    by_cases hp : 0 < (v j).im
    · exact Or.inl ⟨by simp [u,hp],hp⟩
    · have hn : (v j).im < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hv j)
      exact Or.inr ⟨by simp [u,hp],hn⟩
  have hui : Function.Injective u := by
    intro i j he
    have hr := congrArg Complex.re he
    rw [hure,hure,add_right_inj] at hr
    exact Fin.ext (by exact_mod_cast hr)
  have hc : CMS.CrossDistinct u v := by
    intro i j he
    have hsum : |(v j).re| ≤ ∑ k, |(v k).re| :=
      Finset.single_le_sum (f := fun k : Fin q => |(v k).re|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    have hr := congrArg Complex.re he
    rw [hure] at hr
    have hn : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
    dsimp [A] at hr
    linarith [le_abs_self (v j).re]
  exact ⟨u,hpair,(CMS.collisionFree_append u v).mpr ⟨hui,hinj,hc⟩⟩

/-- The hierarchy forces the original CMS PDE at arbitrary numerator points;
only the denominator coordinates must remain off the real axis. -/
theorem expectedEntireRatioFunction_solvesOriginalAt {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .two)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (z : CMS.Point (q+q)) (hfree : CMS.CollisionFree z)
    (hv : ∀ j, (z (Fin.natAdd q j)).im ≠ 0) :
    CMS.SolvesOriginalAt (n := q) (m := q) (expectedEntireRatioFunction ν) z := by
  let u : CMS.Point q := fun j => z (Fin.castAdd q j)
  let v : CMS.Point q := fun j => z (Fin.natAdd q j)
  have happ : Fin.append u v = z := Fin.append_castAdd_natAdd
  have hfree' : CMS.CollisionFree (Fin.append u v) := happ ▸ hfree
  obtain ⟨u₀,hpair,hfree₀⟩ := exists_paired_collisionFree_numerators v hv
    ((CMS.collisionFree_append u v).mp hfree').2.1
  have hf (t : CMS.Point q) : AnalyticAt ℂ (expectedEntireRatioFunction ν) (Fin.append t v) :=
    analyticAt_expectedEntireRatioFunction ν ha he _
      (fun j => by simpa only [Fin.append_right] using hv j)
  have hlocal : ∀ᶠ t in nhds u₀, CMS.CollisionFree (Fin.append t v) ∧
      CMS.SolvesOriginalAt (n := q) (m := q) (expectedEntireRatioFunction ν) (Fin.append t v) := by
    have hcont := (CMS.analyticAt_append_left v u₀).continuousAt.tendsto
    have hp₀ : ∀ j, SameOpenHalfPlane (Fin.append u₀ v (Fin.castAdd q j))
        (Fin.append u₀ v (Fin.natAdd q j)) := by
      simpa only [Fin.append_left,Fin.append_right] using hpair
    filter_upwards [hcont.eventually (eventually_collisionFree hfree₀),
      hcont.eventually (eventually_pairedSameHalf hp₀)] with t ht hp
    refine ⟨ht,expectedEntireRatioFunction_solvesOriginalAt_paired ν hh ha he t v ht ?_⟩
    simpa only [Fin.append_left,Fin.append_right] using hp
  have hs := CMS.solvesOriginalAt_of_local_numerator (expectedEntireRatioFunction ν) v hf u₀ hlocal u hfree'
  simpa only [happ] using hs

/-- The denominator indices in the combined CMS coordinate vector. -/
def ratioDenominatorIndices (q : ℕ) : Finset (Fin (q+q)) :=
  Finset.univ.image (Fin.natAdd q)

@[simp] theorem mem_ratioDenominatorIndices (q : ℕ) (j : Fin q) :
    Fin.natAdd q j ∈ ratioDenominatorIndices q :=
  Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩

/-- The actual expected ratios have the unique original CMS expansion on each
ordered chamber with independently chosen denominator half-planes. -/
theorem existsUnique_expectedEntireRatio_expansion {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .two)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (σ : Fin (q+q) → CMS.Sign) :
    ∃! c : (Fin (q+q) → CMS.Sign) → ℂ,
      Set.EqOn (expectedEntireRatioFunction ν)
        (fun z => ∑ τ, c τ*CMS.originalBranch (n := q) (m := q) τ z)
        (CMS.OrderedMixedDomain (q+q) (ratioDenominatorIndices q) σ) := by
  have hoff (z : CMS.Point (q+q))
      (hz : z ∈ CMS.OrderedMixedDomain (q+q) (ratioDenominatorIndices q) σ)
      (j : Fin q) : (z (Fin.natAdd q j)).im ≠ 0 := by
    have hj := hz.2 _ (mem_ratioDenominatorIndices q j)
    cases hs : σ (Fin.natAdd q j) <;> simp only [hs,Bool.false_eq_true,↓reduceIte] at hj
    · exact ne_of_lt hj
    · exact ne_of_gt hj
  apply CMS.existsUnique_original_expansion_orderedMixed (ratioDenominatorIndices q) σ
  · intro z hz
    exact analyticAt_expectedEntireRatioFunction ν ha he z (hoff z hz)
  · intro z hz
    exact expectedEntireRatioFunction_solvesOriginalAt ν hh ha he z
      (CMS.orderedMixedDomain_collisionFree hz) (hoff z hz)

end BourgadeHuang
