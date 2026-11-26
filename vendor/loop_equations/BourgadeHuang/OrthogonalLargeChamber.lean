import BourgadeHuang.OrthogonalCMSContinuation
import BourgadeHuang.CMS.OrderedGapMixedGeometry

/-! The actual orthogonal ratio expectation on the common type of large
ordered chamber. Analyticity and every deformed CMS equation follow from the
proved expectation and loop identities, including arbitrary numerator values. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace BourgadeHuang
namespace OrthogonalCMS

/-- Both orthogonal denominator blocks, with no numerator restriction. -/
def denominatorIndices (q : ℕ) : Finset (Fin (q+(q+q))) :=
  Finset.univ.image (Fin.natAdd q)

def chamberSigns {q : ℕ} (η : Fin q → CMS.Sign) : Fin (q+(q+q)) → CMS.Sign :=
  Fin.append (fun _=>false) (Fin.append η η)

def largeChamber {q : ℕ} (R : ℝ) (η : Fin q → CMS.Sign) : Set (CMS.Point (q+(q+q))) :=
  CMS.OrderedGapMixedDomain (q+(q+q)) R (denominatorIndices q) (chamberSigns η)

@[simp] theorem firstDenominatorIndex_mem (q : ℕ) (j : Fin q) :
    firstDenominatorIndex j∈denominatorIndices q :=
  Finset.mem_image.mpr ⟨Fin.castAdd q j,Finset.mem_univ _,rfl⟩

@[simp] theorem secondDenominatorIndex_mem (q : ℕ) (j : Fin q) :
    secondDenominatorIndex j∈denominatorIndices q :=
  Finset.mem_image.mpr ⟨Fin.natAdd q j,Finset.mem_univ _,rfl⟩

theorem largeChamber_paired {q : ℕ} {R : ℝ} {η : Fin q → CMS.Sign}
    {z : CMS.Point (q+(q+q))} (hz : z∈largeChamber R η) (j : Fin q) :
    SameOpenHalfPlane (z (secondDenominatorIndex j)) (z (firstDenominatorIndex j)) := by
  have h1 := hz.2 _ (firstDenominatorIndex_mem q j)
  have h2 := hz.2 _ (secondDenominatorIndex_mem q j)
  simp only [chamberSigns,firstDenominatorIndex,secondDenominatorIndex,
    Fin.append_left,Fin.append_right] at h1 h2
  cases hs : η j <;> simp only [hs,Bool.false_eq_true,↓reduceIte] at h1 h2
  · exact Or.inr ⟨h2,h1⟩
  · exact Or.inl ⟨h2,h1⟩

theorem charges_physical (q : ℕ) :
    ∀i,charges q i= -1 ∨ charges q i=(1:ℂ)/2 := by
  intro i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · exact Or.inl (by simp only [charges,Fin.append_left,Fin.append_right])
  · refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;> exact Or.inr (by simp only [charges,Fin.append_left,Fin.append_right])

/-- Reconstructing a tuple from the three genuine block projections. -/
theorem append_projections {q : ℕ} (z : CMS.Point (q+(q+q))) :
    Fin.append (fun j=>z (numeratorIndex j))
      (Fin.append (fun j=>z (firstDenominatorIndex j)) (fun j=>z (secondDenominatorIndex j)))=z := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [numeratorIndex,Fin.append_left]
  · refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;>
      simp only [firstDenominatorIndex,secondDenominatorIndex,Fin.append_left,Fin.append_right]

end OrthogonalCMS

/-- All hypotheses of the analytic deformed solution space are discharged
for the actual expected fractional-denominator ratio on each large chamber. -/
theorem expectedOrthogonalRatioFunction_largeChamber_solution {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .one)
    {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    {R : ℝ} (hR : 0≤R) (η : Fin q → CMS.Sign) :
    AnalyticOnNhd ℂ (expectedOrthogonalRatioFunction ν) (OrthogonalCMS.largeChamber R η) ∧
      ∀z∈OrthogonalCMS.largeChamber R η,∀i,
        CMS.deformedOperator 1 (OrthogonalCMS.charges q) i (expectedOrthogonalRatioFunction ν) z=0 := by
  constructor
  · intro z hz
    exact analyticAt_expectedOrthogonalRatioFunction ν ha he z (OrthogonalCMS.largeChamber_paired hz)
  · intro z hz i
    have hpair := OrthogonalCMS.largeChamber_paired hz
    have hfree : CMS.CollisionFree z := CMS.orderedGapMixedDomain_collisionFree hR hz
    have happ := OrthogonalCMS.append_projections z
    have h := expectedOrthogonalRatioFunction_CMS ν hh ha he
      (fun j=>z (OrthogonalCMS.numeratorIndex j))
      (fun j=>z (OrthogonalCMS.firstDenominatorIndex j))
      (fun j=>z (OrthogonalCMS.secondDenominatorIndex j))
      (by simpa only [happ] using hfree) hpair i
    simpa only [happ] using h

end BourgadeHuang
