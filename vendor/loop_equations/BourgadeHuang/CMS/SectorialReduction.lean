import BourgadeHuang.CMS.WordDifferentiation

/-! Explicit sectorial differential data and actual repeated-coordinate
reduction, with finite constructed Leibniz terms. -/
noncomputable section
open scoped BigOperators
open Set
namespace BourgadeHuang.CMS
open GapExpression

structure SectorialData (d : ℕ) where
  phase : Fin d → ℂ
  first : Fin d → Fin d → GapExpression d
  scalar : Fin d → GapExpression d
  first_homogeneous : ∀i j,(first i j).Homogeneous 1
  scalar_homogeneous : ∀i,(scalar i).Homogeneous 2

namespace SectorialData

def operator {d : ℕ} (D : SectorialData d) (i : Fin d) (f : Point d → ℂ) (z : Point d) : ℂ :=
  secondPartial i f z+D.phase i*coordDeriv i f z+
    (∑j,(D.first i j).eval z*coordDeriv j f z)+(D.scalar i).eval z*f z

def IsSolution {d : ℕ} (D : SectorialData d) (f : Point d → ℂ) : Prop :=
  AnalyticOnNhd ℂ f (OrderedDomain d) ∧ ∀z∈OrderedDomain d,∀i,D.operator i f z=0

def general {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign) : SectorialData d where
  phase i := 2*Complex.I*c i*signValue (σ i)
  first := sectorialFirstExpression β c σ
  scalar := branchPotentialExpression β c σ
  first_homogeneous := homogeneous_sectorialFirstExpression β c σ
  scalar_homogeneous := homogeneous_branchPotentialExpression β c σ

theorem operator_general {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i : Fin d) (f : Point d → ℂ) {z : Point d} (hz : z∈OrderedDomain d) :
    (general β c σ).operator i f z=sectorialOperator β c σ i f z := by
  simp only [operator,general,eval_sectorialFirstExpression,
    eval_branchPotentialExpression β c σ i (orderedDomain_collisionFree hz)]
  exact (sectorialOperator_eq_firstCoefficients β c σ i f z).symm

theorem isSolution_general_iff {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f (OrderedDomain d)) :
    (general β c σ).IsSolution f ↔
      ∀z∈OrderedDomain d,∀i,
        deformedOperator β c i (fun w => generalBranch β c σ w*f w) z=0 := by
  constructor
  · intro h z hz i
    rw [deformedOperator_generalBranch_mul_eq_zero_iff β c σ hz (hf z hz),
      ← operator_general β c σ i f hz]
    exact h.2 z hz i
  · intro h
    refine ⟨hf,?_⟩
    intro z hz i
    rw [operator_general β c σ i f hz]
    exact (deformedOperator_generalBranch_mul_eq_zero_iff β c σ hz (hf z hz) i).mp (h z hz i)

/-- The nonprincipal part of one sectorial row, represented by an actual finite
list of homogeneous inverse-gap expressions and derivative words. -/
def remainderTerms {d : ℕ} (D : SectorialData d) (i : Fin d) : List (LeibnizTerm d) :=
  finTerms d (fun j => [(D.first i j,[j])])++[(D.scalar i,[])]

theorem termSum_remainderTerms {d : ℕ} (D : SectorialData d) (i : Fin d)
    (f : Point d → ℂ) (z : Point d) :
    termSum (D.remainderTerms i) f z=
      (∑j,(D.first i j).eval z*coordDeriv j f z)+(D.scalar i).eval z*f z := by
  simp only [remainderTerms,termSum_append,termSum_finTerms,termSum,wordDerivative,add_zero]

theorem secondPartial_eq_remainder {d : ℕ} {D : SectorialData d} {f : Point d → ℂ}
    (hf : D.IsSolution f) (i : Fin d) :
    EqOn (secondPartial i f)
      (fun z => -(D.phase i)*coordDeriv i f z-termSum (D.remainderTerms i) f z) (OrderedDomain d) := by
  intro z hz
  have h := hf.2 z hz i
  dsimp only
  rw [termSum_remainderTerms]
  unfold operator at h
  linear_combination h

/-- Every differentiated row has a constructed finite Leibniz expansion; no
independent jet or differentiation hypothesis is used. -/
theorem wordDerivative_secondPartial_eq {d : ℕ} {D : SectorialData d} {f : Point d → ℂ}
    (hf : D.IsSolution f) (i : Fin d) (u : List (Fin d)) :
    EqOn (wordDerivative u (secondPartial i f))
      (fun z => -(D.phase i)*wordDerivative u (coordDeriv i f) z-
        termSum (expandTerms u (D.remainderTerms i)) f z) (OrderedDomain d) := by
  intro z hz
  dsimp only
  rw [wordDerivative_congr u (orderedDomain_isOpen d) (secondPartial_eq_remainder hf i) hz]
  have h1 : AnalyticOnNhd ℂ (fun z => -(D.phase i)*coordDeriv i f z) (OrderedDomain d) :=
    analyticOnNhd_const.mul (analyticOnNhd_coordDeriv hf.1 i)
  have h2 : AnalyticOnNhd ℂ (fun z => -(termSum (D.remainderTerms i) f z)) (OrderedDomain d) :=
    fun z hz => (analyticAt_termSum _ (hf.1 z hz) (orderedDomain_collisionFree hz)).neg
  change wordDerivative u ((fun z => -(D.phase i)*coordDeriv i f z)+
    (fun z => -(termSum (D.remainderTerms i) f z))) z=_
  rw [wordDerivative_add u (orderedDomain_isOpen d) h1 h2 hz]
  change wordDerivative u (fun z => -(D.phase i)*coordDeriv i f z) z+
    wordDerivative u (fun z => -(termSum (D.remainderTerms i) f z)) z=_
  rw [wordDerivative_const_mul u _ (orderedDomain_isOpen d) (analyticOnNhd_coordDeriv hf.1 i) hz]
  have hneg := wordDerivative_const_mul u (-1:ℂ) (orderedDomain_isOpen d)
    (fun z hz => analyticAt_termSum (D.remainderTerms i) (hf.1 z hz) (orderedDomain_collisionFree hz)) hz
  simp only [neg_one_mul] at hneg
  rw [hneg,wordDerivative_termSum u _ (orderedDomain_isOpen d)
    (fun _ hz => orderedDomain_collisionFree hz) hf.1 hz]
  ring

/-- One repeated-coordinate word is reduced using the actual PDE after moving
the repeated pair together by analytic mixed-derivative symmetry. -/
theorem wordDerivative_extra_eq {d : ℕ} {D : SectorialData d} {f : Point d → ℂ}
    (hf : D.IsSolution f) (i : Fin d) (u : List (Fin d)) (hi : i∈u) :
    EqOn (wordDerivative (i::u) f)
      (fun z => -(D.phase i)*wordDerivative u f z-
        termSum (expandTerms (u.erase i) (D.remainderTerms i)) f z) (OrderedDomain d) := by
  have hp : (i::u).Perm (u.erase i++[i,i]) := by
    apply (List.Perm.cons i (List.perm_cons_erase hi)).trans
    simpa only [List.cons_append,List.nil_append] using (List.perm_append_comm : ([i,i]++u.erase i).Perm (u.erase i++[i,i]))
  have hq : u.Perm (u.erase i++[i]) :=
    (List.perm_cons_erase hi).trans (by simpa using (List.perm_append_comm : ([i]++u.erase i).Perm (u.erase i++[i])))
  intro z hz
  rw [wordDerivative_perm hp (orderedDomain_isOpen d) hf.1 hz,wordDerivative_append]
  change wordDerivative (u.erase i) (secondPartial i f) z=_
  rw [wordDerivative_secondPartial_eq hf i (u.erase i) hz]
  have hh := wordDerivative_perm hq (orderedDomain_isOpen d) hf.1 hz
  rw [wordDerivative_append] at hh
  change wordDerivative u f z=wordDerivative (u.erase i) (coordDeriv i f) z at hh
  dsimp only
  rw [← hh]

end SectorialData
end BourgadeHuang.CMS
