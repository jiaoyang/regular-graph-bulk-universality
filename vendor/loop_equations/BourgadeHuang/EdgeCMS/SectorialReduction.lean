import BourgadeHuang.EdgeCMS.WordDifferentiation

/-! Explicit sectorial differential data and actual repeated-coordinate
reduction, with finite constructed Leibniz terms. -/
noncomputable section
open scoped BigOperators
open Set
namespace BourgadeHuang.EdgeCMS
open CMS
open Coefficient

structure SectorialData {d : ℕ} (C : OpenCone d) where
  phase : Fin d → ℂ
  first : Fin d → Fin d → Coefficient C
  scalar : Fin d → Coefficient C
  first_homogeneous : ∀i j,(first i j).Homogeneous 1
  scalar_homogeneous : ∀i,(scalar i).Homogeneous 2

namespace SectorialData

def operator {d : ℕ} {C : OpenCone d} (D : SectorialData C) (i : Fin d) (f : Point d → ℂ) (z : Point d) : ℂ :=
  secondPartial i f z+D.phase i*coordDeriv i f z+
    (∑j,(D.first i j).eval z*coordDeriv j f z)+(D.scalar i).eval z*f z

def IsSolution {d : ℕ} {C : OpenCone d} (D : SectorialData C) (f : Point d → ℂ) : Prop :=
  AnalyticOnNhd ℂ f C.carrier ∧ ∀z∈C.carrier,∀i,D.operator i f z=0

/-- The nonprincipal part of one sectorial row, represented by an actual finite
list of homogeneous inverse-gap expressions and derivative words. -/
def remainderTerms {d : ℕ} {C : OpenCone d} (D : SectorialData C) (i : Fin d) : List (LeibnizTerm C) :=
  finTerms d (fun j => [(D.first i j,[j])])++[(D.scalar i,[])]

theorem termSum_remainderTerms {d : ℕ} {C : OpenCone d} (D : SectorialData C) (i : Fin d)
    (f : Point d → ℂ) (z : Point d) :
    termSum (D.remainderTerms i) f z=
      (∑j,(D.first i j).eval z*coordDeriv j f z)+(D.scalar i).eval z*f z := by
  simp only [remainderTerms,termSum_append,termSum_finTerms,termSum,wordDerivative,add_zero]

theorem secondPartial_eq_remainder {d : ℕ} {C : OpenCone d} {D : SectorialData C} {f : Point d → ℂ}
    (hf : D.IsSolution f) (i : Fin d) :
    EqOn (secondPartial i f)
      (fun z => -(D.phase i)*coordDeriv i f z-termSum (D.remainderTerms i) f z) C.carrier := by
  intro z hz
  have h := hf.2 z hz i
  dsimp only
  rw [termSum_remainderTerms]
  unfold operator at h
  linear_combination h

/-- Every differentiated row has a constructed finite Leibniz expansion; no
independent jet or differentiation hypothesis is used. -/
theorem wordDerivative_secondPartial_eq {d : ℕ} {C : OpenCone d} {D : SectorialData C} {f : Point d → ℂ}
    (hf : D.IsSolution f) (i : Fin d) (u : List (Fin d)) :
    EqOn (wordDerivative u (secondPartial i f))
      (fun z => -(D.phase i)*wordDerivative u (coordDeriv i f) z-
        termSum (expandTerms u (D.remainderTerms i)) f z) C.carrier := by
  intro z hz
  dsimp only
  rw [wordDerivative_congr u C.isOpen (secondPartial_eq_remainder hf i) hz]
  have h1 : AnalyticOnNhd ℂ (fun z => -(D.phase i)*coordDeriv i f z) C.carrier :=
    analyticOnNhd_const.mul (analyticOnNhd_coordDeriv hf.1 i)
  have h2 : AnalyticOnNhd ℂ (fun z => -(termSum (D.remainderTerms i) f z)) C.carrier :=
    fun z hz => (analyticAt_termSum _ (hf.1 z hz) hz).neg
  change wordDerivative u ((fun z => -(D.phase i)*coordDeriv i f z)+
    (fun z => -(termSum (D.remainderTerms i) f z))) z=_
  rw [wordDerivative_add u C.isOpen h1 h2 hz]
  change wordDerivative u (fun z => -(D.phase i)*coordDeriv i f z) z+
    wordDerivative u (fun z => -(termSum (D.remainderTerms i) f z)) z=_
  rw [wordDerivative_const_mul u _ C.isOpen (analyticOnNhd_coordDeriv hf.1 i) hz]
  have hneg := wordDerivative_const_mul u (-1:ℂ) C.isOpen
    (fun z hz => analyticAt_termSum (D.remainderTerms i) (hf.1 z hz) hz) hz
  simp only [neg_one_mul] at hneg
  rw [hneg,wordDerivative_termSum u _ C.isOpen
    (fun _ hz => hz) hf.1 hz]
  ring

/-- One repeated-coordinate word is reduced using the actual PDE after moving
the repeated pair together by analytic mixed-derivative symmetry. -/
theorem wordDerivative_extra_eq {d : ℕ} {C : OpenCone d} {D : SectorialData C} {f : Point d → ℂ}
    (hf : D.IsSolution f) (i : Fin d) (u : List (Fin d)) (hi : i∈u) :
    EqOn (wordDerivative (i::u) f)
      (fun z => -(D.phase i)*wordDerivative u f z-
        termSum (expandTerms (u.erase i) (D.remainderTerms i)) f z) C.carrier := by
  have hp : (i::u).Perm (u.erase i++[i,i]) := by
    apply (List.Perm.cons i (List.perm_cons_erase hi)).trans
    simpa only [List.cons_append,List.nil_append] using (List.perm_append_comm : ([i,i]++u.erase i).Perm (u.erase i++[i,i]))
  have hq : u.Perm (u.erase i++[i]) :=
    (List.perm_cons_erase hi).trans (by simpa using (List.perm_append_comm : ([i]++u.erase i).Perm (u.erase i++[i])))
  intro z hz
  rw [wordDerivative_perm hp C.isOpen hf.1 hz,wordDerivative_append]
  change wordDerivative (u.erase i) (secondPartial i f) z=_
  rw [wordDerivative_secondPartial_eq hf i (u.erase i) hz]
  have hh := wordDerivative_perm hq C.isOpen hf.1 hz
  rw [wordDerivative_append] at hh
  change wordDerivative u f z=wordDerivative (u.erase i) (coordDeriv i f) z at hh
  dsimp only
  rw [← hh]

end SectorialData
end BourgadeHuang.EdgeCMS
