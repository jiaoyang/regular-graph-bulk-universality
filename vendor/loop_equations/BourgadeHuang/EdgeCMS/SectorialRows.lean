import BourgadeHuang.EdgeCMS.SectorialNormalForm
import BourgadeHuang.CMS.SectorialRows

/-! Constructed square-free equations for analytic homogeneous systems. -/
noncomputable section
open scoped BigOperators Topology
open Set
namespace BourgadeHuang.EdgeCMS
open CMS

theorem wordDerivative_eq_squareFreeDerivative_cone {d : ℕ} {C : OpenCone d}
    {v : List (Fin d)} (hv : v.Nodup) {f : Point d → ℂ}
    (hf : AnalyticOnNhd ℂ f C.carrier) :
    EqOn (wordDerivative v f) (squareFreeDerivative v.toFinset f) C.carrier :=
  wordDerivative_perm (List.toFinset_toList hv).symm C.isOpen hf

theorem coordDeriv_squareFreeDerivative_of_not_mem_cone {d : ℕ} {C : OpenCone d}
    (S : Finset (Fin d)) {i : Fin d} (hi : i ∉ S) {f : Point d → ℂ}
    (hf : AnalyticOnNhd ℂ f C.carrier) :
    EqOn (coordDeriv i (squareFreeDerivative S f)) (squareFreeDerivative (insert i S) f) C.carrier := by
  have hv : (i :: S.toList).Nodup := List.nodup_cons.mpr ⟨by simpa using hi, S.nodup_toList⟩
  have hh := wordDerivative_eq_squareFreeDerivative_cone hv hf
  simpa only [List.toFinset_cons, Finset.toList_toFinset, wordDerivative, squareFreeDerivative] using hh

/-- The coefficient includes its proved inverse-gap degree. -/
structure SquareFreeTerm {d : ℕ} (C : OpenCone d) where
  coefficient : Coefficient C
  weight : ℕ
  target : Finset (Fin d)
  homogeneous : coefficient.Homogeneous weight

namespace SquareFreeTerm

def evalSum {d : ℕ} {C : OpenCone d} (ts : List (SquareFreeTerm C)) (f : Point d → ℂ) (z : Point d) : ℂ :=
  (ts.map (fun t => t.coefficient.eval z*squareFreeDerivative t.target f z)).sum

@[simp] theorem evalSum_nil {d : ℕ} {C : OpenCone d} (f : Point d → ℂ) (z : Point d) :
    evalSum ([] : List (SquareFreeTerm C)) f z=0 := rfl

@[simp] theorem evalSum_cons {d : ℕ} {C : OpenCone d} (t : SquareFreeTerm C) (ts : List (SquareFreeTerm C))
    (f : Point d → ℂ) (z : Point d) : evalSum (t::ts) f z=
      t.coefficient.eval z*squareFreeDerivative t.target f z+evalSum ts f z := rfl


/-- The explicit differential-operator representation of a subset-indexed row. -/
def asTerms {d : ℕ} {C : OpenCone d} (ts : List (SquareFreeTerm C)) : List (Coefficient.LeibnizTerm C) :=
  ts.map (fun a => (a.coefficient,a.target.toList))

theorem termSum_asTerms {d : ℕ} {C : OpenCone d} (ts : List (SquareFreeTerm C))
    (f : Point d → ℂ) (z : Point d) :
    Coefficient.termSum (asTerms ts) f z=evalSum ts f z := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [asTerms,List.map_cons,Coefficient.termSum,evalSum_cons] at ih ⊢; rw [ih]; rfl

def IsCorrection {d : ℕ} {C : OpenCone d} (n : ℕ) (t : SquareFreeTerm C) : Prop :=
  1≤t.weight ∧ ((t.weight+t.target.card=n ∧ t.target.Nonempty) ∨ t.weight+t.target.card=n+1)

theorem IsCorrection.target_card_le {d n : ℕ} {C : OpenCone d} {t : SquareFreeTerm C}
    (ht : t.IsCorrection n) : t.target.card≤n := by obtain ⟨h,h'⟩ := ht; omega

theorem IsCorrection.target_card_lt_of_low {d n : ℕ} {C : OpenCone d} {t : SquareFreeTerm C}
    (ht : t.IsCorrection n) (hl : t.weight+t.target.card=n) : t.target.card<n := by
  obtain ⟨h,_⟩ := ht
  omega

end SquareFreeTerm

namespace SectorialData
open Coefficient

private theorem package_corrections {d n : ℕ} {C : OpenCone d} (ts : List (LeibnizTerm C))
    (hts : ∀a v,(a,v)∈ts→CorrectionTerm n a v) :
    ∃us : List (SquareFreeTerm C),(∀t∈us,t.IsCorrection n) ∧
      ∀f,AnalyticOnNhd ℂ f C.carrier→
        EqOn (termSum ts f) (SquareFreeTerm.evalSum us f) C.carrier := by
  induction ts with
  | nil => exact ⟨[],by simp,fun _ _ _ _ => rfl⟩
  | cons t ts ih =>
    rcases t with ⟨a,v⟩
    obtain ⟨hv,q,hq,hpos,hdeg⟩ := hts a v (List.mem_cons_self ..)
    obtain ⟨us,hus,heq⟩ := ih (fun a v hm => hts a v (List.mem_cons_of_mem _ hm))
    let t : SquareFreeTerm C := ⟨a,q,v.toFinset,hq⟩
    have ht : t.IsCorrection n := by
      change 1≤q ∧ ((q+v.toFinset.card=n ∧ v.toFinset.Nonempty) ∨ q+v.toFinset.card=n+1)
      simpa only [← Finset.card_pos,List.toFinset_card_of_nodup hv,List.ne_nil_iff_length_pos] using And.intro hpos hdeg
    refine ⟨t::us,?_,?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl|hw
      · exact ht
      · exact hus w hw
    · intro f hf z hz
      change a.eval z*wordDerivative v f z+termSum ts f z=
        a.eval z*squareFreeDerivative v.toFinset f z+SquareFreeTerm.evalSum us f z
      rw [wordDerivative_eq_squareFreeDerivative_cone hv hf hz,heq f hf hz]

/-- The actual repeated-coordinate equation, with a finite subset-indexed row
and proved degrees of every coefficient. -/
theorem exists_squareFree_correction {d : ℕ} {C : OpenCone d} (D : SectorialData C)
    (S : Finset (Fin d)) (i : Fin d) (hi : i∈S) :
    ∃ts : List (SquareFreeTerm C),(∀t∈ts,t.IsCorrection S.card) ∧
      ∀f,D.IsSolution f→EqOn (coordDeriv i (squareFreeDerivative S f))
        (fun z => -(D.phase i)*squareFreeDerivative S f z-SquareFreeTerm.evalSum ts f z)
        C.carrier := by
  obtain ⟨ts,hts,heq⟩ := D.exists_repeated_normalForm S.toList S.nodup_toList i
    (by simpa using hi)
  obtain ⟨us,hus,hueq⟩ := package_corrections ts hts
  refine ⟨us,by simpa using hus,?_⟩
  intro f hf z hz
  have hh := heq f hf hz
  dsimp only at hh
  change coordDeriv i (squareFreeDerivative S f) z=
    -(D.phase i)*squareFreeDerivative S f z-termSum ts f z at hh
  dsimp only
  rw [hh,hueq f hf.1 hz]



/-- Chosen finite normal-form row, justified for every actual solution. -/
def correctionRow {d : ℕ} {C : OpenCone d} (D : SectorialData C) (S : Finset (Fin d)) (i : Fin d) :
    List (SquareFreeTerm C) :=
  if hi : i ∈ S then (D.exists_squareFree_correction S i hi).choose else []

theorem correctionRow_spec {d : ℕ} {C : OpenCone d} (D : SectorialData C) (S : Finset (Fin d)) (i : Fin d) :
    ∀ t ∈ D.correctionRow S i, t.IsCorrection S.card := by
  classical
  by_cases hi : i ∈ S
  · simpa only [correctionRow, dif_pos hi] using (D.exists_squareFree_correction S i hi).choose_spec.1
  · simp [correctionRow, hi]

theorem coordDeriv_squareFreeDerivative_of_mem {d : ℕ} {C : OpenCone d} (D : SectorialData C)
    (S : Finset (Fin d)) {i : Fin d} (hi : i∈S) {f : Point d → ℂ} (hf : D.IsSolution f) :
    EqOn (coordDeriv i (squareFreeDerivative S f))
      (fun z => -(D.phase i)*squareFreeDerivative S f z-
        SquareFreeTerm.evalSum (D.correctionRow S i) f z) C.carrier := by
  intro z hz
  simpa only [correctionRow, dif_pos hi] using
    (D.exists_squareFree_correction S i hi).choose_spec.2 f hf hz

end SectorialData

namespace SquareFreeTerm

/-- Matrix entries of a finite correction row. -/
def matrixEntry {d : ℕ} {C : OpenCone d} (ts : List (SquareFreeTerm C)) (T : Finset (Fin d)) (z : Point d) : ℂ :=
  (ts.map (fun t => if t.target=T then t.coefficient.eval z else 0)).sum

theorem evalSum_eq_matrix {d : ℕ} {C : OpenCone d} (ts : List (SquareFreeTerm C))
    (f : Point d → ℂ) (z : Point d) :
    evalSum ts f z=∑T : Finset (Fin d),matrixEntry ts T z*squareFreeDerivative T f z := by
  classical
  induction ts with
  | nil => simp [evalSum,matrixEntry]
  | cons t ts ih =>
    simp only [evalSum_cons,matrixEntry,List.map_cons,List.sum_cons,add_mul,
      Finset.sum_add_distrib]
    simp only [matrixEntry] at ih
    rw [← ih]
    congr 1
    simp [ite_mul]

theorem analyticAt_matrixEntry {d : ℕ} {C : OpenCone d} (ts : List (SquareFreeTerm C))
    (T : Finset (Fin d)) {z : Point d} (hz : z ∈ C.carrier) :
    AnalyticAt ℂ (matrixEntry ts T) z := by
  induction ts with
  | nil => exact analyticAt_const
  | cons t ts ih =>
    change AnalyticAt ℂ (fun w => (if t.target=T then t.coefficient.eval w else 0)+matrixEntry ts T w) z
    by_cases ht : t.target=T
    · simpa only [if_pos ht] using
        (Coefficient.analyticAt_eval t.coefficient hz).add ih
    · simpa only [if_neg ht,zero_add] using ih

end SquareFreeTerm

namespace SectorialData

/-- The actual first-order connection on the finite square-free jet vector. -/
def connection {d : ℕ} {C : OpenCone d} (D : SectorialData C) (i : Fin d) (z : Point d)
    (S T : Finset (Fin d)) : ℂ :=
  if i∈S then -(D.phase i)*(if T=S then 1 else 0)-
    SquareFreeTerm.matrixEntry (D.correctionRow S i) T z
  else if T=insert i S then 1 else 0

theorem analyticAt_connection {d : ℕ} {C : OpenCone d} (D : SectorialData C) (i : Fin d)
    (S T : Finset (Fin d)) {z : Point d} (hz : z ∈ C.carrier) :
    AnalyticAt ℂ (fun w => D.connection i w S T) z := by
  unfold connection
  split
  · exact analyticAt_const.sub (SquareFreeTerm.analyticAt_matrixEntry _ _ hz)
  · exact analyticAt_const

/-- Every actual analytic solution satisfies the constructed finite first-order
system, with no separately supplied jet relation. -/
theorem coordDeriv_squareFreeDerivative_eq_connection {d : ℕ} {C : OpenCone d} (D : SectorialData C)
    {f : Point d → ℂ} (hf : D.IsSolution f) (S : Finset (Fin d)) (i : Fin d)
    {z : Point d} (hz : z∈C.carrier) :
    coordDeriv i (squareFreeDerivative S f) z=
      ∑T : Finset (Fin d),D.connection i z S T*squareFreeDerivative T f z := by
  classical
  by_cases hi : i∈S
  · have hh := D.coordDeriv_squareFreeDerivative_of_mem S hi hf hz
    dsimp only at hh
    rw [hh,SquareFreeTerm.evalSum_eq_matrix]
    simp only [connection,if_pos hi,sub_mul,Finset.sum_sub_distrib]
    congr 1
    simp [ite_mul,Finset.mul_sum]
  · rw [coordDeriv_squareFreeDerivative_of_not_mem_cone S hi hf.1 hz]
    simp [connection,hi,ite_mul]

end SectorialData
end BourgadeHuang.EdgeCMS
