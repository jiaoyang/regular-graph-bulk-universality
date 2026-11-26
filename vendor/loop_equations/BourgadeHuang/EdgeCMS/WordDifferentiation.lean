import BourgadeHuang.EdgeCMS.HomogeneousCoefficients
import BourgadeHuang.CMS.WordDifferentiation

/-! Finite actual Leibniz expansion with arbitrary analytic homogeneous
coefficients on the chosen open cone. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.EdgeCMS
open CMS

namespace Coefficient

abbrev LeibnizTerm {d : ℕ} (C : OpenCone d) := Coefficient C × List (Fin d)

def termSum {d : ℕ} {C : OpenCone d} : List (LeibnizTerm C) → (Point d → ℂ) → Point d → ℂ
  | [],_,_ => 0
  | (e,w)::ts,f,z => e.eval z*wordDerivative w f z+termSum ts f z

def stepTerms {d : ℕ} {C : OpenCone d} (i : Fin d) : List (LeibnizTerm C) → List (LeibnizTerm C)
  | [] => []
  | (e,w)::ts => (e.derivative i,w)::(e,i::w)::stepTerms i ts

def leibnizTerms {d : ℕ} {C : OpenCone d} (e : Coefficient C) : List (Fin d) → List (LeibnizTerm C)
  | [] => [(e,[])]
  | i::w => stepTerms i (leibnizTerms e w)

theorem analyticAt_termSum {d : ℕ} {C : OpenCone d} (ts : List (LeibnizTerm C)) {f : Point d → ℂ}
    {z : Point d} (hf : AnalyticAt ℂ f z) (hz : z ∈ C.carrier) :
    AnalyticAt ℂ (termSum ts f) z := by
  induction ts with
  | nil => exact analyticAt_const
  | cons t ts ih => exact ((analyticAt_eval t.1 hz).mul (analyticAt_wordDerivative t.2 hf)).add ih

theorem coordDeriv_termSum {d : ℕ} {C : OpenCone d} (ts : List (LeibnizTerm C)) {f : Point d → ℂ}
    {z : Point d} (hf : AnalyticAt ℂ f z) (hz : z ∈ C.carrier) (i : Fin d) :
    coordDeriv i (termSum ts f) z=termSum (stepTerms i ts) f z := by
  induction ts with
  | nil => simp [termSum,stepTerms,coordDeriv]
  | cons t ts ih =>
    rcases t with ⟨e,w⟩
    change coordDeriv i ((fun x => e.eval x*wordDerivative w f x)+(termSum ts f)) z=_
    rw [coordDeriv_add_analytic (f := fun x => e.eval x*wordDerivative w f x)
      (g := termSum ts f) ((analyticAt_eval e hz).mul (analyticAt_wordDerivative w hf))
      (analyticAt_termSum ts hf hz),coordDeriv_mul_analytic (analyticAt_eval e hz)
      (analyticAt_wordDerivative w hf),coordDeriv_eval e hz,ih]
    simp only [stepTerms,termSum,wordDerivative]
    ring

/-- Finite Leibniz expansion with actual derivatives and constructed terms. -/
theorem wordDerivative_mul_eval {d : ℕ} {C : OpenCone d} (e : Coefficient C) (w : List (Fin d))
    {U : Set (Point d)} (hU : IsOpen U) (hcf : ∀z∈U,z ∈ C.carrier)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    EqOn (wordDerivative w (fun z => e.eval z*f z)) (termSum (leibnizTerms e w) f) U := by
  induction w with
  | nil => intro z hz; simp [wordDerivative,leibnizTerms,termSum]
  | cons i w ih =>
    intro z hz
    change coordDeriv i (wordDerivative w (fun z => e.eval z*f z)) z=_
    rw [coordDeriv_congr_nhds (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) ih),
      coordDeriv_termSum _ (hf z hz) (hcf z hz)]
    rfl

private theorem stepTerms_spec {d k : ℕ} {C : OpenCone d} {ts : List (LeibnizTerm C)} {w : List (Fin d)}
    (h : ∀e v,(e,v)∈ts→∃q,e.Homogeneous q ∧ q+v.length=k ∧ v.Sublist w)
    (i : Fin d) :
    ∀e v,(e,v)∈stepTerms i ts→∃q,e.Homogeneous q ∧ q+v.length=k+1 ∧ v.Sublist (i::w) := by
  induction ts with
  | nil => simp [stepTerms]
  | cons t ts ih =>
    rcases t with ⟨a,u⟩
    intro e v hm
    simp only [stepTerms,List.mem_cons,Prod.mk.injEq] at hm
    rcases hm with ⟨he,hv⟩ | ⟨he,hv⟩ | hm
    · subst e v
      obtain ⟨q,hq,hlen,hsub⟩ := h a u (List.mem_cons_self ..)
      exact ⟨q+1,homogeneous_derivative hq i,by omega,hsub.cons i⟩
    · subst e v
      obtain ⟨q,hq,hlen,hsub⟩ := h a u (List.mem_cons_self ..)
      exact ⟨q,hq,by simpa only [List.length_cons] using congrArg (·+1) hlen,hsub.cons_cons i⟩
    · exact ih (fun e v hv => h e v (List.mem_cons_of_mem _ hv)) e v hm

/-- Each Leibniz term has the exact total gap-weight plus derivative order, and
its derivative word is a subword of the original word. -/
theorem leibnizTerms_spec {d k : ℕ} {C : OpenCone d} {e : Coefficient C} (he : e.Homogeneous k)
    (w : List (Fin d)) :
    ∀a v,(a,v)∈leibnizTerms e w→∃q,a.Homogeneous q ∧ q+v.length=k+w.length ∧ v.Sublist w := by
  induction w with
  | nil =>
    intro a v hm
    simp only [leibnizTerms,List.mem_singleton,Prod.mk.injEq] at hm
    rcases hm with ⟨rfl,rfl⟩
    exact ⟨k,he,rfl,List.Sublist.refl []⟩
  | cons i w ih =>
    simpa only [List.length_cons,Nat.add_assoc] using stepTerms_spec ih i


theorem termSum_append {d : ℕ} {C : OpenCone d} (ts us : List (LeibnizTerm C)) (f : Point d → ℂ) (z : Point d) :
    termSum (ts++us) f z=termSum ts f z+termSum us f z := by
  induction ts with
  | nil => simp [termSum]
  | cons t ts ih => simp only [List.cons_append,termSum,ih,add_assoc]

def scaleTerms {d : ℕ} {C : OpenCone d} (a : Coefficient C) (ts : List (LeibnizTerm C)) : List (LeibnizTerm C) :=
  ts.map (fun t => (mul a t.1,t.2))

theorem termSum_scaleTerms {d : ℕ} {C : OpenCone d} (a : Coefficient C) (ts : List (LeibnizTerm C))
    (f : Point d → ℂ) (z : Point d) : termSum (scaleTerms a ts) f z=a.eval z*termSum ts f z := by
  induction ts with
  | nil => simp [scaleTerms,termSum]
  | cons t ts ih =>
    simp only [scaleTerms,List.map_cons,termSum,eval_mul] at ih ⊢
    rw [ih]
    ring

def appendWordTerms {d : ℕ} {C : OpenCone d} (v : List (Fin d)) (ts : List (LeibnizTerm C)) : List (LeibnizTerm C) :=
  ts.map (fun t => (t.1,t.2++v))

theorem termSum_appendWordTerms {d : ℕ} {C : OpenCone d} (v : List (Fin d)) (ts : List (LeibnizTerm C))
    (f : Point d → ℂ) (z : Point d) :
    termSum (appendWordTerms v ts) f z=termSum ts (wordDerivative v f) z := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [appendWordTerms,List.map_cons,termSum,wordDerivative_append] at ih ⊢
    rw [ih]

theorem wordDerivative_mul_word {d : ℕ} {C : OpenCone d} (e : Coefficient C) (u v : List (Fin d))
    {U : Set (Point d)} (hU : IsOpen U) (hcf : ∀z∈U,z ∈ C.carrier)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    EqOn (wordDerivative u (fun z => e.eval z*wordDerivative v f z))
      (termSum (appendWordTerms v (leibnizTerms e u)) f) U := by
  intro z hz
  rw [termSum_appendWordTerms]
  exact wordDerivative_mul_eval e u hU hcf (fun w hw => analyticAt_wordDerivative v (hf w hw)) hz


def expandTerms {d : ℕ} {C : OpenCone d} (u : List (Fin d)) : List (LeibnizTerm C) → List (LeibnizTerm C)
  | [] => []
  | (e,v)::ts => appendWordTerms v (leibnizTerms e u)++expandTerms u ts

theorem wordDerivative_termSum {d : ℕ} {C : OpenCone d} (u : List (Fin d)) (ts : List (LeibnizTerm C))
    {U : Set (Point d)} (hU : IsOpen U) (hcf : ∀z∈U,z ∈ C.carrier)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    EqOn (wordDerivative u (termSum ts f)) (termSum (expandTerms u ts) f) U := by
  induction ts with
  | nil =>
    intro z hz
    have h := wordDerivative_const_mul u (0:ℂ) hU hf hz
    simpa only [zero_mul,termSum,expandTerms] using h
  | cons t ts ih =>
    rcases t with ⟨e,v⟩
    intro z hz
    change wordDerivative u ((fun x => e.eval x*wordDerivative v f x)+termSum ts f) z=_
    rw [wordDerivative_add u hU (f := fun x => e.eval x*wordDerivative v f x)
      (g := termSum ts f)
      (fun x hx => (analyticAt_eval e (hcf x hx)).mul (analyticAt_wordDerivative v (hf x hx)))
      (fun x hx => analyticAt_termSum ts (hf x hx) (hcf x hx)) hz]
    change wordDerivative u (fun x => e.eval x*wordDerivative v f x) z+wordDerivative u (termSum ts f) z=_
    rw [wordDerivative_mul_word e u v hU hcf hf hz,ih hz]
    exact (termSum_append _ _ f z).symm

def finTerms {d : ℕ} {C : OpenCone d} : (n : ℕ) → (Fin n → List (LeibnizTerm C)) → List (LeibnizTerm C)
  | 0,_ => []
  | n+1,f => f 0++finTerms n (fun j => f j.succ)

theorem termSum_finTerms {d n : ℕ} {C : OpenCone d} (t : Fin n → List (LeibnizTerm C))
    (f : Point d → ℂ) (z : Point d) : termSum (finTerms n t) f z=∑j,termSum (t j) f z := by
  induction n with
  | zero => simp [finTerms,termSum]
  | succ n ih => simp only [finTerms,termSum_append,ih,Fin.sum_univ_succ]

end Coefficient
end BourgadeHuang.EdgeCMS
