import BourgadeHuang.EdgeCMS.SectorialReduction

/-! Constructive finite square-free normal forms for the sectorial equations.
The coefficient weights are retained through every Leibniz and PDE reduction. -/
noncomputable section
open scoped BigOperators
open Set
namespace BourgadeHuang.EdgeCMS
open CMS
open Coefficient

namespace Coefficient

theorem mem_finTerms_iff {d n : ℕ} {C : OpenCone d} (f : Fin n → List (LeibnizTerm C)) (t : LeibnizTerm C) :
    t∈finTerms n f ↔ ∃j,t∈f j := by
  induction n with
  | zero => simp [finTerms]
  | succ n ih =>
    simp only [finTerms,List.mem_append,ih]
    constructor
    · rintro (h|⟨j,hj⟩)
      · exact ⟨0,h⟩
      · exact ⟨j.succ,hj⟩
    · rintro ⟨j,hj⟩
      refine Fin.cases (fun h => Or.inl h) (fun k h => Or.inr ⟨k,h⟩) j hj

theorem mem_expandTerms {d : ℕ} {C : OpenCone d} (u : List (Fin d)) (ts : List (LeibnizTerm C))
    {e : Coefficient C} {v : List (Fin d)} (hm : (e,v)∈expandTerms u ts) :
    ∃a w,(a,w)∈ts ∧ ∃t,(e,t)∈leibnizTerms a u ∧ v=t++w := by
  induction ts with
  | nil => simp [expandTerms] at hm
  | cons aw ts ih =>
    rcases aw with ⟨a,w⟩
    simp only [expandTerms,List.mem_append] at hm
    rcases hm with hm|hm
    · obtain ⟨⟨b,t⟩,ht,heq⟩ := List.mem_map.mp hm
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl,rfl⟩
      exact ⟨a,w,List.mem_cons_self ..,t,ht,rfl⟩
    · obtain ⟨a,w,haw,t,ht,hv⟩ := ih hm
      exact ⟨a,w,List.mem_cons_of_mem _ haw,t,ht,hv⟩

/-- A finite termwise replacement preserves the actual sum and any stated
property of its coefficient/word pairs. -/
theorem exists_termSum_replacement {d : ℕ} {C : OpenCone d} (ts : List (LeibnizTerm C))
    (P : Coefficient C → List (Fin d) → Prop) (S : (Point d → ℂ) → Prop)
    (h : ∀e v,(e,v)∈ts→∃ us : List (LeibnizTerm C),
      (∀a w,(a,w)∈us→P a w) ∧
      ∀f,S f→EqOn (fun z => e.eval z*wordDerivative v f z) (termSum us f) C.carrier) :
    ∃ us : List (LeibnizTerm C),(∀a w,(a,w)∈us→P a w) ∧
      ∀f,S f→EqOn (termSum ts f) (termSum us f) C.carrier := by
  induction ts with
  | nil => exact ⟨[],by simp,fun _ _ _ _ => rfl⟩
  | cons t ts ih =>
    rcases t with ⟨e,v⟩
    obtain ⟨us,hus,heq⟩ := h e v (List.mem_cons_self ..)
    obtain ⟨vs,hvs,hveq⟩ := ih (fun a w hm => h a w (List.mem_cons_of_mem _ hm))
    refine ⟨us++vs,?_,?_⟩
    · intro a w hm
      exact (List.mem_append.mp hm).elim (hus a w) (hvs a w)
    · intro f hf z hz
      change e.eval z*wordDerivative v f z+termSum ts f z=_
      have hh := heq f hf hz
      dsimp only at hh
      rw [hh,hveq f hf hz,termSum_append]

end Coefficient

namespace SectorialData

theorem remainderTerms_spec {d : ℕ} {C : OpenCone d} (D : SectorialData C) (i : Fin d)
    {e : Coefficient C} {v : List (Fin d)} (hm : (e,v)∈D.remainderTerms i) :
    (∃j,e=D.first i j ∧ v=[j]) ∨ (e=D.scalar i ∧ v=[]) := by
  simp only [remainderTerms,List.mem_append,mem_finTerms_iff,List.mem_singleton,
    Prod.mk.injEq] at hm
  exact hm

/-- A differentiated remainder is either a differentiated scalar term or a
first-order term with one appended coordinate. The remaining word is always a
subword of the differentiating word. -/
theorem expanded_remainder_spec {d : ℕ} {C : OpenCone d} (D : SectorialData C) (i : Fin d)
    (u : List (Fin d)) {e : Coefficient C} {v : List (Fin d)}
    (hm : (e,v)∈expandTerms u (D.remainderTerms i)) :
    ∃t q,t.Sublist u ∧ e.Homogeneous q ∧
      ((v=t ∧ q+t.length=2+u.length) ∨
       (∃j,v=t++[j] ∧ q+t.length=1+u.length)) := by
  obtain ⟨a,w,haw,t,ht,rfl⟩ := mem_expandTerms u _ hm
  rcases D.remainderTerms_spec i haw with ⟨j,rfl,rfl⟩|⟨rfl,rfl⟩
  · obtain ⟨q,hq,hlen,hsub⟩ := leibnizTerms_spec (D.first_homogeneous i j) u e t ht
    exact ⟨t,q,hsub,hq,Or.inr ⟨j,rfl,hlen⟩⟩
  · obtain ⟨q,hq,hlen,hsub⟩ := leibnizTerms_spec (D.scalar_homogeneous i) u e t ht
    exact ⟨t,q,hsub,hq,Or.inl ⟨by simp,hlen⟩⟩

/-- The two radial orders retained by square-free reduction. -/
def NormalTerm {d : ℕ} {C : OpenCone d} (n : ℕ) (e : Coefficient C) (v : List (Fin d)) : Prop :=
  v.Nodup ∧ ∃q,e.Homogeneous q ∧ ((q+v.length=n ∧ v≠[]) ∨ q+v.length=n+1)

/-- A correction has positive inverse-gap weight. Its order-zero radial terms
therefore strictly lower the square-free degree. -/
def CorrectionTerm {d : ℕ} {C : OpenCone d} (n : ℕ) (e : Coefficient C) (v : List (Fin d)) : Prop :=
  v.Nodup ∧ ∃q,e.Homogeneous q ∧ 1≤q ∧ ((q+v.length=n ∧ v≠[]) ∨ q+v.length=n+1)

theorem CorrectionTerm.normal {d n : ℕ} {C : OpenCone d} {e : Coefficient C} {v : List (Fin d)}
    (h : CorrectionTerm n e v) : NormalTerm n e v := by
  obtain ⟨hv,q,hq,_,hdeg⟩ := h
  exact ⟨hv,q,hq,hdeg⟩

theorem CorrectionTerm.degree_le {d n : ℕ} {C : OpenCone d} {e : Coefficient C} {v : List (Fin d)}
    (h : CorrectionTerm n e v) : v.length≤n := by
  obtain ⟨_,q,_,hq,hdeg⟩ := h
  omega


private theorem normalize_remainder {d : ℕ} {C : OpenCone d} (D : SectorialData C)
    (u : List (Fin d)) (hu : u.Nodup) (i : Fin d) (hi : i∈u)
    (ih : ∀t : List (Fin d),t.length<u.length→t.Nodup→∀j : Fin d,
      ∃ ts : List (LeibnizTerm C),(∀a v,(a,v)∈ts→NormalTerm t.length a v) ∧
      ∀f,D.IsSolution f→EqOn (wordDerivative (j::t) f) (termSum ts f) C.carrier) :
    ∃ ts : List (LeibnizTerm C),(∀a v,(a,v)∈ts→CorrectionTerm u.length a v) ∧
      ∀f,D.IsSolution f→EqOn (termSum (expandTerms (u.erase i) (D.remainderTerms i)) f)
        (termSum ts f) C.carrier := by
  apply exists_termSum_replacement _ (CorrectionTerm u.length) D.IsSolution
  intro e v hm
  obtain ⟨t,q,ht,hq,hv⟩ := D.expanded_remainder_spec i (u.erase i) hm
  have htlen := ht.length_le
  have herase := List.length_erase_of_mem hi
  have hun : 0<u.length := List.length_pos_of_mem hi
  have htn : t.Nodup := ht.nodup (List.Nodup.erase i hu)
  have htlt : t.length<u.length := by omega
  rcases hv with ⟨rfl,hdeg⟩|⟨j,rfl,hdeg⟩
  · refine ⟨[(e,v)],?_,?_⟩
    · intro a w hm
      simp only [List.mem_singleton,Prod.mk.injEq] at hm
      rcases hm with ⟨rfl,rfl⟩
      exact ⟨htn,q,hq,by omega,Or.inr (by omega)⟩
    · intro f hf z hz
      simp only [termSum,add_zero]
  · obtain ⟨ts,hts,heq⟩ := ih t htlt htn j
    refine ⟨scaleTerms e ts,?_,?_⟩
    · intro a w hm
      obtain ⟨⟨b,v⟩,hb,he⟩ := List.mem_map.mp hm
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      obtain ⟨hv,k,hk,hkd⟩ := hts b v hb
      refine ⟨hv,q+k,Homogeneous.mul hq hk,by omega,?_⟩
      rcases hkd with hkd|hkd
      · exact Or.inl ⟨by omega,hkd.2⟩
      · exact Or.inr (by omega)
    · intro f hf z hz
      dsimp only
      rw [termSum_scaleTerms]
      have hp : (t++[j]).Perm (j::t) := by
        simp only [List.singleton_append] at *
        exact List.perm_append_comm
      rw [wordDerivative_perm hp C.isOpen hf.1 hz,heq f hf hz]

/-- Every extra derivative of a square-free word has a finite square-free
normal form. The construction depends only on the differential equations,
not on the chosen analytic solution. -/
theorem exists_extra_normalForm {d : ℕ} {C : OpenCone d} (D : SectorialData C)
    (u : List (Fin d)) (hu : u.Nodup) (i : Fin d) :
    ∃ ts : List (LeibnizTerm C),(∀a v,(a,v)∈ts→NormalTerm u.length a v) ∧
      ∀f,D.IsSolution f→EqOn (wordDerivative (i::u) f) (termSum ts f) C.carrier := by
  suffices hall : ∀n,∀u : List (Fin d),u.length=n→u.Nodup→∀i : Fin d,
      ∃ ts : List (LeibnizTerm C),(∀a v,(a,v)∈ts→NormalTerm u.length a v) ∧
      ∀f,D.IsSolution f→EqOn (wordDerivative (i::u) f) (termSum ts f) C.carrier from
    hall u.length u rfl hu i
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u hn hu i
    by_cases hi : i∈u
    · obtain ⟨ts,hts,heq⟩ := normalize_remainder D u hu i hi (by
        intro t ht htn j
        exact ih t.length (by omega) t rfl htn j)
      refine ⟨(Coefficient.const (-(D.phase i)),u)::scaleTerms (Coefficient.const (-1)) ts,?_,?_⟩
      · intro a v hm
        simp only [List.mem_cons,Prod.mk.injEq] at hm
        rcases hm with ⟨rfl,rfl⟩|hm
        · exact ⟨hu,0,Homogeneous.const _,Or.inl ⟨by omega,by intro hnil; simp [hnil] at hi⟩⟩
        · obtain ⟨⟨b,w⟩,hb,he⟩ := List.mem_map.mp hm
          simp only [Prod.mk.injEq] at he
          rcases he with ⟨rfl,rfl⟩
          obtain ⟨hw,k,hk,_,hdeg⟩ := hts b w hb
          exact ⟨hw,0+k,Homogeneous.mul (Homogeneous.const _) hk,by simpa using hdeg⟩
      · intro f hf z hz
        rw [wordDerivative_extra_eq hf i u hi hz]
        dsimp only
        rw [heq f hf hz]
        simp only [termSum,termSum_scaleTerms,Coefficient.eval_const]
        ring
    · refine ⟨[(Coefficient.const 1,i::u)],?_,?_⟩
      · intro a v hm
        simp only [List.mem_singleton,Prod.mk.injEq] at hm
        rcases hm with ⟨rfl,rfl⟩
        exact ⟨List.nodup_cons.mpr ⟨hi,hu⟩,0,Homogeneous.const _,Or.inr (by simp)⟩
      · intro f hf z hz
        simp only [termSum,Coefficient.eval_const,one_mul,add_zero]

/-- For a repeated coordinate the diagonal term is explicit. Every remaining
order-zero radial coefficient strictly lowers the derivative degree. -/
theorem exists_repeated_normalForm {d : ℕ} {C : OpenCone d} (D : SectorialData C)
    (u : List (Fin d)) (hu : u.Nodup) (i : Fin d) (hi : i∈u) :
    ∃ ts : List (LeibnizTerm C),(∀a v,(a,v)∈ts→CorrectionTerm u.length a v) ∧
      ∀f,D.IsSolution f→EqOn (wordDerivative (i::u) f)
        (fun z => -(D.phase i)*wordDerivative u f z-termSum ts f z) C.carrier := by
  obtain ⟨ts,hts,heq⟩ := normalize_remainder D u hu i hi
    (fun t _ htn j => D.exists_extra_normalForm t htn j)
  refine ⟨ts,hts,?_⟩
  intro f hf z hz
  rw [wordDerivative_extra_eq hf i u hi hz]
  dsimp only
  rw [heq f hf hz]

end SectorialData
end BourgadeHuang.EdgeCMS
