import BourgadeHuang.CMS.SectorialObstruction

/-! A holomorphic solution of the actual finite connection consists of the
true square-free jets of its empty component, and that component satisfies
the original gauged CMS differential equations. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS
open GapExpression
set_option maxHeartbeats 1600000
variable {d : ℕ}

/-- Equality of square-free operator symbols acts on every analytic germ;
no global extension of that germ and no PDE solution is required. -/
theorem termSum_squareFree_symbol (ts : List (LeibnizTerm d))
    (hts : ∀e u,(e,u)∈ts→u.Nodup) {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) :
    termSum ts f z=∑S : Finset (Fin d),
      MvPolynomial.coeff (wordIndex S.toList) (operatorSymbol ts z)*squareFreeDerivative S f z := by
  induction ts with
  | nil=>simp [termSum,operatorSymbol]
  | cons t ts ih=>
    have ht : t.2.Nodup := hts t.1 t.2 (List.mem_cons_self ..)
    have hi := ih (fun e u h=>hts e u (List.mem_cons_of_mem _ h))
    have hindex (S : Finset (Fin d)) : wordIndex t.2=wordIndex S.toList ↔ t.2.toFinset=S := by
      have hword : wordIndex t.2=wordIndex t.2.toFinset.toList :=
        (wordIndex_eq_iff_perm _ _).mpr (List.toFinset_toList ht).symm
      rw [hword,wordIndex_toList_injective]
    have hderiv : wordDerivative t.2 f z=squareFreeDerivative t.2.toFinset f z :=
      wordDerivative_perm (List.toFinset_toList ht).symm (isOpen_analyticAt ℂ f)
        (fun _ h=>h) hf
    simp only [termSum,operatorSymbol,List.map_cons,List.sum_cons,MvPolynomial.coeff_add,
      MvPolynomial.coeff_C_mul,coeff_wordSymbol,hindex,add_mul,Finset.sum_add_distrib]
    change t.1.eval z*wordDerivative t.2 f z+termSum ts f z=_
    rw [hi,hderiv]
    congr 1
    simp [mul_ite,ite_mul]

theorem termSum_eq_of_squareFree_symbol {ts us : List (LeibnizTerm d)}
    (hts : ∀e u,(e,u)∈ts→u.Nodup) (hus : ∀e u,(e,u)∈us→u.Nodup)
    {f : Point d → ℂ} {z : Point d} (hf : AnalyticAt ℂ f z)
    (he : operatorSymbol ts z=operatorSymbol us z) : termSum ts f z=termSum us f z := by
  rw [termSum_squareFree_symbol ts hts hf,termSum_squareFree_symbol us hus hf,he]

namespace SectorialData
variable (D : SectorialData d)

/-- The finite system of actual coordinate derivatives. -/
def ConnectionSolutionOn (G : Point d → Finset (Fin d) → ℂ) (U : Set (Point d)) : Prop :=
  (∀S,AnalyticOnNhd ℂ (fun z=>G z S) U) ∧
    ∀z∈U,∀i S,coordDeriv i (fun w=>G w S) z=∑T,D.connection i z S T*G z T

theorem connectionSolution_wordDerivative {G : Point d → Finset (Fin d) → ℂ}
    {U : Set (Point d)} (hU : IsOpen U) (hG : D.ConnectionSolutionOn G U)
    (u : List (Fin d)) (hu : u.Nodup) :
    EqOn (wordDerivative u (fun z=>G z ∅)) (fun z=>G z u.toFinset) U := by
  induction u with
  | nil=>intro z hz;rfl
  | cons i u ih=>
    have hi : i∉u.toFinset := by simpa using (List.nodup_cons.mp hu).1
    have he := ih (List.nodup_cons.mp hu).2
    intro z hz
    change coordDeriv i (wordDerivative u (fun z=>G z ∅)) z=G z (i::u).toFinset
    rw [coordDeriv_congr_nhds (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) he),hG.2 z hz i u.toFinset]
    simp [connection,hi]

/-- Every subset component really is the corresponding mixed derivative of
the empty component. -/
theorem connectionSolution_squareFreeDerivative {G : Point d → Finset (Fin d) → ℂ}
    {U : Set (Point d)} (hU : IsOpen U) (hG : D.ConnectionSolutionOn G U)
    (S : Finset (Fin d)) :
    EqOn (squareFreeDerivative S (fun z=>G z ∅)) (fun z=>G z S) U := by
  simpa only [squareFreeDerivative,Finset.toList_toFinset] using
    D.connectionSolution_wordDerivative hU hG S.toList S.nodup_toList

/-- The chosen singleton row agrees with the explicitly isolated defining
PDE, as an operator on any analytic germ. -/
theorem general_connection_singleton_row (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hβ : β≠0) (hc : ∀i,c i= -1 ∨ c i=β/2)
    (i : Fin d) {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (hz : z∈OrderedDomain d) :
    (∑T,(general β c σ).connection i z {i} T*squareFreeDerivative T f z)=
      -((general β c σ).phase i)*coordDeriv i f z-
        termSum ((general β c σ).remainderTerms i) f z := by
  let D := general β c σ
  let ts := (.const (-(D.phase i)),[i])::scaleTerms (.const (-1)) (D.remainderTerms i)
  have heq : D.OperatorCongruent (D.connectionTerms i {i}) ts := by
    have hconn := (D.connectionTerms_certificate i {i}).symm
    simp only [Finset.toList_singleton] at hconn
    exact hconn.trans (OperatorCongruent.equation D i)
  have hts : ∀e u,(e,u)∈ts→u.Nodup := by
    intro e u hu
    rcases List.mem_cons.mp hu with he|he
    · have hw := (Prod.mk.inj he).2
      simp only [hw,List.nodup_cons,List.mem_nil_iff,not_false_eq_true,List.nodup_nil,and_self]
    · obtain ⟨t,ht,he⟩ := List.mem_map.mp he
      have hw := (Prod.mk.inj he).2
      rcases D.remainderTerms_spec i ht with ⟨j,_,h⟩|⟨_,h⟩
      · simpa only [←hw,h] using (show ([j]:List (Fin d)).Nodup by simp)
      · simpa only [←hw,h] using (show ([]:List (Fin d)).Nodup by simp)
  have hs := heq.squareFree_symbol β c σ hβ hc (D.connectionTerms_squareFree i {i}) hts hz
  have ht := termSum_eq_of_squareFree_symbol (D.connectionTerms_squareFree i {i}) hts hf hs
  rw [D.termSum_connectionTerms] at ht
  simpa only [ts,termSum,termSum_scaleTerms,GapExpression.eval,wordDerivative,add_zero,
    neg_one_mul,←sub_eq_add_neg] using ht

/-- A local holomorphic connection solution satisfies the actual defining
sectorial PDE. The compatibility of the singleton row is proved by
confluence, rather than assumed as an additional equation. -/
theorem general_connectionSolution_operator (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hβ : β≠0) (hc : ∀i,c i= -1 ∨ c i=β/2)
    {G : Point d → Finset (Fin d) → ℂ} {U : Set (Point d)}
    (hU : IsOpen U) (hsub : U⊆OrderedDomain d)
    (hG : (general β c σ).ConnectionSolutionOn G U) :
    ∀z∈U,∀i,(general β c σ).operator i (fun w=>G w ∅) z=0 := by
  let D := general β c σ
  have hj := D.connectionSolution_squareFreeDerivative hU hG
  intro z hz i
  have hfirst : EqOn (coordDeriv i (fun w=>G w ∅)) (fun w=>G w {i}) U := by
    simpa only [squareFreeDerivative,Finset.toList_singleton,wordDerivative] using hj {i}
  have hsecond : secondPartial i (fun w=>G w ∅) z=
      ∑T,D.connection i z {i} T*squareFreeDerivative T (fun w=>G w ∅) z := by
    unfold secondPartial
    rw [coordDeriv_congr_nhds (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) hfirst),hG.2 z hz i {i}]
    apply Finset.sum_congr rfl
    intro T hT
    rw [hj T hz]
  rw [general_connection_singleton_row β c σ hβ hc i (hG.1 ∅ z hz) (hsub hz)] at hsecond
  rw [D.termSum_remainderTerms] at hsecond
  change secondPartial i (fun w=>G w ∅) z+D.phase i*coordDeriv i (fun w=>G w ∅) z+_+_=0
  linear_combination hsecond

/-- The ungauged local CMS equation follows for the actual general branch. -/
theorem general_connectionSolution_deformed (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hβ : β≠0) (hc : ∀i,c i= -1 ∨ c i=β/2)
    {G : Point d → Finset (Fin d) → ℂ} {U : Set (Point d)}
    (hU : IsOpen U) (hsub : U⊆OrderedDomain d)
    (hG : (general β c σ).ConnectionSolutionOn G U) :
    ∀z∈U,∀i,deformedOperator β c i (fun w=>generalBranch β c σ w*G w ∅) z=0 := by
  intro z hz i
  rw [deformedOperator_generalBranch_mul_eq_zero_iff β c σ (hsub hz) (hG.1 ∅ z hz),
    ←operator_general β c σ i _ (hsub hz)]
  exact general_connectionSolution_operator β c σ hβ hc hU hsub hG z hz i

end SectorialData
end BourgadeHuang.CMS
