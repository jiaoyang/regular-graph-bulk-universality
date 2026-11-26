import BourgadeHuang.CMS.DifferentialCertificates
import BourgadeHuang.CMS.SectorialNormalForm

/-! Square-free reduction with explicit differential-ideal certificates.
The normal forms retain their construction, independently of PDE existence. -/
noncomputable section
open scoped BigOperators
open Set
namespace BourgadeHuang.CMS
open GapExpression
namespace SectorialData
namespace OperatorCongruent
variable {d : ℕ} {D : SectorialData d}

lemma expandTerms_append (u : List (Fin d)) (ts us : List (LeibnizTerm d)) :
    expandTerms u (ts++us)=expandTerms u ts++expandTerms u us := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.cons_append,expandTerms,ih,List.append_assoc]

lemma expand_const_word (a : ℂ) (u v : List (Fin d)) :
    D.OperatorCongruent (expandTerms u [(.const a,v)]) [(.const a,u++v)] := by
  apply of_identity
  intro f hf z hz
  rw [← wordDerivative_termSum u _ (orderedDomain_isOpen d)
    (fun _ hw => orderedDomain_collisionFree hw) hf hz]
  have he : termSum [(.const a,v)] f=fun w => a*wordDerivative v f w := by
    funext w
    simp only [termSum,GapExpression.eval,add_zero]
  rw [he,wordDerivative_const_mul u a (orderedDomain_isOpen d)
    (fun w hw => analyticAt_wordDerivative v (hf w hw)) hz]
  simp only [termSum,GapExpression.eval,add_zero,wordDerivative_append]

lemma expand_scale_const (a : ℂ) (u : List (Fin d)) (ts : List (LeibnizTerm d)) :
    D.OperatorCongruent (expandTerms u (scaleTerms (.const a) ts))
      (scaleTerms (.const a) (expandTerms u ts)) := by
  apply of_identity
  intro f hf z hz
  rw [← wordDerivative_termSum u _ (orderedDomain_isOpen d)
    (fun _ hw => orderedDomain_collisionFree hw) hf hz]
  have he : termSum (scaleTerms (.const a) ts) f=fun w => a*termSum ts f w := by
    funext w
    rw [termSum_scaleTerms]
    rfl
  rw [he,wordDerivative_const_mul u a (orderedDomain_isOpen d)
    (fun w hw => analyticAt_termSum ts (hf w hw) (orderedDomain_collisionFree hw)) hz]
  dsimp only
  rw [wordDerivative_termSum u _ (orderedDomain_isOpen d)
    (fun _ hw => orderedDomain_collisionFree hw) hf hz,termSum_scaleTerms]
  rfl

/-- Repeated-coordinate reduction retains a differentiated primitive PDE row. -/
theorem extra (D : SectorialData d) (i : Fin d) (u : List (Fin d)) (hi : i∈u) :
    D.OperatorCongruent [(.const 1,i::u)]
      ((.const (-(D.phase i)),u)::scaleTerms (.const (-1))
        (expandTerms (u.erase i) (D.remainderTerms i))) := by
  have hp : (i::u).Perm (u.erase i++[i,i]) := by
    apply (List.Perm.cons i (List.perm_cons_erase hi)).trans
    simpa only [List.cons_append,List.nil_append] using
      (List.perm_append_comm : ([i,i]++u.erase i).Perm (u.erase i++[i,i]))
  have hq : u.Perm (u.erase i++[i]) :=
    (List.perm_cons_erase hi).trans (by
      simpa using (List.perm_append_comm : ([i]++u.erase i).Perm (u.erase i++[i])))
  apply (word_perm hp (.const 1)).trans
  apply (expand_const_word 1 (u.erase i) [i,i]).symm.trans
  apply ((equation D i).expand (u.erase i)).trans
  change D.OperatorCongruent
    (expandTerms (u.erase i) ([((.const (-(D.phase i))),[i])]++scaleTerms (.const (-1)) (D.remainderTerms i)))
    ([((.const (-(D.phase i))),u)]++scaleTerms (.const (-1)) (expandTerms (u.erase i) (D.remainderTerms i)))
  rw [expandTerms_append]
  exact ((expand_const_word _ _ _).trans (word_perm hq.symm _)).append (expand_scale_const _ _ _)

end OperatorCongruent

private theorem exists_certified_replacement {d : ℕ} (D : SectorialData d)
    (ts : List (LeibnizTerm d)) (P : GapExpression d → List (Fin d) → Prop)
    (h : ∀e v,(e,v)∈ts→∃us,(∀a w,(a,w)∈us→P a w) ∧ D.OperatorCongruent [(e,v)] us) :
    ∃us,(∀a w,(a,w)∈us→P a w) ∧ D.OperatorCongruent ts us := by
  induction ts with
  | nil => exact ⟨[],by simp,OperatorCongruent.refl _⟩
  | cons t ts ih =>
    rcases t with ⟨e,v⟩
    obtain ⟨us,hus,heq⟩ := h e v (List.mem_cons_self ..)
    obtain ⟨vs,hvs,hveq⟩ := ih (fun a w hm => h a w (List.mem_cons_of_mem _ hm))
    refine ⟨us++vs,?_,heq.append hveq⟩
    intro a w hm
    exact (List.mem_append.mp hm).elim (hus a w) (hvs a w)

private theorem normalize_remainder_certified {d : ℕ} (D : SectorialData d)
    (u : List (Fin d)) (hu : u.Nodup) (i : Fin d) (hi : i∈u)
    (ih : ∀t : List (Fin d),t.length<u.length→t.Nodup→∀j : Fin d,
      ∃ts,(∀a v,(a,v)∈ts→NormalTerm t.length a v) ∧
        D.OperatorCongruent [(.const 1,j::t)] ts) :
    ∃ts,(∀a v,(a,v)∈ts→CorrectionTerm u.length a v) ∧
      D.OperatorCongruent (expandTerms (u.erase i) (D.remainderTerms i)) ts := by
  apply exists_certified_replacement D _ (CorrectionTerm u.length)
  intro e v hm
  obtain ⟨t,q,ht,hq,hv⟩ := D.expanded_remainder_spec i (u.erase i) hm
  have htlen := ht.length_le
  have herase := List.length_erase_of_mem hi
  have hun : 0<u.length := List.length_pos_of_mem hi
  have htn : t.Nodup := ht.nodup (List.Nodup.erase i hu)
  have htlt : t.length<u.length := by omega
  rcases hv with ⟨rfl,hdeg⟩|⟨j,rfl,hdeg⟩
  · refine ⟨[(e,v)],?_,OperatorCongruent.refl _⟩
    intro a w hm
    simp only [List.mem_singleton,Prod.mk.injEq] at hm
    rcases hm with ⟨rfl,rfl⟩
    exact ⟨htn,q,hq,by omega,Or.inr (by omega)⟩
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
    · have hp : (t++[j]).Perm (j::t) := List.perm_append_comm
      apply (OperatorCongruent.word_perm hp e).trans
      apply OperatorCongruent.trans _ (heq.scale e)
      apply OperatorCongruent.of_identity
      intro f hf z hz
      simp only [scaleTerms,List.map_cons,List.map_nil,termSum,GapExpression.eval,mul_one]

/-- The square-free normal form is accompanied by a finite left-ideal
certificate valid on every analytic test function. -/
theorem exists_extra_normalForm_certified {d : ℕ} (D : SectorialData d)
    (u : List (Fin d)) (hu : u.Nodup) (i : Fin d) :
    ∃ts,(∀a v,(a,v)∈ts→NormalTerm u.length a v) ∧
      D.OperatorCongruent [(.const 1,i::u)] ts := by
  suffices hall : ∀n,∀u : List (Fin d),u.length=n→u.Nodup→∀i : Fin d,
      ∃ts,(∀a v,(a,v)∈ts→NormalTerm u.length a v) ∧
        D.OperatorCongruent [(.const 1,i::u)] ts from hall u.length u rfl hu i
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u hn hu i
    by_cases hi : i∈u
    · obtain ⟨ts,hts,heq⟩ := normalize_remainder_certified D u hu i hi (by
        intro t ht htn j
        exact ih t.length (by omega) t rfl htn j)
      refine ⟨(.const (-(D.phase i)),u)::scaleTerms (.const (-1)) ts,?_,?_⟩
      · intro a v hm
        simp only [List.mem_cons,Prod.mk.injEq] at hm
        rcases hm with ⟨rfl,rfl⟩|hm
        · exact ⟨hu,0,Homogeneous.const _,Or.inl ⟨by omega,by intro hnil; simp [hnil] at hi⟩⟩
        · obtain ⟨⟨b,w⟩,hb,he⟩ := List.mem_map.mp hm
          simp only [Prod.mk.injEq] at he
          rcases he with ⟨rfl,rfl⟩
          obtain ⟨hw,k,hk,_,hdeg⟩ := hts b w hb
          exact ⟨hw,0+k,Homogeneous.mul (Homogeneous.const _) hk,by simpa using hdeg⟩
      · exact (OperatorCongruent.extra D i u hi).trans
          ((OperatorCongruent.refl [(.const (-(D.phase i)),u)]).append (heq.scale (.const (-1))))
    · refine ⟨[(.const 1,i::u)],?_,OperatorCongruent.refl _⟩
      intro a v hm
      simp only [List.mem_singleton,Prod.mk.injEq] at hm
      rcases hm with ⟨rfl,rfl⟩
      exact ⟨List.nodup_cons.mpr ⟨hi,hu⟩,0,Homogeneous.const _,Or.inr (by simp)⟩

/-- The repeated-coordinate diagonal and its strict lower-degree correction
are obtained with their explicit differential-ideal certificate. -/
theorem exists_repeated_normalForm_certified {d : ℕ} (D : SectorialData d)
    (u : List (Fin d)) (hu : u.Nodup) (i : Fin d) (hi : i∈u) :
    ∃ts,(∀a v,(a,v)∈ts→CorrectionTerm u.length a v) ∧
      D.OperatorCongruent [(.const 1,i::u)]
        ((.const (-(D.phase i)),u)::scaleTerms (.const (-1)) ts) := by
  obtain ⟨ts,hts,heq⟩ := normalize_remainder_certified D u hu i hi
    (fun t _ htn j => D.exists_extra_normalForm_certified t htn j)
  exact ⟨ts,hts,(OperatorCongruent.extra D i u hi).trans
    ((OperatorCongruent.refl [(.const (-(D.phase i)),u)]).append (heq.scale (.const (-1))))⟩

end SectorialData
end BourgadeHuang.CMS
