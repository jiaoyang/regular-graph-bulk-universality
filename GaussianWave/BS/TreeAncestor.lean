import GaussianWave.BS.TreeHomogeneity

/-! Literal rooted ancestry is iterated parenthood. It agrees with the
stored word-prefix relation and is preserved by every actual rooted graph
automorphism. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS

def RegularTreeAncestor {d : ℕ} (u v : RegularTreeVertex d) : Prop :=
  ∃ n : ℕ,(regularTreeParent^[n]) v=u

theorem regularTreeParent_iterate_append {d : ℕ} (a : Fin d)
    (s w : List (Fin (d-1))) :
    (regularTreeParent^[s.length]) (some (a,s++w))=some (a,w) := by
  induction s with
  | nil => rfl
  | cons b s ih =>
      simpa only [List.length_cons,Function.iterate_succ_apply,List.cons_append,regularTreeParent] using ih

theorem regularTreeParent_iterate_some {d : ℕ} (n : ℕ) (a b : Fin d)
    (w z : List (Fin (d-1)))
    (h : (regularTreeParent^[n]) (some (a,w))=some (b,z)) :
    a=b ∧ ∃ s : List (Fin (d-1)),w=s++z := by
  induction n generalizing w with
  | zero =>
      change some (a,w)=some (b,z) at h
      have hp := Option.some.inj h
      exact ⟨congrArg Prod.fst hp,[],by simpa only [List.nil_append] using congrArg Prod.snd hp⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      cases w with
      | nil =>
          have hn : (regularTreeParent^[n]) (none : RegularTreeVertex d)=none :=
            Function.iterate_fixed rfl n
          simp only [regularTreeParent,hn] at h
          exact False.elim (Option.noConfusion h)
      | cons c w =>
          obtain ⟨hab,s,hs⟩ := ih w h
          exact ⟨hab,c::s,by simp only [List.cons_append,hs]⟩

theorem regularTreeAncestor_word_iff {d : ℕ} (a b : Fin d)
    (w z : List (Fin (d-1))) :
    RegularTreeAncestor (some (a,w.reverse)) (some (b,z.reverse)) ↔ a=b ∧ w.IsPrefix z := by
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨hba,s,hs⟩ := regularTreeParent_iterate_some n b a z.reverse w.reverse hn
    refine ⟨hba.symm,s.reverse,?_⟩
    have hr := congrArg List.reverse hs
    simpa only [List.reverse_reverse,List.reverse_append] using hr.symm
  · rintro ⟨rfl,s,hs⟩
    refine ⟨s.reverse.length,?_⟩
    rw [← hs,List.reverse_append]
    exact regularTreeParent_iterate_append a s.reverse w.reverse

theorem regularTreeIso_ancestor (d : ℕ) (e : regularWordTree d ≃g regularWordTree d)
    (hroot : e none=none) (u v : RegularTreeVertex d) :
    RegularTreeAncestor (e u) (e v) ↔ RegularTreeAncestor u v := by
  have hc : Function.Semiconj e regularTreeParent regularTreeParent :=
    regularTreeIso_parent d e hroot
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n,e.injective ?_⟩
    exact (hc.iterate_right n v).trans hn
  · rintro ⟨n,hn⟩
    exact ⟨n,(hc.iterate_right n v).symm.trans (congrArg e hn)⟩

/-- The finite branch prefix condition needed for recursive automorphism
decomposition follows from an actual rooted ambient graph isomorphism. -/
theorem regularTreeIso_word_prefix (d : ℕ) (e : regularWordTree d ≃g regularWordTree d)
    (hroot : e none=none) (a b : Fin d) (u v u' v' : List (Fin (d-1)))
    (hu : e (some (a,u.reverse))=some (b,u'.reverse))
    (hv : e (some (a,v.reverse))=some (b,v'.reverse)) :
    u'.IsPrefix v' ↔ u.IsPrefix v := by
  have h := regularTreeIso_ancestor d e hroot (some (a,u.reverse)) (some (a,v.reverse))
  rw [hu,hv,regularTreeAncestor_word_iff,regularTreeAncestor_word_iff] at h
  simpa only [true_and] using h

end GaussianWave.BS
