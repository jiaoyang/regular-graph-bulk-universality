import BourgadeHuang.CMS.ExplicitFunctions
import Mathlib.Tactic.Linarith

/-! Exact sign counts in the degree of the CMS rational prefactor. -/
noncomputable section
namespace BourgadeHuang.CMS

def signCount {n : ℕ} (ε : Fin n → Sign) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun i => ε i=b)).card

def crossSamePairs {n m : ℕ} (ε : Fin n → Sign) (η : Fin m → Sign) :
    Finset (Fin n × Fin m) := Finset.univ.filter (fun p => ε p.1=η p.2)

theorem card_oppositePairs {n : ℕ} (ε : Fin n → Sign) :
    (oppositePairs ε).card=signCount ε false*signCount ε true := by
  classical
  rw [signCount,signCount,←Finset.card_product]
  apply Finset.card_bij (fun p _ => if ε p.1=false then p else p.swap)
  · intro p hp
    have hh : p.1<p.2 ∧ ε p.1≠ε p.2 := by simpa [oppositePairs] using hp
    cases h1 : ε p.1 <;> cases h2 : ε p.2 <;> simp_all
  · intro p hp q hq he
    have hp' : p.1<p.2 := (Finset.mem_filter.mp hp).2.1
    have hq' : q.1<q.2 := (Finset.mem_filter.mp hq).2.1
    split_ifs at he with h1 h2 h2
    · exact he
    · have hf := congrArg Prod.fst he
      have hs := congrArg Prod.snd he
      simp only [Prod.fst_swap,Prod.snd_swap] at hf hs
      omega
    · have hf := congrArg Prod.fst he
      have hs := congrArg Prod.snd he
      simp only [Prod.fst_swap,Prod.snd_swap] at hf hs
      omega
    · exact Prod.swap_injective he
  · intro p hp
    have hf : ε p.1=false := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
    have ht : ε p.2=true := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2
    have hne : p.1≠p.2 := by intro he; rw [he,ht] at hf; contradiction
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨p,?_,?_⟩
      · simp [oppositePairs,hlt,hf,ht]
      · simp [hf]
    · refine ⟨p.swap,?_,?_⟩
      · simp [oppositePairs,hgt,hf,ht]
      · simp [ht]

theorem card_crossSamePairs {n m : ℕ} (ε : Fin n → Sign) (η : Fin m → Sign) :
    (crossSamePairs ε η).card =
      signCount ε false*signCount η false+signCount ε true*signCount η true := by
  classical
  let A := (Finset.univ.filter (fun i => ε i=false)).product
    (Finset.univ.filter (fun j => η j=false))
  let B := (Finset.univ.filter (fun i => ε i=true)).product
    (Finset.univ.filter (fun j => η j=true))
  have he : crossSamePairs ε η=A∪B := by
    ext p
    cases h1 : ε p.1 <;> cases h2 : η p.2 <;> simp [crossSamePairs,A,B,h1,h2]
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hf : ε p.1=false := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
    have ht : ε p.1=true := (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
    rw [ht] at hf
    contradiction
  rw [he,Finset.card_union_of_disjoint hd]
  dsimp only [A,B,signCount]
  exact congrArg₂ Nat.add
    (Finset.card_product (Finset.univ.filter (fun i : Fin n => ε i=false))
      (Finset.univ.filter (fun j : Fin m => η j=false)))
    (Finset.card_product (Finset.univ.filter (fun i : Fin n => ε i=true))
      (Finset.univ.filter (fun j : Fin m => η j=true)))

theorem signCount_false_add_true {n : ℕ} (ε : Fin n → Sign) :
    signCount ε false+signCount ε true=n := by
  classical
  have he : Finset.univ.filter (fun i => ε i=true) =
      Finset.univ.filter (fun i => ¬ε i=false) := by ext i; cases ε i <;> simp
  unfold signCount
  rw [he,Finset.filter_card_add_filter_neg_card_eq_card,Finset.card_univ,Fintype.card_fin]

theorem crossSamePairs_sub_oppositePairs_int {q : ℕ} (ε η : Fin q → Sign) :
    ((crossSamePairs ε η).card:ℤ)-
      ((oppositePairs ε).card+(oppositePairs η).card:ℕ) =
        ((signCount ε false:ℤ)-(signCount η true:ℤ))^2 := by
  have he : (signCount ε false:ℤ)+(signCount ε true:ℤ)=q := by
    exact_mod_cast signCount_false_add_true ε
  have hh : (signCount η false:ℤ)+(signCount η true:ℤ)=q := by
    exact_mod_cast signCount_false_add_true η
  rw [card_crossSamePairs,card_oppositePairs,card_oppositePairs]
  push_cast
  have h1 : (signCount ε true:ℤ)=(q:ℤ)-(signCount ε false:ℤ) := by omega
  have h2 : (signCount η false:ℤ)=(q:ℤ)-(signCount η true:ℤ) := by omega
  rw [h1,h2]
  ring

theorem oppositePairs_add_le_crossSamePairs {q : ℕ} (ε η : Fin q → Sign) :
    (oppositePairs ε).card+(oppositePairs η).card≤(crossSamePairs ε η).card := by
  have h := crossSamePairs_sub_oppositePairs_int ε η
  have hp := sq_nonneg ((signCount ε false:ℤ)-(signCount η true:ℤ))
  omega

theorem crossSamePairs_degree_square {q : ℕ} (ε η : Fin q → Sign) :
    (((crossSamePairs ε η).card-((oppositePairs ε).card+(oppositePairs η).card):ℕ):ℤ) =
      ((signCount ε false:ℤ)-(signCount η true:ℤ))^2 := by
  rw [Nat.cast_sub (oppositePairs_add_le_crossSamePairs ε η)]
  exact crossSamePairs_sub_oppositePairs_int ε η

end BourgadeHuang.CMS
