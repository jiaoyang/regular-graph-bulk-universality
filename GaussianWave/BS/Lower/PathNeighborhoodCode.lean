import GaussianWave.BS.Lower.LocalRecodingEntropy

/-! Concrete finite neighborhood codes with an alphabet independent of the
graph size. A code records the occurrence of every colored path word of
length at most `R`; it is port-independent and retains the root color. -/
noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000
namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Graph

abbrev BoundedColorWord (A : Type*) (R : ℕ) := Σ n : Fin (R+1),Fin (n.val+1) → A
abbrev PathNeighborhoodCode (A : Type*) (R : ℕ) := BoundedColorWord A R → Bool

def ColoredPathWord {V A : Type*} (H : SimpleGraph V) (R : ℕ) (color : V → A)
    (o : V) (word : BoundedColorWord A R) : Prop :=
  ∃ p : Fin (word.1.val+1) → V,p 0=o ∧
    (∀ j : Fin word.1.val,H.Adj (p j.castSucc) (p j.succ)) ∧ ∀ j,color (p j)=word.2 j

def pathNeighborhoodCode {V A : Type*} (H : SimpleGraph V) (R : ℕ) (color : V → A)
    (o : V) : PathNeighborhoodCode A R := fun word => decide (ColoredPathWord H R color o word)

@[simp] theorem pathNeighborhoodCode_true_iff {V A : Type*} (H : SimpleGraph V) (R : ℕ)
    (color : V → A) (o : V) (word : BoundedColorWord A R) :
    pathNeighborhoodCode H R color o word=true ↔ ColoredPathWord H R color o word := by
  simp only [pathNeighborhoodCode,decide_eq_true_eq]

def zeroColorWord {A : Type*} (R : ℕ) (a : A) : BoundedColorWord A R :=
  ⟨⟨0,by omega⟩,fun _ => a⟩

theorem pathNeighborhoodCode_zero_iff {V A : Type*} (H : SimpleGraph V) (R : ℕ)
    (color : V → A) (o : V) (a : A) :
    pathNeighborhoodCode H R color o (zeroColorWord R a)=true ↔ a=color o := by
  rw [pathNeighborhoodCode_true_iff]
  constructor
  · rintro ⟨p,hp,_,hcolor⟩
    exact ((hcolor 0).symm.trans (congrArg color hp))
  · intro ha
    exact ⟨fun _ => o,rfl,fun j => Fin.elim0 j,fun _ => ha.symm⟩

def pathCodeRootColor {A : Type*} (R : ℕ) (default : A) (code : PathNeighborhoodCode A R) : A :=
  if h : ∃ a,code (zeroColorWord R a)=true then h.choose else default

theorem pathCodeRootColor_decode {V A : Type*} (H : SimpleGraph V) (R : ℕ)
    (color : V → A) (o : V) (default : A) :
    pathCodeRootColor R default (pathNeighborhoodCode H R color o)=color o := by
  have hex : ∃ a,pathNeighborhoodCode H R color o (zeroColorWord R a)=true :=
    ⟨color o,(pathNeighborhoodCode_zero_iff H R color o _).mpr rfl⟩
  simp only [pathCodeRootColor,dif_pos hex]
  exact (pathNeighborhoodCode_zero_iff H R color o _).mp hex.choose_spec

theorem pathTuple_edist_le {V : Type*} (H : SimpleGraph V) (n : ℕ)
    (p : Fin (n+1) → V) (hp : ∀ j : Fin n,H.Adj (p j.castSucc) (p j.succ)) :
    ∀ i : Fin (n+1),H.edist (p 0) (p i) ≤ (i.val : ℕ∞) := by
  refine Fin.induction ?_ (fun i ih => ?_)
  · simp
  · calc
      _ ≤ H.edist (p 0) (p i.castSucc)+H.edist (p i.castSucc) (p i.succ) := SimpleGraph.edist_triangle
      _ ≤ (i.val : ℕ∞)+1 := add_le_add ih (SimpleGraph.edist_eq_one_iff_adj.mpr (hp i)).le
      _ = _ := by simp

theorem pathNeighborhoodCode_local {V A : Type*} (H : SimpleGraph V) (R : ℕ)
    (color color' : V → A) (o : V)
    (hcolor : ∀ v,H.edist o v ≤ (R : ℕ∞) → color v=color' v) :
    pathNeighborhoodCode H R color o=pathNeighborhoodCode H R color' o := by
  have himp (c c' : V → A) (hc : ∀ v,H.edist o v ≤ (R : ℕ∞) → c v=c' v)
      (word : BoundedColorWord A R) : ColoredPathWord H R c o word → ColoredPathWord H R c' o word := by
    rintro ⟨p,hroot,hp,hcword⟩
    refine ⟨p,hroot,hp,fun j => ?_⟩
    have hd : H.edist o (p j) ≤ (R : ℕ∞) := by
      rw [← hroot]
      exact (pathTuple_edist_le H word.1.val p hp j).trans (by exact_mod_cast (by omega : j.val ≤ R))
    exact (hc (p j) hd).symm.trans (hcword j)
  funext word
  simp only [pathNeighborhoodCode]
  congr 1
  exact propext ⟨himp color color' hcolor word,himp color' color (fun v hv => (hcolor v hv).symm) word⟩

/-- The code is invariant under actual rooted graph isomorphisms. -/
theorem pathNeighborhoodCode_graphIso {V W A : Type*} {H : SimpleGraph V} {K : SimpleGraph W}
    (e : H ≃g K) (R : ℕ) (color : V → A) (o : V) :
    pathNeighborhoodCode K R (color ∘ e.symm) (e o)=pathNeighborhoodCode H R color o := by
  funext word
  simp only [pathNeighborhoodCode]
  congr 1
  apply propext
  constructor
  · rintro ⟨p,hroot,hp,hcolor⟩
    exact ⟨fun i => e.symm (p i),by simpa only [hroot,e.symm_apply_apply],
      fun i => e.symm.map_rel_iff.mpr (hp i),hcolor⟩
  · rintro ⟨p,hroot,hp,hcolor⟩
    refine ⟨fun i => e (p i),congrArg e hroot,fun i => e.map_rel_iff.mpr (hp i),?_⟩
    intro i
    simpa only [Function.comp_apply,e.symm_apply_apply] using hcolor i

def pathNeighborhoodPalette (q R : ℕ) := Fintype.card (PathNeighborhoodCode (Fin q) R)

theorem pathNeighborhoodPalette_pos (q R : ℕ) : 0 < pathNeighborhoodPalette q R := by
  letI : Nonempty (PathNeighborhoodCode (Fin q) R) := ⟨fun _ => false⟩
  exact Fintype.card_pos

def pathNeighborhoodRecoding {N d q : ℕ} (G : RegularGraph N d) (R : ℕ)
    (color : Fin N → Fin q) (v : Fin N) : Fin (pathNeighborhoodPalette q R) :=
  Fintype.equivFin (PathNeighborhoodCode (Fin q) R) (pathNeighborhoodCode G.val R color v)

def pathNeighborhoodDecoder (q R : ℕ) (hq : 0 < q) : Fin (pathNeighborhoodPalette q R) → Fin q :=
  fun b => pathCodeRootColor R ⟨0,hq⟩ ((Fintype.equivFin (PathNeighborhoodCode (Fin q) R)).symm b)

theorem pathNeighborhoodRecoding_local {N d q : ℕ} (G : RegularGraph N d) (R : ℕ) :
    IsGraphLocal G R (pathNeighborhoodRecoding G R (q := q)) := by
  intro v c c' hc
  exact congrArg (Fintype.equivFin _) (pathNeighborhoodCode_local G.val R c c' v hc)

theorem pathNeighborhoodRecoding_decode {N d q : ℕ} (G : RegularGraph N d) (R : ℕ) (hq : 0 < q)
    (c : Fin N → Fin q) (v : Fin N) :
    pathNeighborhoodDecoder q R hq (pathNeighborhoodRecoding G R c v)=c v := by
  simp only [pathNeighborhoodDecoder,pathNeighborhoodRecoding,Equiv.symm_apply_apply]
  exact pathCodeRootColor_decode G.val R c v _

end GaussianWave.BS.Lower
