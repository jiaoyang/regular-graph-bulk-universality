import GeneralizedBulk.Graph.ColorSampling
import GeneralizedBulk.Matrix.CoordinateCompression

/-! Actual real coordinate selectors and lossless finite vector color codes
for whole configurations, sampled stars, and sampled oriented edges. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration
open ColorProfiles Entropy

def starVertexSelection {N d : ℕ} (G : RegularGraph N d) (z : Fin N × Equiv.Perm (Fin d)) : Fin (d+1) → Fin N :=
  Fin.cases z.1 (fun j => graphNeighbor G z.1 (z.2.symm j))

theorem starVertexSelection_injective {N d : ℕ} (G : RegularGraph N d) (z : Fin N × Equiv.Perm (Fin d)) :
    Function.Injective (starVertexSelection G z) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro h; rfl
    · intro h
      exact False.elim ((canonicalPortLabeling G z.1 (z.2.symm j)).property.ne h)
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact False.elim ((canonicalPortLabeling G z.1 (z.2.symm i)).property.ne' h)
    · intro h
      have he : z.2.symm i = z.2.symm j := (canonicalPortLabeling G z.1).injective (Subtype.ext h)
      exact congrArg Fin.succ (z.2.symm.injective he)

def edgeVertexSelection {N d : ℕ} (G : RegularGraph N d) (z : Fin N × Fin d) (j : Fin 2) : Fin N :=
  if j = 0 then z.1 else graphNeighbor G z.1 z.2

theorem edgeVertexSelection_injective {N d : ℕ} (G : RegularGraph N d) (z : Fin N × Fin d) :
    Function.Injective (edgeVertexSelection G z) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim ((canonicalPortLabeling G z.1 z.2).property.ne (by simpa [edgeVertexSelection] using h))
  · exact False.elim ((canonicalPortLabeling G z.1 z.2).property.ne' (by simpa [edgeVertexSelection] using h))
  · rfl

def flatSelection {k L N : ℕ} (e : Fin L → Fin N) (t : Fin (k*L)) : Fin k × Fin N :=
  ((finProdFinEquiv.symm t).1,e (finProdFinEquiv.symm t).2)

theorem flatSelection_injective {k L N : ℕ} (e : Fin L → Fin N) (he : Function.Injective e) :
    Function.Injective (flatSelection (k := k) e) := by
  intro a b h
  apply finProdFinEquiv.symm.injective
  have hf : (finProdFinEquiv.symm a).1 = (finProdFinEquiv.symm b).1 :=
    congrArg (fun z : Fin k × Fin N => z.1) h
  have hs : e (finProdFinEquiv.symm a).2 = e (finProdFinEquiv.symm b).2 :=
    congrArg (fun z : Fin k × Fin N => z.2) h
  exact Prod.ext hf (he hs)

def bundleColorEquiv {k q : ℕ} {B : Type*} (e : (Fin k → B) ≃ Fin q) (L : ℕ) :
    (Fin k × Fin L → B) ≃ (Fin L → Fin q) where
  toFun w := fun j => e (fun r => w (r,j))
  invFun s := fun i => e.symm (s i.2) i.1
  left_inv w := by funext i; exact congrFun (e.symm_apply_apply (fun r => w (r,i.2))) i.1
  right_inv s := by funext j; exact e.apply_symm_apply (s j)

def flatWordEquiv (k L : ℕ) (B : Type*) : (Fin (k*L) → B) ≃ (Fin k × Fin L → B) :=
  Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl B)

def flatBundleColorEquiv {k q : ℕ} {B : Type*} (e : (Fin k → B) ≃ Fin q) (L : ℕ) :
    (Fin (k*L) → B) ≃ (Fin L → Fin q) := (flatWordEquiv k L B).trans (bundleColorEquiv e L)

theorem flatBundleColorEquiv_apply {k q L : ℕ} {B : Type*} (e : (Fin k → B) ≃ Fin q)
    (w : Fin (k*L) → B) (j : Fin L) :
    flatBundleColorEquiv e L w j = e (fun r => w (finProdFinEquiv (r,j))) := rfl

theorem flatBundleColorEquiv_selected {k q L N : ℕ} {B : Type*} (e : (Fin k → B) ≃ Fin q)
    (J : ℝ → B) (s : Fin L → Fin N) (x : Fin k × Fin N → ℝ) :
    flatBundleColorEquiv e L (fun t => J (x (flatSelection s t))) =
      fun j => quantizedVertexColor e J x (s j) := by
  funext j
  simp only [flatBundleColorEquiv_apply,flatSelection,Equiv.symm_apply_apply,quantizedVertexColor]

theorem flatBundleColorEquiv_star {k q N d : ℕ} {B : Type*} (e : (Fin k → B) ≃ Fin q)
    (J : ℝ → B) (G : RegularGraph N d) (z : Fin N × Equiv.Perm (Fin d))
    (x : Fin k × Fin N → ℝ) :
    flatBundleColorEquiv e (d+1) (fun t => J (x (flatSelection (starVertexSelection G z) t))) =
      sampledStarWord G (quantizedVertexColor e J x) z := by
  rw [flatBundleColorEquiv_selected]
  rw [sampledStarWord,← starWordPerm_symm]
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [starVertexSelection,starWordPerm,neighborSlotPerm,orderedStarWord]

def pairColorEquiv {q : ℕ} : (Fin 2 → Fin q) ≃ (Fin q × Fin q) where
  toFun s := (s 0,s 1)
  invFun ab := ![ab.1,ab.2]
  left_inv s := by funext i; fin_cases i <;> rfl
  right_inv ab := rfl

theorem flatBundleColorEquiv_edge {k q N d : ℕ} {B : Type*} (e : (Fin k → B) ≃ Fin q)
    (J : ℝ → B) (G : RegularGraph N d) (z : Fin N × Fin d) (x : Fin k × Fin N → ℝ) :
    pairColorEquiv (flatBundleColorEquiv e 2 (fun t => J (x (flatSelection (edgeVertexSelection G z) t)))) =
      sampledEdgeWord G (quantizedVertexColor e J x) z := by
  rw [flatBundleColorEquiv_selected]
  simp [pairColorEquiv,edgeVertexSelection,sampledEdgeWord]

end GeneralizedBulk.Graph.Configuration
