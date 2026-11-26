import Mathlib

/-! An exact permutation split using the actual `Fin.succAbove` unused-port
enumeration, matching the graph-cover sampler. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS

/-- Insert the first image and an arbitrary permutation of unused ports. -/
def portPermFromFirst {q : ℕ} (p : Fin (q+1)) (ρ : Equiv.Perm (Fin q)) : Equiv.Perm (Fin (q+1)) :=
  (finSuccEquiv' 0).trans ((Equiv.optionCongr ρ).trans (finSuccEquiv' p).symm)

@[simp] theorem portPermFromFirst_zero {q : ℕ} (p : Fin (q+1)) (ρ : Equiv.Perm (Fin q)) :
    portPermFromFirst p ρ 0=p := by simp [portPermFromFirst]

@[simp] theorem portPermFromFirst_succ {q : ℕ} (p : Fin (q+1)) (ρ : Equiv.Perm (Fin q)) (j : Fin q) :
    portPermFromFirst p ρ j.succ=p.succAbove (ρ j) := by
  have h : (finSuccEquiv' (0 : Fin (q+1))) j.succ=some j := by
    simpa only [Fin.succAbove_zero] using finSuccEquiv'_succAbove (0 : Fin (q+1)) j
  simp [portPermFromFirst,h]

/-- Delete the first input and its image from an actual permutation. -/
def portPermDeleteFirst {q : ℕ} (σ : Equiv.Perm (Fin (q+1))) : Equiv.Perm (Fin q) :=
  (finSuccAboveEquiv (0 : Fin (q+1))).trans
    ((σ.subtypeEquiv (fun j => by constructor <;> intro h he <;> apply h <;>
      first | exact σ.injective he | exact congrArg σ he)).trans
      (finSuccAboveEquiv (σ 0)).symm)

@[simp] theorem portPermDeleteFirst_succAbove {q : ℕ} (σ : Equiv.Perm (Fin (q+1))) (j : Fin q) :
    (σ 0).succAbove (portPermDeleteFirst σ j)=σ j.succ := by
  have h := (finSuccAboveEquiv (σ 0)).apply_symm_apply
    ((σ.subtypeEquiv (fun j => by constructor <;> intro h he <;> apply h <;>
      first | exact σ.injective he | exact congrArg σ he)) ((finSuccAboveEquiv 0) j))
  exact congrArg Subtype.val h

/-- A literal finite seed bijection; no uniform marginal is supplied as a
premise to the subsequent cover-law identity. -/
def portPermutationSplit (q : ℕ) : Equiv.Perm (Fin (q+1)) ≃ Fin (q+1) × Equiv.Perm (Fin q) where
  toFun σ := (σ 0,portPermDeleteFirst σ)
  invFun z := portPermFromFirst z.1 z.2
  left_inv σ := by
    ext j
    induction j using Fin.cases with
    | zero => simp
    | succ j => simp
  right_inv z := by
    rcases z with ⟨p,ρ⟩
    apply Prod.ext
    · simp
    · apply Equiv.ext
      intro j
      change portPermDeleteFirst (portPermFromFirst p ρ) j=ρ j
      apply Fin.succAbove_right_injective (p := p)
      have h := portPermDeleteFirst_succAbove (portPermFromFirst p ρ) j
      simpa only [portPermFromFirst_zero,portPermFromFirst_succ] using h

end GaussianWave.BS
