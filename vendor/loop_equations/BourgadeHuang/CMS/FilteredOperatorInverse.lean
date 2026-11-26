import BourgadeHuang.CMS.ComplexVolterraOperators
import Mathlib.RingTheory.Nilpotent.Basic

/-! Finite triangular elimination in the actual Banach space of bounded
continuous functions. No smallness is required for the strictly triangular
part; its inverse is a finite polynomial. -/
noncomputable section
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS

section Filtration
variable {X J : Type*} [TopologicalSpace X] [Fintype J]

/-- Vanishing of all components below a finite degree. -/
def VanishesBelow (degree : J → ℕ) (k : ℕ) (f : X →ᵇ (J → ℂ)) : Prop :=
  ∀x i,degree i<k → f x i=0

/-- A strictly triangular operator raises the vanishing filtration. -/
def RaisesDegree (degree : J → ℕ)
    (B : (X →ᵇ (J → ℂ)) →L[ℂ] (X →ᵇ (J → ℂ))) : Prop :=
  ∀k f,VanishesBelow degree k f → VanishesBelow degree (k+1) (B f)

theorem vanishesBelow_pow {degree : J → ℕ}
    {B : (X →ᵇ (J → ℂ)) →L[ℂ] (X →ᵇ (J → ℂ))}
    (hB : RaisesDegree degree B) (f : X →ᵇ (J → ℂ)) (n : ℕ) :
    VanishesBelow degree n ((B^n) f) := by
  induction n with
  | zero => intro x i hi; omega
  | succ n ih =>
      simpa only [pow_succ',ContinuousLinearMap.mul_apply] using hB n ((B^n) f) ih

theorem pow_eq_zero_of_raisesDegree {degree : J → ℕ}
    {B : (X →ᵇ (J → ℂ)) →L[ℂ] (X →ᵇ (J → ℂ))}
    (hB : RaisesDegree degree B) {H : ℕ} (hH : ∀i,degree i<H) : B^H=0 := by
  ext f x i
  exact vanishesBelow_pow hB f H x i (hH i)

end Filtration

section PolynomialInverse
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- The finite geometric polynomial used to eliminate the triangular part. -/
def triangularInverse (B : E →L[ℂ] E) (H : ℕ) : E →L[ℂ] E :=
  ∑k∈Finset.range H,B^k

theorem triangularInverse_mul {B : E →L[ℂ] E} {H : ℕ} (hB : B^H=0) :
    triangularInverse B H*(1-B)=1 := by
  have h := geom_sum_mul B H
  rw [hB,zero_sub] at h
  simpa only [triangularInverse,← mul_neg,neg_sub,neg_neg] using congrArg Neg.neg h

theorem mul_triangularInverse {B : E →L[ℂ] E} {H : ℕ} (hB : B^H=0) :
    (1-B)*triangularInverse B H=1 := by
  have h := mul_geom_sum B H
  rw [hB,zero_sub] at h
  simpa only [triangularInverse,← neg_mul,neg_sub,neg_neg] using congrArg Neg.neg h

theorem triangularInverse_eq_inverse {B : E →L[ℂ] E} {H : ℕ} (hB : B^H=0) :
    triangularInverse B H=Ring.inverse (1-B) := by
  have hu : IsUnit (1-B) := (show IsNilpotent B from ⟨H,hB⟩).isUnit_one_sub
  calc
    triangularInverse B H=triangularInverse B H*((1-B)*Ring.inverse (1-B)) := by
      rw [Ring.mul_inverse_cancel _ hu,mul_one]
    _=(triangularInverse B H*(1-B))*Ring.inverse (1-B) := by rw [mul_assoc]
    _=Ring.inverse (1-B) := by rw [triangularInverse_mul hB,one_mul]

theorem analyticAt_triangularInverse {B : P → E →L[ℂ] E} {x : P}
    (hB : AnalyticAt ℂ B x) (H : ℕ) :
    AnalyticAt ℂ (fun y => triangularInverse (B y) H) x := by
  exact Finset.analyticAt_sum _ (fun k _ => hB.pow k)

theorem norm_triangularInverse_le (B : E →L[ℂ] E) (H : ℕ) :
    ‖triangularInverse B H‖≤∑k∈Finset.range H,‖B‖^k := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  cases k with
  | zero => simpa only [pow_zero] using ContinuousLinearMap.norm_id_le (𝕜:=ℂ) (E:=E)
  | succ k => exact norm_pow_le' B (Nat.succ_pos k)

end PolynomialInverse
end BourgadeHuang.CMS
