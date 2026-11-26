import GaussianWave.BS.Lower.OrbitEntropy

/-! Entropy comparison for a coding that recovers a finer finite coding on
a high-probability good set. This handles repeated-marker ambiguity honestly. -/
noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 800000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

theorem pushMass_as_sum (f : A → B) (p : A → ℝ) (b : B) :
    pushMass f p b = ∑ a,p a*(if f a = b then 1 else 0) := by
  simp only [pushMass,Finset.sum_filter,mul_ite,mul_one,mul_zero]

theorem pushMass_comp (f : A → B) (g : B → C) (p : A → ℝ) :
    pushMass g (pushMass f p) = pushMass (g ∘ f) p := by
  funext c
  rw [pushMass_as_sum,sum_pushMass_mul,pushMass_as_sum]
  rfl

/-- Deterministic finite coding cannot increase Shannon entropy. This uses
only nonnegative masses, and also covers empty fibers and zero masses. -/
theorem entropy_pushMass_le (f : A → B) (p : A → ℝ) (hp : ∀ a,0 ≤ p a) :
    entropy (pushMass f p) ≤ entropy p := by
  have hfiber (b : B) : Real.negMulLog (pushMass f p b) ≤
      ∑ a ∈ Finset.univ.filter (fun a => f a = b),Real.negMulLog (p a) := by
    have h := entropy_lower_total (fun a : (Finset.univ.filter (fun a : A => f a = b)) => p a.val) (fun a => hp a.val)
    simpa only [entropy,pushMass,Finset.sum_coe_sort (Finset.univ.filter (fun a : A => f a = b)) p,
      Finset.sum_coe_sort (Finset.univ.filter (fun a : A => f a = b)) (fun a => Real.negMulLog (p a))] using h
  calc
    _ ≤ ∑ b,∑ a ∈ Finset.univ.filter (fun a => f a = b),Real.negMulLog (p a) :=
      Finset.sum_le_sum (fun b _ => hfiber b)
    _ = _ := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := f) (fun a _ => Finset.mem_univ _) (fun a => Real.negMulLog (p a))

/-- A coarser coding loses no more than the bad-set mass times `log |A|`
when it recovers the finer coding on every good input. The finer coding is
surjective so unattained dummy alphabet values cause no spurious fiber loss. -/
theorem entropy_coding_coarsening_bound
    (h : A → C) (hsurj : Function.Surjective h) (g : C → B)
    (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (good : A → Prop)
    (hrecover : ∀ a,good a → ∀ a',g (h a') = g (h a) → h a' = h a) :
    0 ≤ entropy (pushMass h p)-entropy (pushMass (g ∘ h) p) ∧
      entropy (pushMass h p)-entropy (pushMass (g ∘ h) p) ≤
        (∑ a,if good a then 0 else p a)*Real.log (Fintype.card A) := by
  let q := pushMass h p
  have hq : ∀ c,0 ≤ q c := pushMass_nonneg h p hp
  have hlower := entropy_pushMass_le g q hq
  have hupper := entropy_partition_bound g q hq
  change entropy q ≤ entropy (pushMass g q)+∑ b,pushMass g q b*Real.log (fiberCard g b) at hupper
  have hcard (a : A) : fiberCard g (g (h a)) ≤ Fintype.card A :=
    (Finset.card_filter_le _ _).trans (by
      simpa only [Finset.card_univ] using Fintype.card_le_of_surjective h hsurj)
  have hpos (a : A) : 0 < fiberCard g (g (h a)) := by
    exact Finset.card_pos.mpr ⟨h a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have hlog (a : A) : Real.log (fiberCard g (g (h a))) ≤ Real.log (Fintype.card A) :=
    Real.log_le_log (by exact_mod_cast hpos a) (by exact_mod_cast hcard a)
  have hgood (a : A) (ha : good a) : fiberCard g (g (h a)) = 1 := by
    have he : Finset.univ.filter (fun c : C => g c = g (h a)) = {h a} := by
      ext c
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      constructor
      · intro hc
        obtain ⟨a',rfl⟩ := hsurj c
        exact hrecover a ha a' hc
      · intro hc; rw [hc]
    unfold fiberCard
    rw [he,Finset.card_singleton]
  have hsum : (∑ b,pushMass g q b*Real.log (fiberCard g b)) ≤
      (∑ a,if good a then 0 else p a)*Real.log (Fintype.card A) := by
    rw [sum_pushMass_mul]
    change (∑ c,pushMass h p c*Real.log (fiberCard g (g c))) ≤ _
    rw [sum_pushMass_mul]
    calc
      _ ≤ ∑ a,(if good a then 0 else p a)*Real.log (Fintype.card A) := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases hg : good a
        · simp only [if_pos hg,hgood a hg,Nat.cast_one,Real.log_one,mul_zero,zero_mul,le_refl]
        · simp only [if_neg hg]
          exact mul_le_mul_of_nonneg_left (hlog a) (hp a)
      _ = _ := (Finset.sum_mul _ _ _).symm
  rw [← pushMass_comp h g p]
  change 0 ≤ entropy q-entropy (pushMass g q) ∧ _
  constructor
  · exact sub_nonneg.mpr hlower
  · linarith [hupper,hsum]

end GaussianWave.BS.Lower
