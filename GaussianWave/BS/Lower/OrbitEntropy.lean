import GaussianWave.BS.Reused.Entropy.FiniteProduct
import GaussianWave.BS.Reused.Entropy.FiniteLawIntegral

/-! Exact entropy loss under invariant finite quotient coding, including
nonfree actions and markers that make the action free with high probability. -/
noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 800000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

section FiniteFibers
variable {A B : Type*} [Fintype A] [Fintype B]

def fiberCard (f : A → B) (b : B) : ℕ := (Finset.univ.filter (fun a => f a = b)).card

/-- Deterministic finite pushforward integration, without probability or
nonnegativity restrictions. -/
theorem sum_pushMass_mul (f : A → B) (p : A → ℝ) (h : B → ℝ) :
    (∑ b,pushMass f p b*h b) = ∑ a,p a*h (f a) := by
  unfold pushMass
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ b,∑ a ∈ Finset.univ.filter (fun a => f a = b),p a*h (f a) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := f) (fun a _ => Finset.mem_univ _) (fun a => p a*h (f a))

/-- A mass function constant on every finite coding fiber has exactly
uniform conditional masses within each nonempty fiber. -/
theorem entropy_uniform_fibers (f : A → B) (p : A → ℝ)
    (hconst : ∀ a a',f a = f a' → p a = p a') :
    entropy p = entropy (pushMass f p)+∑ b,pushMass f p b*Real.log (fiberCard f b) := by
  have hfiber (b : B) :
      (∑ a ∈ Finset.univ.filter (fun a => f a = b),Real.negMulLog (p a)) =
        Real.negMulLog (pushMass f p b)+pushMass f p b*Real.log (fiberCard f b) := by
    let S := Finset.univ.filter (fun a => f a = b)
    by_cases hS : S.Nonempty
    · obtain ⟨a0,ha0⟩ := hS
      have hfa0 : f a0 = b := (Finset.mem_filter.mp ha0).2
      have hp (a : A) (ha : a ∈ S) : p a = p a0 :=
        hconst a a0 ((Finset.mem_filter.mp ha).2.trans hfa0.symm)
      have hsum : pushMass f p b = (S.card : ℝ)*p a0 := by
        unfold pushMass
        change (∑ a ∈ S,p a) = _
        simp_rw [Finset.sum_congr rfl (fun a ha => hp a ha)]
        simp
      have hent : (∑ a ∈ S,Real.negMulLog (p a)) = (S.card : ℝ)*Real.negMulLog (p a0) := by
        calc
          _ = ∑ _a ∈ S,Real.negMulLog (p a0) := Finset.sum_congr rfl (fun a ha => congrArg Real.negMulLog (hp a ha))
          _ = _ := by simp
      change (∑ a ∈ S,Real.negMulLog (p a)) = _
      rw [hent,hsum]
      change _ = Real.negMulLog ((S.card : ℝ)*p a0)+((S.card : ℝ)*p a0)*Real.log S.card
      rw [Real.negMulLog_mul]
      unfold Real.negMulLog
      ring
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      have hp : pushMass f p b = 0 := by change (∑ a ∈ S,p a) = 0; rw [he]; simp
      change (∑ a ∈ S,Real.negMulLog (p a)) = _
      rw [he,hp]
      simp
  calc
    _ = ∑ b,∑ a ∈ Finset.univ.filter (fun a => f a = b),Real.negMulLog (p a) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
        (g := f) (fun a _ => Finset.mem_univ _) (fun a => Real.negMulLog (p a))
    _ = ∑ b,(Real.negMulLog (pushMass f p b)+pushMass f p b*Real.log (fiberCard f b)) :=
      Finset.sum_congr rfl (fun b _ => hfiber b)
    _ = _ := by rw [Finset.sum_add_distrib]; rfl

/-- The same exact loss written as expectation under the original law. -/
theorem entropy_uniform_fibers_loss (f : A → B) (p : A → ℝ)
    (hconst : ∀ a a',f a = f a' → p a = p a') :
    entropy p-entropy (pushMass f p) = ∑ a,p a*Real.log (fiberCard f (f a)) := by
  have h := entropy_uniform_fibers f p hconst
  rw [sum_pushMass_mul] at h
  linarith

end FiniteFibers
section FiniteOrbits
variable {G A B : Type*} [Group G] [Fintype G] [Fintype A] [Fintype B] [MulAction G A]

/-- Orbit size is independent of any chosen finite enumeration. -/
def orbitCard (G : Type*) [Group G] [Fintype G] {A : Type*} [Fintype A] [MulAction G A] (a : A) : ℕ :=
  Nat.card (MulAction.orbit G a)

def orbitFiberEquiv (f : A → B)
    (hcode : ∀ a a',f a = f a' ↔ a ∈ MulAction.orbit G a') (a : A) :
    {x : A // f x = f a} ≃ MulAction.orbit G a where
  toFun x := ⟨x.val,(hcode x.val a).mp x.property⟩
  invFun x := ⟨x.val,(hcode x.val a).mpr x.property⟩
  left_inv x := rfl
  right_inv x := rfl

theorem fiberCard_eq_orbitCard (f : A → B)
    (hcode : ∀ a a',f a = f a' ↔ a ∈ MulAction.orbit G a') (a : A) :
    fiberCard f (f a) = orbitCard G a := by
  rw [fiberCard,← Fintype.card_subtype,Fintype.card_eq_nat_card]
  exact Nat.card_congr (orbitFiberEquiv f hcode a)

theorem orbitCard_pos (a : A) : 0 < orbitCard G a := by
  unfold orbitCard
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_pos_iff.mpr ⟨⟨a,MulAction.mem_orbit_self a⟩⟩

def groupToOrbit (a : A) (g : G) : MulAction.orbit G a := ⟨g • a,MulAction.mem_orbit a g⟩

theorem groupToOrbit_surjective (a : A) : Function.Surjective (groupToOrbit (G := G) a) := by
  intro x
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp x.property
  exact ⟨g,Subtype.ext hg⟩

theorem orbitCard_le_group (a : A) : orbitCard G a ≤ Fintype.card G := by
  have h := Fintype.card_le_of_surjective (groupToOrbit (G := G) a) (groupToOrbit_surjective a)
  simpa only [orbitCard,Nat.card_eq_fintype_card] using h

theorem orbitCard_eq_group_of_free (a : A) (hfree : Function.Injective (fun g : G => g • a)) :
    orbitCard G a = Fintype.card G := by
  let e : G ≃ MulAction.orbit G a := Equiv.ofBijective (groupToOrbit a)
    ⟨fun g h he => hfree (congrArg Subtype.val he),groupToOrbit_surjective a⟩
  simpa only [orbitCard,Nat.card_eq_fintype_card] using (Fintype.card_congr e).symm

/-- Invariance of actual masses supplies uniform conditional masses on each
orbit, so the exact coding entropy loss is the expected log-orbit size. -/
theorem entropy_orbit_coding_loss (f : A → B)
    (hcode : ∀ a a',f a = f a' ↔ a ∈ MulAction.orbit G a') (p : A → ℝ)
    (hinv : ∀ (g : G) a,p (g • a) = p a) :
    entropy p-entropy (pushMass f p) = ∑ a,p a*Real.log (orbitCard G a) := by
  have hc : ∀ a a',f a = f a' → p a = p a' := by
    intro a a' h
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp ((hcode a a').mp h)
    rw [← hg]
    exact hinv g a'
  have h := entropy_uniform_fibers_loss f p hc
  simpa only [fiberCard_eq_orbitCard f hcode] using h

/-- A finite invariant probability law loses exactly `log |G|` under free
orbit coding, up to at most the nonfree mass times `log |G|`. -/
theorem entropy_orbit_coding_defect_bound (f : A → B)
    (hcode : ∀ a a',f a = f a' ↔ a ∈ MulAction.orbit G a') (p : A → ℝ)
    (hp : ∀ a,0 ≤ p a) (hs : ∑ a,p a = 1) (hinv : ∀ (g : G) a,p (g • a) = p a)
    (good : A → Prop) (hfree : ∀ a,good a → Function.Injective (fun g : G => g • a)) :
    0 ≤ Real.log (Fintype.card G)-(entropy p-entropy (pushMass f p)) ∧
      Real.log (Fintype.card G)-(entropy p-entropy (pushMass f p)) ≤
        (∑ a,if good a then 0 else p a)*Real.log (Fintype.card G) := by
  rw [entropy_orbit_coding_loss f hcode p hinv]
  let L := Real.log (Fintype.card G)
  let D (a : A) := L-Real.log (orbitCard G a)
  have hlog0 (a : A) : 0 ≤ Real.log (orbitCard G a) :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (orbitCard_pos (G := G) a))))
  have hlogle (a : A) : Real.log (orbitCard G a) ≤ L :=
    Real.log_le_log (by exact_mod_cast orbitCard_pos (G := G) a)
      (by exact_mod_cast orbitCard_le_group (G := G) a)
  have hD0 (a : A) : 0 ≤ D a := sub_nonneg.mpr (hlogle a)
  have hDle (a : A) : D a ≤ L := by dsimp [D]; linarith [hlog0 a]
  have hDgood (a : A) (ha : good a) : D a = 0 := by
    dsimp [D,L]
    rw [orbitCard_eq_group_of_free a (hfree a ha),sub_self]
  have he : L-(∑ a,p a*Real.log (orbitCard G a)) = ∑ a,p a*D a := by
    simp only [D,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul]
  change 0 ≤ L-(∑ a,p a*Real.log (orbitCard G a)) ∧ _
  rw [he]
  constructor
  · exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp a) (hD0 a))
  · calc
      _ ≤ ∑ a,(if good a then 0 else p a)*L := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases hgood : good a
        · simp only [if_pos hgood,hDgood a hgood,mul_zero,zero_mul,le_refl]
        · simp only [if_neg hgood]
          exact mul_le_mul_of_nonneg_left (hDle a) (hp a)
      _ = _ := (Finset.sum_mul _ _ _).symm

end FiniteOrbits

section FreeMarkers
variable {G V F M : Type*} [Group G] [MulAction G V] [FaithfulSMul G V]

/-- Distinct vertex markers make the reindexing action free, even when the
original colors contain arbitrary symmetries. -/
theorem reindexing_free_of_injective_markers (lab : V → F × M)
    (hinj : Function.Injective (fun v => (lab v).2)) :
    Function.Injective (fun g : G => fun v => lab (g⁻¹ • v)) := by
  intro g h he
  apply inv_injective
  apply eq_of_smul_eq_smul (α := V)
  intro v
  exact hinj (congrArg Prod.snd (congrFun he v))

end FreeMarkers
end GaussianWave.BS.Lower
