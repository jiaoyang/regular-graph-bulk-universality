import GaussianWave.BS.Lower.ApproximateCodingEntropy

/-! Invariant codes need only recover stabilizer orbits when markers are
distinct. Extra ambiguity on repeated-marker inputs is bounded explicitly. -/
noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

variable {G A B : Type*} [Group G] [Fintype G] [Fintype A] [Fintype B] [MulAction G A]

abbrev FiniteOrbitQuotient (G A : Type*) [Group G] [MulAction G A] := Quotient (MulAction.orbitRel G A)

def canonicalOrbitCode (G : Type*) [Group G] {A : Type*} [MulAction G A] (a : A) :
    FiniteOrbitQuotient G A := Quotient.mk'' a

theorem canonicalOrbitCode_eq_iff (a a' : A) :
    canonicalOrbitCode G a = canonicalOrbitCode G a' ↔ a ∈ MulAction.orbit G a' := by
  constructor
  · intro h; exact Quotient.exact h
  · intro h; exact Quotient.sound h

theorem canonicalOrbitCode_surjective : Function.Surjective (canonicalOrbitCode G : A → FiniteOrbitQuotient G A) :=
  Quotient.mk''_surjective

/-- Every actual group-invariant finite code descends to the actual orbit
quotient. No entropy or inverse-code conclusion is assumed. -/
def orbitCodeDescend (f : A → B) (hinv : ∀ (g : G) a,f (g • a) = f a) : FiniteOrbitQuotient G A → B :=
  Quotient.lift f (fun a a' h => by
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp h
    rw [← hg]
    exact hinv g a')

@[simp] theorem orbitCodeDescend_canonical (f : A → B) (hinv : ∀ (g : G) a,f (g • a) = f a) (a : A) :
    orbitCodeDescend f hinv (canonicalOrbitCode G a) = f a := rfl

/-- Repeated-marker ambiguity beyond a true orbit quotient costs at most
its probability mass times the logarithm of the whole finite input alphabet. -/
theorem entropy_orbit_coarsening_bound (f : A → B)
    (hfinv : ∀ (g : G) a,f (g • a) = f a) (p : A → ℝ) (hp : ∀ a,0 ≤ p a)
    (good : A → Prop) (hrecover : ∀ a,good a → ∀ a',f a' = f a → a' ∈ MulAction.orbit G a) :
    0 ≤ entropy (pushMass (canonicalOrbitCode G) p)-entropy (pushMass f p) ∧
      entropy (pushMass (canonicalOrbitCode G) p)-entropy (pushMass f p) ≤
        (∑ a,if good a then 0 else p a)*Real.log (Fintype.card A) := by
  let g := orbitCodeDescend f hfinv
  have he : g ∘ canonicalOrbitCode G = f := by funext a; rfl
  have hrec : ∀ a,good a → ∀ a',g (canonicalOrbitCode G a') = g (canonicalOrbitCode G a) →
      canonicalOrbitCode G a' = canonicalOrbitCode G a := by
    intro a ha a' h
    exact (canonicalOrbitCode_eq_iff a' a).mpr (hrecover a ha a' h)
  have h := entropy_coding_coarsening_bound (canonicalOrbitCode G) canonicalOrbitCode_surjective g p hp good hrec
  simpa only [he] using h

/-- Honest two-sided error for an invariant coding that recovers group
orbits only on a good free-action set. The alphabet factor in the lower
bound is essential for actual overlapping-neighborhood tuple codes. -/
theorem entropy_good_orbit_coding_error_bound (f : A → B)
    (hfinv : ∀ (g : G) a,f (g • a) = f a) (p : A → ℝ)
    (hp : ∀ a,0 ≤ p a) (hs : ∑ a,p a = 1) (hpinv : ∀ (g : G) a,p (g • a) = p a)
    (good : A → Prop) (hfree : ∀ a,good a → Function.Injective (fun g : G => g • a))
    (hrecover : ∀ a,good a → ∀ a',f a' = f a → a' ∈ MulAction.orbit G a) :
    -(∑ a,if good a then 0 else p a)*Real.log (Fintype.card A) ≤
        Real.log (Fintype.card G)-(entropy p-entropy (pushMass f p)) ∧
      Real.log (Fintype.card G)-(entropy p-entropy (pushMass f p)) ≤
        (∑ a,if good a then 0 else p a)*Real.log (Fintype.card G) := by
  have horbit := entropy_orbit_coding_defect_bound (canonicalOrbitCode G)
    (fun a a' => canonicalOrbitCode_eq_iff a a') p hp hs hpinv good hfree
  have hcoarse := entropy_orbit_coarsening_bound f hfinv p hp good hrecover
  constructor <;> linarith [horbit.1,horbit.2,hcoarse.1,hcoarse.2]

end GaussianWave.BS.Lower
