import GaussianWave.BS.Reused.Entropy.CountableShannon

/-! Literal countable pushforward masses and entropy data processing. -/
noncomputable section
open scoped BigOperators Classical Topology

namespace GaussianWave.BS.Reused.Entropy

variable {A B C : Type*}

def countablePush (p : A → ℝ) (f : A → B) (b : B) : ℝ :=
  ∑' a : {a : A // f a = b},p a.val

theorem countablePush_nonneg (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (f : A → B) (b : B) :
    0 ≤ countablePush p f b := tsum_nonneg (fun a => hp a.val)

theorem countablePush_hasSum (p : A → ℝ) (hsum : HasSum p 1) (f : A → B) :
    HasSum (countablePush p f) 1 := hsum.tsum_fiberwise f

theorem countablePush_id (p : A → ℝ) : countablePush p id = p := by
  funext a
  unfold countablePush
  apply tsum_eq_single (⟨a,rfl⟩ : {a' : A // id a' = a})
  intro b hb
  exact False.elim (hb (Subtype.ext b.property))

def composedFiberEquiv (f : A → B) (g : B → C) (c : C) :
    (Σ b : {b : B // g b = c},{a : A // f a = b.val}) ≃ {a : A // g (f a) = c} where
  toFun z := ⟨z.2.val,by rw [z.2.property]; exact z.1.property⟩
  invFun a := ⟨⟨f a.val,a.property⟩,⟨a.val,rfl⟩⟩
  left_inv z := by
    rcases z with ⟨⟨b,hb⟩,⟨a,ha⟩⟩
    dsimp at ha
    subst b
    rfl
  right_inv a := Subtype.ext rfl

theorem countablePush_comp (p : A → ℝ) (hp : Summable p) (f : A → B) (g : B → C) :
    countablePush (countablePush p f) g = countablePush p (g ∘ f) := by
  funext c
  let e := composedFiberEquiv f g c
  have hs : Summable (fun z : Σ b : {b : B // g b = c},{a : A // f a = b.val} => p z.2.val) :=
    e.summable_iff.mpr (hp.subtype (fun a => g (f a) = c))
  change (∑' b : {b : B // g b = c},∑' a : {a : A // f a = b.val},p a.val) = _
  rw [← hs.tsum_sigma]
  exact e.tsum_eq (fun a : {a : A // g (f a) = c} => p a.val)

theorem negMulLog_tsum_le_tsum (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (hp1 : ∀ a,p a ≤ 1)
    (hs : Summable p) (hH : Summable (fun a => Real.negMulLog (p a))) :
    Real.negMulLog (∑' a,p a) ≤ ∑' a,Real.negMulLog (p a) := by
  have hfinite (s : Finset A) : Real.negMulLog (∑ a ∈ s,p a) ≤ ∑ a ∈ s,Real.negMulLog (p a) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha,Finset.sum_insert ha]
      exact (Finite.negMulLog_add_le (hp a) (Finset.sum_nonneg (fun a ha => hp a))).trans (add_le_add_left ih _)
  have hlim := (Real.continuous_negMulLog.tendsto (∑' a,p a)).comp hs.hasSum
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun s => (hfinite s).trans
    (hH.sum_le_tsum s (fun a ha => Real.negMulLog_nonneg (hp a) (hp1 a))))

theorem entropy_push_fiber_bound (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (hsum : HasSum p 1)
    (hH : Summable (fun a => Real.negMulLog (p a))) (f : A → B) (b : B) :
    Real.negMulLog (countablePush p f b) ≤ ∑' a : {a : A // f a = b},Real.negMulLog (p a.val) :=
  negMulLog_tsum_le_tsum _ (fun a => hp a.val) (fun a => mass_le_one_of_hasSum p hp hsum a.val)
    (hsum.summable.subtype _) (hH.subtype _)

theorem summable_entropy_countablePush (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (hsum : HasSum p 1)
    (hH : Summable (fun a => Real.negMulLog (p a))) (f : A → B) :
    Summable (fun b => Real.negMulLog (countablePush p f b)) := by
  have hpush := countablePush_hasSum p hsum f
  have hnonneg := countablePush_nonneg p hp f
  apply Summable.of_nonneg_of_le
    (fun b => Real.negMulLog_nonneg (hnonneg b) (mass_le_one_of_hasSum _ hnonneg hpush b))
    (entropy_push_fiber_bound p hp hsum hH f)
    (hH.hasSum.tsum_fiberwise f).summable

theorem countableEntropy_push_le (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (hsum : HasSum p 1)
    (hH : Summable (fun a => Real.negMulLog (p a))) (f : A → B) :
    countableEntropy (countablePush p f) ≤ countableEntropy p := by
  have h := Summable.tsum_le_tsum (entropy_push_fiber_bound p hp hsum hH f)
    (summable_entropy_countablePush p hp hsum hH f) (hH.hasSum.tsum_fiberwise f).summable
  exact h.trans_eq (hH.hasSum.tsum_fiberwise f).tsum_eq

theorem countableEntropy_push_eq_of_leftInverse (p : A → ℝ)
    (hp : ∀ a,0 ≤ p a) (hsum : HasSum p 1) (hH : Summable (fun a => Real.negMulLog (p a)))
    (f : A → B) (g : B → A) (hgf : Function.LeftInverse g f) :
    countableEntropy (countablePush p f) = countableEntropy p := by
  apply le_antisymm (countableEntropy_push_le p hp hsum hH f)
  have h := countableEntropy_push_le (countablePush p f) (countablePush_nonneg p hp f)
    (countablePush_hasSum p hsum f) (summable_entropy_countablePush p hp hsum hH f) g
  rw [countablePush_comp p hsum.summable f g] at h
  have he : g ∘ f = id := funext hgf
  rwa [he,countablePush_id] at h

end GaussianWave.BS.Reused.Entropy
