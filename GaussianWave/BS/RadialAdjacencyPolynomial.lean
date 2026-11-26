import GaussianWave.BS.FiniteSupportAdjacency
import GaussianWave.BS.RadialTreeGeometry

/-! Finite adjacency polynomials realize radial kernels on the actual tree.
Their product kernels are radial without an automorphism-transitivity premise. -/
noncomputable section
open scoped BigOperators Classical
namespace GaussianWave.BS

section Operators
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The sphere polynomial, evaluated directly in any endomorphism algebra. -/
def radialSphereOperator (A : Module.End ℝ E) (d : ℝ) : ℕ → Module.End ℝ E
  | 0 => 1
  | 1 => A
  | n+2 => A*radialSphereOperator A d (n+1) -
      (if n=0 then d else d-1) • radialSphereOperator A d n

/-- A finitely supported radial coefficient profile determines one and the
same polynomial operator at every tree center. -/
def radialFilterOperator (A : Module.End ℝ E) (d : ℝ) (R : ℕ) (f : ℕ → ℝ) : Module.End ℝ E :=
  ∑ n ∈ Finset.range (R+1), f n • radialSphereOperator A d n
end Operators

/-- The actual adjacency action on a radial profile. -/
def radialAdjacencyProfile (d : ℝ) : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) where
  toFun f n := if n=0 then d*f 1 else f (n-1)+(d-1)*f (n+1)
  map_add' f g := by ext n; by_cases h : n=0 <;> simp [h] <;> ring
  map_smul' c f := by ext n; by_cases h : n=0 <;> simp [h] <;> ring

def sphereIndicator (n : ℕ) : ℕ → ℝ := fun k => if k=n then 1 else 0

theorem radialAdjacencyProfile_indicator_zero (d : ℝ) :
    radialAdjacencyProfile d (sphereIndicator 0)=sphereIndicator 1 := by
  ext n
  cases n with
  | zero => simp [radialAdjacencyProfile,sphereIndicator]
  | succ n =>
    simp only [radialAdjacencyProfile, LinearMap.coe_mk, AddHom.coe_mk,
      Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
      sphereIndicator]
    by_cases h : n=0 <;> simp [h]

theorem radialAdjacencyProfile_indicator_succ (d : ℝ) (n : ℕ) :
    radialAdjacencyProfile d (sphereIndicator (n+1)) =
      sphereIndicator (n+2)+(if n=0 then d else d-1) • sphereIndicator n := by
  ext r
  cases r with
  | zero =>
    by_cases hn : n=0
    · subst n; simp [radialAdjacencyProfile,sphereIndicator]
    · have h1 : 1 ≠ n+1 := by omega
      have h2 : (0 : ℕ) ≠ n+2 := by omega
      have h3 : (0 : ℕ) ≠ n := Ne.symm hn
      simp [radialAdjacencyProfile,sphereIndicator,hn,h1,h2,h3]
  | succ r =>
    have h1 : (r+1-1=n+1) ↔ r+1=n+2 := by omega
    have h2 : (r+1+1=n+1) ↔ r+1=n := by omega
    by_cases hn : n=0
    · subst n
      have h3 : r+1+1 ≠ 1 := by omega
      have h4 : r+1 ≠ 0 := by omega
      simp only [radialAdjacencyProfile, LinearMap.coe_mk, AddHom.coe_mk,
        Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,Pi.add_apply,
        Pi.smul_apply,smul_eq_mul,sphereIndicator,h1,h3,h4,if_false,mul_zero,add_zero]
    · simp only [radialAdjacencyProfile,LinearMap.coe_mk,AddHom.coe_mk,
        Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,Pi.add_apply,
        Pi.smul_apply,smul_eq_mul,sphereIndicator,h1,h2,if_neg hn]

/-- Evaluated sphere polynomials are actual distance indicators. -/
theorem radialSphereOperator_profile_indicator (d : ℝ) (n : ℕ) :
    radialSphereOperator (radialAdjacencyProfile d) d n (sphereIndicator 0)=sphereIndicator n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => exact radialAdjacencyProfile_indicator_zero d
  | more n hn hn1 =>
    simp only [radialSphereOperator,LinearMap.sub_apply,Module.End.mul_apply,
      LinearMap.smul_apply,hn,hn1,radialAdjacencyProfile_indicator_succ]
    simp

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

def HasTreeRadialProfile (G : SimpleGraph V) (u : V) (a : V →₀ ℝ) (f : ℕ → ℝ) : Prop :=
  ∀ v, a v=f (G.dist v u)

/-- The constructed finite-support adjacency intertwines with the explicit
radial-profile operator. -/
theorem finiteAdjacency_has_radialProfile (hT : G.IsTree) (d : ℕ) (hd : G.IsRegularOfDegree d)
    (u : V) (a : V →₀ ℝ) (f : ℕ → ℝ) (h : HasTreeRadialProfile G u a f) :
    HasTreeRadialProfile G u (finiteAdjacency G a) (radialAdjacencyProfile d f) := by
  intro v
  rw [finiteAdjacency_apply]
  simp_rw [show ∀ v, a v=f (G.dist v u) from h]
  rw [tree_sum_neighbor_radial hT d hd f v u]
  change _ = if G.dist v u=0 then (d : ℝ)*f 1 else
    f (G.dist v u-1)+((d : ℝ)-1)*f (G.dist v u+1)
  simp only [hT.isConnected.dist_eq_zero_iff]

theorem single_has_radialProfile (hT : G.IsTree) (u : V) :
    HasTreeRadialProfile G u (Finsupp.single u 1) (sphereIndicator 0) := by
  intro v
  unfold sphereIndicator
  simp only [hT.isConnected.dist_eq_zero_iff]
  simp only [Finsupp.single_apply]
  split_ifs <;> simp_all

/-- All the sphere polynomials intertwine with the actual graph operator. -/
theorem radialSphereOperator_has_radialProfile (hT : G.IsTree) (d : ℕ) (hd : G.IsRegularOfDegree d)
    (u : V) (a : V →₀ ℝ) (f : ℕ → ℝ) (h : HasTreeRadialProfile G u a f) (n : ℕ) :
    HasTreeRadialProfile G u (radialSphereOperator (finiteAdjacency G) d n a)
      (radialSphereOperator (radialAdjacencyProfile d) d n f) := by
  induction n using Nat.twoStepInduction with
  | zero => exact h
  | one => exact finiteAdjacency_has_radialProfile hT d hd u a f h
  | more n hn hn1 =>
    have ha := finiteAdjacency_has_radialProfile hT d hd u
      (radialSphereOperator (finiteAdjacency G) d (n+1) a)
      (radialSphereOperator (radialAdjacencyProfile d) d (n+1) f) hn1
    intro v
    simp only [radialSphereOperator,LinearMap.sub_apply,Module.End.mul_apply,
      LinearMap.smul_apply,Finsupp.sub_apply,Finsupp.smul_apply,Pi.sub_apply,
      Pi.smul_apply,smul_eq_mul]
    rw [ha,hn]

/-- Every finite radial filter intertwines, with the same profile operator
at every possible center. -/
theorem radialFilterOperator_has_radialProfile (hT : G.IsTree) (d : ℕ) (hd : G.IsRegularOfDegree d)
    (u : V) (a : V →₀ ℝ) (f g : ℕ → ℝ) (h : HasTreeRadialProfile G u a g) (R : ℕ) :
    HasTreeRadialProfile G u (radialFilterOperator (finiteAdjacency G) d R f a)
      (radialFilterOperator (radialAdjacencyProfile d) d R f g) := by
  intro v
  simp only [radialFilterOperator,LinearMap.sum_apply,LinearMap.smul_apply,
    Finset.sum_apply,Finsupp.finset_sum_apply,Finsupp.smul_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [radialSphereOperator_has_radialProfile hT d hd u a g h n v]

/-- Its action on a point mass is exactly the prescribed truncated radial
profile, so these are actual kernels rather than assumed approximations. -/
theorem radialFilterOperator_single_apply (hT : G.IsTree) (d : ℕ) (hd : G.IsRegularOfDegree d)
    (u v : V) (R : ℕ) (f : ℕ → ℝ) :
    radialFilterOperator (finiteAdjacency G) d R f (Finsupp.single u 1) v =
      if G.dist v u ≤ R then f (G.dist v u) else 0 := by
  have h := radialFilterOperator_has_radialProfile hT d hd u (Finsupp.single u 1)
    f (sphereIndicator 0) (single_has_radialProfile hT u) R v
  rw [h]
  simp only [radialFilterOperator,LinearMap.sum_apply,LinearMap.smul_apply,
    radialSphereOperator_profile_indicator,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,sphereIndicator,
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_range,Nat.lt_succ_iff]


section Symmetry
variable {W : Type*}

/-- Actual symmetry of an endomorphism for the finite Euclidean pairing. -/
def FinsuppSymmetric (A : Module.End ℝ (W →₀ ℝ)) : Prop :=
  ∀ a b, finsuppPairing (A a) b=finsuppPairing a (A b)

private theorem finsuppSymmetric_sub {A B : Module.End ℝ (W →₀ ℝ)}
    (hA : FinsuppSymmetric A) (hB : FinsuppSymmetric B) : FinsuppSymmetric (A-B) := by
  intro a b
  simp only [LinearMap.sub_apply,map_sub,LinearMap.sub_apply]
  rw [hA a b,hB a b]

private theorem finsuppSymmetric_smul {A : Module.End ℝ (W →₀ ℝ)}
    (hA : FinsuppSymmetric A) (c : ℝ) : FinsuppSymmetric (c • A) := by
  intro a b
  simp only [LinearMap.smul_apply,map_smul,LinearMap.smul_apply]
  rw [hA a b]

private theorem finsuppSymmetric_mul {A B : Module.End ℝ (W →₀ ℝ)}
    (hA : FinsuppSymmetric A) (hB : FinsuppSymmetric B) (hc : A*B=B*A) : FinsuppSymmetric (A*B) := by
  intro a b
  change finsuppPairing (A (B a)) b=finsuppPairing a (A (B b))
  rw [hA (B a) b,hB a (A b)]
  have he : B (A b)=A (B b) := congrArg (fun T : Module.End ℝ (W →₀ ℝ) => T b) hc.symm
  rw [he]

/-- Every evaluated sphere polynomial commutes with its actual adjacency
operator; the proof is algebra inside the endomorphism ring. -/
theorem radialSphereOperator_commutes {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Module.End ℝ E) (d : ℝ) (n : ℕ) :
    A*radialSphereOperator A d n=radialSphereOperator A d n*A := by
  induction n using Nat.twoStepInduction with
  | zero => simp [radialSphereOperator]
  | one => rfl
  | more n hn hn1 =>
    simp only [radialSphereOperator,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
    congr 1
    · calc
        A*(A*radialSphereOperator A d (n+1)) = A*(radialSphereOperator A d (n+1)*A) := by rw [hn1]
        _ = (A*radialSphereOperator A d (n+1))*A := (mul_assoc _ _ _).symm
    · rw [hn]

/-- Genuine self-adjointness passes from adjacency to every sphere
polynomial, using proved commutation rather than a spectral premise. -/
theorem radialSphereOperator_symmetric (A : Module.End ℝ (W →₀ ℝ))
    (hA : FinsuppSymmetric A) (d : ℝ) (n : ℕ) : FinsuppSymmetric (radialSphereOperator A d n) := by
  induction n using Nat.twoStepInduction with
  | zero => intro a b; rfl
  | one => exact hA
  | more n hn hn1 =>
    exact finsuppSymmetric_sub
      (finsuppSymmetric_mul hA hn1 (radialSphereOperator_commutes A d (n+1)))
      (finsuppSymmetric_smul hn _)

/-- Every actual finite radial filter is self-adjoint. -/
theorem radialFilterOperator_symmetric (A : Module.End ℝ (W →₀ ℝ))
    (hA : FinsuppSymmetric A) (d : ℝ) (R : ℕ) (f : ℕ → ℝ) :
    FinsuppSymmetric (radialFilterOperator A d R f) := by
  intro a b
  simp only [radialFilterOperator,LinearMap.sum_apply,map_sum,map_smul,
    LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [radialSphereOperator_symmetric A hA d n a b]
end Symmetry

/-- A product of two identical radial filters is still radial, and its
profile is explicit and independent of both chosen vertices. -/
theorem radial_filter_pairing_kernel (hT : G.IsTree) (d : ℕ) (hd : G.IsRegularOfDegree d)
    (R : ℕ) (f : ℕ → ℝ) (u v : V) :
    finsuppPairing (radialFilterOperator (finiteAdjacency G) d R f (Finsupp.single u 1))
      (radialFilterOperator (finiteAdjacency G) d R f (Finsupp.single v 1)) =
      radialFilterOperator (radialAdjacencyProfile d) d R f
        (radialFilterOperator (radialAdjacencyProfile d) d R f (sphereIndicator 0)) (G.dist u v) := by
  rw [radialFilterOperator_symmetric (finiteAdjacency G) (finsuppPairing_adjacency G) d R f,
    finsuppPairing_single_left,one_mul]
  have h1 := radialFilterOperator_has_radialProfile hT d hd v (Finsupp.single v 1)
    f (sphereIndicator 0) (single_has_radialProfile hT v) R
  exact radialFilterOperator_has_radialProfile hT d hd v _ f _ h1 R u


/-- Actual finite radial convolution commutes with adjacency. -/
theorem radialFilterOperator_commutes {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Module.End ℝ E) (d : ℝ) (R : ℕ) (f : ℕ → ℝ) :
    A*radialFilterOperator A d R f=radialFilterOperator A d R f*A := by
  unfold radialFilterOperator
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_smul_comm,smul_mul_assoc,radialSphereOperator_commutes]

end GaussianWave.BS
