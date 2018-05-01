import data.equiv group_theory.coset

universes u v w u₁

namespace setoid
variables {α : Sort u} [setoid α]

lemma comm {a b : α} : a ≈ b ↔ b ≈ a :=
⟨symm, symm⟩

end setoid

section coset_group
variables {α : Type u} [group α] (s : set α) [is_subgroup s]
variables (x y : α) (L : left_cosets s)

local attribute [instance] left_rel

def left_cosets.left_mul : left_cosets s :=
quotient.lift_on L (λ z, ⟦x * z⟧) $ λ m n (H : m⁻¹ * n ∈ s),
quotient.sound $ show (x * m)⁻¹ * (x * n) ∈ s, by simpa [mul_assoc]

@[simp] lemma left_cosets.mul_eq :
  left_cosets.left_mul s x ⟦y⟧ = ⟦x * y⟧ := rfl

theorem left_cosets.one_mul :
  left_cosets.left_mul s 1 L = L :=
quotient.induction_on L $ λ _, by simp

theorem left_cosets.mul_mul :
  left_cosets.left_mul s (x * y) L
  = left_cosets.left_mul s x (left_cosets.left_mul s y L) :=
quotient.induction_on L $ λ _, by simp [mul_assoc]

end coset_group

namespace is_subgroup

variables {α : Type u} [group α] (g x y : α) (s : set α) [is_subgroup s]

def conjugate : set α :=
{ x | g⁻¹ * x * g ∈ s }

@[simp] lemma mem_conjugate_iff : x ∈ conjugate g s ↔ g⁻¹ * x * g ∈ s :=
iff.refl _

instance conjugate.is_subgroup : is_subgroup (conjugate g s) :=
{ one_mem := have (1:α) ∈ s := is_submonoid.one_mem s, by simpa,
  mul_mem := λ x y hx hy, have (g⁻¹ * x * g) * (g⁻¹ * y * g) ∈ s := is_submonoid.mul_mem hx hy,
    by simpa [mul_assoc] using this,
  inv_mem := λ x hx, have (g⁻¹ * x * g)⁻¹ ∈ s := is_subgroup.inv_mem hx,
    by simpa [mul_assoc] using this }

theorem conjugate_one : conjugate 1 s = s :=
set.ext $ λ z, by simp

theorem conjugate_mul : conjugate (x * y) s = conjugate x (conjugate y s) :=
set.ext $ λ z, by simp [conjugate, mul_assoc]

end is_subgroup

variables (G : Type u) [group G] (X S : Type v)

class group_action : Type (max u v) :=
(fn : G → X → X)
(one : ∀ x, fn 1 x = x)
(mul : ∀ g h x, fn (g * h) x = fn g (fn h x))

variable [group_action G X]

infixr ` ● `:100 := group_action.fn -- \ci

variables (g h : G) (x y : X)

variables {G X g h x y}

@[simp] lemma one_act : (1:G) ● x = x :=
group_action.one G x

lemma mul_act : (g * h) ● x = g ● h ● x :=
group_action.mul g h x

lemma act_act : g ● h ● x = (g * h) ● x :=
eq.symm $ group_action.mul g h x

lemma inv_act (H : g ● x = y) : g⁻¹ ● y = x :=
by rw ← H; simp [act_act]

lemma inv_act_iff : g⁻¹ ● y = x ↔ g ● x = y :=
⟨λ H, by rw ← H; simp [act_act], inv_act⟩

namespace group_action

variables (G X g h x y)

def to_equiv : X ≃ X :=
⟨(●) g, (●) g⁻¹, λ x, by simp [act_act], λ x, by simp [act_act]⟩

def examples.trivial : group_action G S :=
⟨λ g, id, λ x, rfl, λ g h x, rfl⟩

def examples.func : group_action G (X → S) :=
{ fn  := λ g f x, f (g⁻¹ ● x),
  one := by simp,
  mul := by simp [mul_act] }

def examples.mul_left : group_action G G :=
⟨(*), by simp, by simp [mul_assoc]⟩

def examples.mul_right_inv : group_action G G :=
⟨λ x y, y * x⁻¹, by simp, by simp [mul_assoc]⟩

def examples.conjugate : group_action G G :=
⟨λ g x, g * x * g⁻¹, by simp, by simp [mul_assoc]⟩

def examples.cosets (H : set G) (hs : is_subgroup H) : group_action G (left_cosets H) :=
⟨left_cosets.left_mul H, left_cosets.one_mul H, left_cosets.mul_mul H⟩

def examples.subsets : group_action G (set X) :=
⟨λ g A, (●) g '' A,
 λ A, set.ext $ λ x,
   ⟨λ ⟨y, hyA, hyx⟩, by simp at hyx; rw ← hyx; from hyA,
    λ hxA, ⟨x, by simp [hxA]⟩⟩,
 λ g h A, set.ext $ λ x,
  ⟨λ ⟨y, hyH, hghyx⟩, ⟨h ● y, ⟨y, hyH, rfl⟩, by simpa [mul_act] using hghyx⟩,
   λ ⟨y, ⟨z, hzH, hhzy⟩, hgyx⟩, ⟨z, hzH, by simp [mul_act, hhzy, hgyx]⟩⟩⟩

def examples.subgroups : group_action G { s : set G // is_subgroup s } :=
⟨λ g s, ⟨@is_subgroup.conjugate _ _ g s.1 s.2, @is_subgroup.conjugate.is_subgroup _ _ _ _ s.2⟩,
 λ s, subtype.eq $ @is_subgroup.conjugate_one _ _ s.1 s.2,
 λ g h s, subtype.eq $ @is_subgroup.conjugate_mul _ _ g h s.1 s.2⟩

def examples.product : group_action G (G × S) :=
⟨λ g hx, (g * hx.1, hx.2), by simp, by simp [mul_assoc]⟩

class faithful (G : Type u) [group G] (X : Type v) extends group_action G X : Type (max u v) :=
(one_of_forall_eq : ∀ g : G, (∀ x : X, g ● x = x) → g = 1)

def faithful.examples.mul_left : group_action.faithful G G :=
{ one_of_forall_eq := λ g H, have H1 : g * 1 = 1, from H 1, by simpa using H1,
  .. examples.mul_left G }

class free (G : Type u) [group G] (X : Type v) extends group_action G X : Type (max u v) :=
(one_of_eq : ∀ (g : G) (x : X), g ● x = x → g = 1)

def free.examples.mul_left : group_action.free G G :=
{ one_of_eq := λ g x H, have H1 : g * x * x⁻¹ = x * x⁻¹,
    from congr_arg (λ z, z * x⁻¹) H, by simpa using H1,
  .. examples.mul_left G }

def orbit : set X :=
{ y | ∃ g : G, g ● x = y }

def stab : set G :=
{ g | g ● x = x }

@[simp] lemma mem_orbit_iff : y ∈ orbit G X x ↔ ∃ g : G, g ● x = y := iff.rfl

@[simp] lemma mem_stab_iff : g ∈ stab G X x ↔ g ● x = x := iff.rfl

instance stab.is_subgroup : is_subgroup (stab G X x) :=
{ mul_mem := λ g1 g2 hg1 hg2, by simp at hg1 hg2; simp [mul_act, hg1, hg2],
  one_mem := by simp,
  inv_mem := λ g hg, inv_act hg }
set_option pp.proofs true
set_option trace.check true

def stab_cosets_to_orbit : left_cosets (stab G X x) → orbit G X x :=
@quotient.lift _ _ (left_rel (stab G X x)) (λ g, (⟨g ● x, g, rfl⟩ : orbit G X x)) $
λ g1 g2 (H : (g1⁻¹ * g2) ● x = x), subtype.eq $ inv_act_iff.1 $ eq.trans act_act H

noncomputable def orbit_equiv_stab_cosets : orbit G X x ≃ left_cosets (stab G X x) :=
equiv.symm $ @equiv.of_bijective _ _ (stab_cosets_to_orbit G X x) $
⟨λ L1 L2, by letI := left_rel (stab G X x); exact
  quotient.induction_on₂ L1 L2 (λ m n H,
    have m ● x = n ● x, from subtype.mk.inj H,
    quotient.sound $ show (m⁻¹ * n) ● x = x, by simpa [mul_act, inv_act_iff]),
λ ⟨y, g, H⟩, by letI := left_rel (stab G X x); exact ⟨⟦g⟧, subtype.eq H⟩⟩

noncomputable def orbit_stab : (orbit G X x × stab G X x) ≃ G :=
(equiv.prod_congr (orbit_equiv_stab_cosets G X x) (equiv.refl $ stab G X x)).trans
(is_subgroup.group_equiv_left_cosets_times_subgroup _).symm

instance orbit_rel : setoid X :=
⟨λ x y, ∃ g : G, g ● x = y,
 λ x, ⟨1, by simp⟩,
 λ x y ⟨g, H⟩, ⟨g⁻¹, by simp [inv_act_iff, H]⟩,
 λ x y z ⟨g1, H1⟩ ⟨g2, H2⟩, ⟨g2 * g1, by simp [mul_act, H1, H2]⟩⟩

def orbits : Type v := quotient (group_action.orbit_rel G X)

def orbits_to_orbit : orbits G X → set X :=
quotient.lift (orbit G X) $ λ x y ⟨g, H⟩,
set.ext $ λ z,
⟨λ ⟨g1, h1⟩, ⟨g1 * g⁻¹, by rw [mul_act, inv_act H, h1]⟩,
 λ ⟨g1, h1⟩, ⟨g1 * g, by rw [mul_act, H, h1]⟩⟩

theorem orbits_to_orbit_eq_orbit_out (A) : orbits_to_orbit G X A = orbit G X (quotient.out A) :=
by rw [orbits_to_orbit, ← quotient.out_eq A, quotient.lift_beta]; simp

theorem orbits_to_orbit_eq_fibre (A) : orbits_to_orbit G X A = { x | ⟦x⟧ = A } :=
set.ext $ λ x, quotient.induction_on A $ λ z, by simp [orbits_to_orbit]; rw setoid.comm; refl

theorem orbit_out_eq_fibre (A) : orbit G X (quotient.out A) = { x | ⟦x⟧ = A } :=
(orbits_to_orbit_eq_orbit_out G X A).symm.trans (orbits_to_orbit_eq_fibre G X A)

def stab_equiv (H : g ● x = y) : stab G X x ≃ stab G X y :=
⟨λ g1, ⟨g * g1.1 * g⁻¹, by cases g1 with g1 h1; change g1 ● x = x at h1; simp [mul_act, inv_act H, h1, H]⟩,
 λ g1, ⟨g⁻¹ * g1.1 * g, by cases g1 with g1 h1; change g1 ● y = y at h1; simp [mul_act, H, h1, inv_act H]⟩,
 λ ⟨g1, h1⟩, by simp [mul_assoc],
 λ ⟨g1, h1⟩, by simp [mul_assoc]⟩

def fixed : set X := { x | g ● x = x }

noncomputable def burnside : (Σ g, fixed G X g) ≃ (orbits G X × G) :=
calc  (Σ g, fixed G X g)
    ≃ (Σ x, stab G X x) :
  ⟨λ z, ⟨z.2.1, z.1, z.2.2⟩, λ z, ⟨z.2.1, z.1, z.2.2⟩, λ ⟨g, x, h⟩, rfl, λ ⟨x, g, h⟩, rfl⟩
... ≃ (Σ A : orbits G X, Σ x : { x | ⟦x⟧ = A }, stab G X x) :
  ⟨λ z, ⟨⟦z.1⟧, ⟨_, rfl⟩, z.2⟩, λ z, ⟨z.2.1.1, z.2.2⟩, λ ⟨x, z⟩, rfl, λ ⟨A, ⟨x, (hx : ⟦x⟧ = A)⟩, z⟩, sigma.eq hx $ by subst hx⟩
... ≃ (Σ A : orbits G X, Σ x : { x | ⟦x⟧ = A }, stab G X (quotient.out A)) :
  equiv.sigma_congr_right (λ A, equiv.sigma_congr_right (λ ⟨x, (hx : ⟦x⟧ = A)⟩,
    stab_equiv G X _ _ _ (classical.some_spec (quotient.exact (hx.trans (quotient.out_eq A).symm)))))
... ≃ (Σ A : orbits G X, { x | ⟦x⟧ = A } × stab G X (quotient.out A)) :
  equiv.sigma_congr_right (λ A, equiv.sigma_equiv_prod _ _)
... ≃ (Σ A : orbits G X, orbit G X (quotient.out A) × stab G X (quotient.out A)) :
  equiv.sigma_congr_right (λ A, by rw orbit_out_eq_fibre)
... ≃ (Σ A : orbits G X, G) :
  equiv.sigma_congr_right (λ A, orbit_stab G X _)
... ≃ (orbits G X × G) :
  equiv.sigma_equiv_prod _ _

variables (Y : Type w) [group_action G Y]
variables (Z : Type u₁) [group_action G Z]

variables {X Y Z}

def is_hom (f : X → Y) : Prop :=
∀ (g : G) (x : X), f (g ● x) = g ● f x

theorem is_hom.id : is_hom G (@id X) :=
λ g x, rfl

theorem is_hom.comp (f : Y → Z) (hf : is_hom G f)
  (g : X → Y) (hg : is_hom G g) : is_hom G (f ∘ g) :=
λ g x, by dsimp; rw [hg, hf]

end group_action