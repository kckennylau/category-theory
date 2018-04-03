import data.equiv group_theory.subgroup

universes u v w u₁

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

def examples.cosets (H : set G) (hs : is_subgroup H) : group_action G (cosets H) :=
⟨λ g hH, ⟨(*) g '' hH.1, let ⟨h, hh⟩ := hH.2 in ⟨g * h,
  by rw ← hh; apply set.ext; intro x; from
  ⟨λ ⟨y, hyH, hghyx⟩, ⟨h * y, ⟨y, hyH, rfl⟩, by simpa [mul_assoc] using hghyx⟩,
   λ ⟨y, ⟨z, hzH, hhzy⟩, hgyx⟩, ⟨z, hzH, by simp [mul_assoc, hhzy, hgyx]⟩⟩⟩⟩,
 λ gH, subtype.eq $ set.ext $ λ z, ⟨λ ⟨x, hx1, hx2⟩, by simp at hx2; rw ← hx2; from hx1,
   λ h, ⟨z, h, by simp⟩⟩,
 λ g h rH, subtype.eq $ set.ext $ λ x,
  ⟨λ ⟨y, hyH, hghyx⟩, ⟨h * y, ⟨y, hyH, rfl⟩, by simpa [mul_assoc] using hghyx⟩,
   λ ⟨y, ⟨z, hzH, hhzy⟩, hgyx⟩, ⟨z, hzH, by simp [mul_assoc, hhzy, hgyx]⟩⟩⟩

def examples.subsets : group_action G (set X) :=
⟨λ g A, (●) g '' A,
 λ A, set.ext $ λ x,
   ⟨λ ⟨y, hyA, hyx⟩, by simp at hyx; rw ← hyx; from hyA,
    λ hxA, ⟨x, by simp [hxA]⟩⟩,
 λ g h A, set.ext $ λ x,
  ⟨λ ⟨y, hyH, hghyx⟩, ⟨h ● y, ⟨y, hyH, rfl⟩, by simpa [mul_act] using hghyx⟩,
   λ ⟨y, ⟨z, hzH, hhzy⟩, hgyx⟩, ⟨z, hzH, by simp [mul_act, hhzy, hgyx]⟩⟩⟩

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

def stab.is_subgroup : is_subgroup (stab G X x) :=
⟨by simp, λ g h1 h h2, by simp [mul_act]; rw [inv_act h2]; simpa using h1⟩

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