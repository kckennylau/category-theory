/- 
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Three-step construction of free group of a type.
Based on https://math.stackexchange.com/a/852661/328173
-/

import data.list.basic algebra.group

universes u v

class inv_type (IT : Type u) extends has_inv IT :=
(inv_inv : ∀ x : IT, x⁻¹⁻¹ = x)

class involution_monoid (M : Type u) extends monoid M, inv_type M :=
(mul_inv : ∀ x y : M, (x*y)⁻¹ = y⁻¹ * x⁻¹)
(one_inv : (1:M)⁻¹ = 1)

instance group.to_involution_monoid (G : Type u) [group G] : involution_monoid G :=
{ mul_inv := mul_inv_rev,
  one_inv := one_inv,
  inv_inv := inv_inv }

class involution_monoid.is_hom {M : Type u} {N : Type v}
  [involution_monoid M] [involution_monoid N] (f : M → N) : Prop :=
(mul : ∀ x y, f (x * y) = f x * f y)
(one : f 1 = 1)
(inv : ∀ x, f x⁻¹ = (f x)⁻¹)

namespace involution_monoid.to_group

variables (M : Type u) [involution_monoid M]

inductive rel : M → M → Prop
| refl : ∀ x, rel x x
| symm : ∀ x y, rel x y → rel y x
| trans : ∀ x y z, rel x y → rel y z → rel x z
| mul : ∀ x y z w, rel x z → rel y w → rel (x * y) (z * w)
| inv : ∀ x y, rel x y → rel x⁻¹ y⁻¹
| mul_left_inv : ∀ x, rel (x⁻¹ * x) 1

instance quotient_rel : setoid M :=
⟨rel M, rel.refl, rel.symm, rel.trans⟩

end involution_monoid.to_group

@[reducible] def involution_monoid.to_group (M : Type u) [involution_monoid M] : Type u :=
quotient (involution_monoid.to_group.quotient_rel M)

namespace involution_monoid.to_group

instance (M : Type u) [involution_monoid M] : group (involution_monoid.to_group M) :=
{ mul := λ x y, quotient.lift_on₂ x y (λ m n, quotient.mk (m * n))
    (λ x y z w hxz hyw, quotient.sound $ rel.mul x y z w hxz hyw),
  mul_assoc := λ x y z, quotient.induction_on₃ x y z $
    λ a b c, quotient.sound $ by rw mul_assoc,
  one := quotient.mk 1,
  mul_one := λ x, quotient.induction_on x $
    λ a, quotient.sound $ by rw mul_one,
  one_mul := λ x, quotient.induction_on x $
    λ a, quotient.sound $ by rw one_mul,
  inv := λ x, quotient.lift_on x (λ m, quotient.mk m⁻¹)
    (λ x y hxy, quotient.sound $ rel.inv x y hxy),
  mul_left_inv := λ x, quotient.induction_on x $
    λ a, quotient.sound $ rel.mul_left_inv a }

def of_involution_monoid {M : Type u} [involution_monoid M] : M → involution_monoid.to_group M :=
quotient.mk

@[simp] lemma of_involution_monoid.mul {M : Type u} [involution_monoid M] {x y : M} :
  of_involution_monoid (x * y) = of_involution_monoid x * of_involution_monoid y := rfl

@[simp] lemma of_involution_monoid.one {M : Type u} [involution_monoid M] :
  of_involution_monoid (1:M) = 1 := rfl

@[simp] lemma of_involution_monoid.inv {M : Type u} [involution_monoid M] {x : M} :
  of_involution_monoid x⁻¹ = (of_involution_monoid x)⁻¹ := rfl

section left_adjoint

parameters (M : Type u) [involution_monoid M]
parameters (G : Type v) [group G]
parameters (f : M → G) -- M → Forgetful(G)
parameters [Hf : involution_monoid.is_hom f]
include Hf

def left_adjoint : involution_monoid.to_group M → G := -- Free(M) → G
λ x, quotient.lift_on x f $ λ a b hab, begin
  induction hab with h c d h ih c d e h1 h2 ih1 ih2
    c d p q h1 h2 ih1 ih2 c d h ih c,
  case involution_monoid.to_group.rel.refl
  { refl },
  case involution_monoid.to_group.rel.symm
  { exact ih.symm },
  case involution_monoid.to_group.rel.trans
  { exact ih1.trans ih2 },
  case involution_monoid.to_group.rel.mul
  { rw [Hf.mul, Hf.mul, ih1, ih2] },
  case involution_monoid.to_group.rel.inv
  { rw [Hf.inv, Hf.inv, ih] },
  case involution_monoid.to_group.rel.mul_left_inv
  { rw [Hf.mul, Hf.inv, mul_left_inv, Hf.one] }
end

theorem left_adjoint.is_group_hom : is_group_hom left_adjoint :=
λ x y, quotient.induction_on₂ x y Hf.mul

theorem left_adjoint.commutes (x) : left_adjoint (of_involution_monoid x) = f x := rfl

parameters (g : involution_monoid.to_group M → G)
parameters (Hg : ∀ x, g (of_involution_monoid x) = f x)

theorem left_adjoint.unique : ∀ x, g x = left_adjoint x :=
λ x, quotient.induction_on x $ λ m, Hg m

end left_adjoint

end involution_monoid.to_group

@[reducible] def inv_type.to_involution_monoid (IT : Type u) [inv_type IT] :=
list IT

namespace inv_type.to_involution_monoid

instance (IT : Type u) [inv_type IT] : involution_monoid (inv_type.to_involution_monoid IT) :=
{ mul := (++),
  one := [],
  inv := λ x, x.reverse.map has_inv.inv,
  mul_assoc := list.append_assoc,
  one_mul := list.nil_append,
  mul_one := list.append_nil,
  mul_inv := λ x y, show (x ++ y).reverse.map has_inv.inv
    = y.reverse.map has_inv.inv ++ x.reverse.map has_inv.inv,
    by rw [list.reverse_append, list.map_append],
  one_inv := rfl,
  inv_inv := λ x, have h1 : (has_inv.inv ∘ has_inv.inv) = @id IT,
    from funext $ inv_type.inv_inv,
    by dsimp; rw [list.map_reverse, list.map_reverse];
    rw [list.map_reverse, list.reverse_reverse];
    rw [list.map_map, h1, list.map_id] }

def of_inv_type {IT : Type u} [inv_type IT] : IT → inv_type.to_involution_monoid IT :=
λ x, [x]

@[simp] lemma of_inv_type.inv {IT : Type u} [inv_type IT] {x : IT} :
  of_inv_type x⁻¹ = (of_inv_type x)⁻¹ := rfl

section left_adjoint

parameters (IT : Type u) [inv_type IT]
parameters (M : Type v) [involution_monoid M]
parameters (f : IT → M) -- IT → Forgetful(M)
parameters (Hinv : ∀ x, f x⁻¹ = (f x)⁻¹)

def left_adjoint : inv_type.to_involution_monoid IT → M := -- Free(IT) → M
λ L, list.prod (L.map f)

theorem left_adjoint.append (x y) : left_adjoint (x ++ y) = left_adjoint x * left_adjoint y :=
by dsimp [left_adjoint]; rw [list.map_append, list.prod_append]

theorem left_adjoint.mul (x y) : left_adjoint (x * y) = left_adjoint x * left_adjoint y :=
left_adjoint.append x y

theorem left_adjoint.one : left_adjoint 1 = 1 := rfl

include Hinv
theorem left_adjoint.inv : ∀ x, left_adjoint x⁻¹ = (left_adjoint x)⁻¹
| []     := eq.symm $ involution_monoid.one_inv M
| (h::IT) := have _ := left_adjoint.inv IT,
  by dsimp [left_adjoint, has_inv.inv] at this ⊢;
  rw [list.map_reverse, list.map_reverse] at this ⊢;
  rw [list.map_cons, list.map_cons, list.prod_cons, involution_monoid.mul_inv, ← this];
  rw [list.reverse_cons', list.prod_append, list.prod_cons, list.prod_nil];
  rw [mul_one, Hinv]
omit Hinv

instance left_adjoint.hom : involution_monoid.is_hom left_adjoint :=
⟨left_adjoint.mul, left_adjoint.one, left_adjoint.inv⟩

theorem left_adjoint.commutes (x) : left_adjoint (of_inv_type x) = f x :=
one_mul _

parameters (g : inv_type.to_involution_monoid IT → M)
parameters (Hg1 : ∀ x y, g (x * y) = g x * g y)
parameters (Hg2 : g 1 = 1)
parameters (Hg3 : ∀ x, g (of_inv_type x) = f x)
include Hg1 Hg3

theorem left_adjoint.unique : ∀ x, g x = left_adjoint x
| []     := Hg2
| (h::t) := eq.trans (Hg1 (of_inv_type h) t) $
  by rw [left_adjoint.unique t]; dsimp [left_adjoint]; rw [Hg3, list.prod_cons]

end left_adjoint

end inv_type.to_involution_monoid

@[reducible] def to_inv_type (T : Type u) :=
sum T T

namespace to_inv_type

def inv (T : Type u) : to_inv_type T → to_inv_type T
| (sum.inl x) := sum.inr x
| (sum.inr x) := sum.inl x

theorem inv.inv (T : Type u) : ∀ x : to_inv_type T, inv T (inv T x) = x
| (sum.inl x) := rfl
| (sum.inr x) := rfl

instance (T : Type u) : inv_type (to_inv_type T) :=
{ inv := inv T,
  inv_inv := inv.inv T }

def of_inv_type {T : Type u} : T → to_inv_type T :=
sum.inl

section left_adjoint

parameters (T : Type u)
parameters (IT : Type v) [inv_type IT]
parameters (f : T → IT) -- T → Forgetful(IT)

def left_adjoint : to_inv_type T → IT -- Free(T) → IT
| (sum.inl x) := f x
| (sum.inr x) := (f x)⁻¹

theorem left_adjoint.inv : ∀ x, left_adjoint x⁻¹ = (left_adjoint x)⁻¹
| (sum.inl x) := rfl
| (sum.inr x) := eq.symm $ inv_type.inv_inv _

theorem left_adjoint.commutes (x) : left_adjoint (of_inv_type x) = f x := rfl

parameters (g : to_inv_type T → IT)
parameters (Hg1 : ∀ x, g x⁻¹ = (g x)⁻¹)
parameters (Hg2 : ∀ x, g (of_inv_type x) = f x)

theorem left_adjoint.unique : ∀ x, g x = left_adjoint x
| (sum.inl x) := Hg2 x
| (sum.inr x) := (Hg1 (sum.inl x)).trans $ congr_arg _ $ Hg2 x

end left_adjoint

end to_inv_type

@[reducible] def free_group.word (S : Type u) : Type u :=
inv_type.to_involution_monoid $ to_inv_type S

@[reducible] def free_group (S : Type u) : Type u :=
involution_monoid.to_group $ free_group.word S

namespace free_group

variables (S : Type u)

instance : group (free_group S) :=
involution_monoid.to_group.group _

def of_type : S → free_group S :=
λ x, ⟦[sum.inl x]⟧

variables (G : Type v) [group G]
variables (f : S → G) -- S → Forgetful(G)

def to_group : free_group S → G := -- Free(S) → G
involution_monoid.to_group.left_adjoint _ G
  (λ y, inv_type.to_involution_monoid.left_adjoint (to_inv_type S) _
    (to_inv_type.left_adjoint S _ f) y)

def to_group.is_group_hom : is_group_hom (to_group S G f) :=
involution_monoid.to_group.left_adjoint.is_group_hom _ _ _ _ _ _

def to_group.commutes (x) : to_group S G f (of_type S x) = f x :=
mul_one _

variables (g : free_group S → G)
variables (Hg1 : is_group_hom g)
variables (Hg2 : ∀ x, g (of_type S x) = f x)
include Hg1 Hg2

def to_group.unique : ∀ x, g x = to_group S G f x :=
λ x, quotient.induction_on x $ λ m, list.rec_on m (is_group_hom.one g) $
λ h t ih, sum.rec_on h
  (λ a, show g (of_type S a * ⟦t⟧) = _ , by rw [Hg1, Hg2, ih]; refl)
  (λ a, show g ((of_type S a)⁻¹ * ⟦t⟧) = _ , by rw [Hg1, is_group_hom.inv g, Hg2, ih]; refl)

omit Hg1 Hg2

variable [decidable_eq S]

def reduce : word S → word S
| ((sum.inl x)::(sum.inr y)::t) := if x = y then reduce t else ((sum.inl x)::(sum.inr y)::reduce t)
| ((sum.inr x)::(sum.inl y)::t) := if x = y then reduce t else ((sum.inr x)::(sum.inl y)::reduce t)
| (h1::h2::t)                   := h1::h2::reduce t
| w                             := w

theorem reduce.sound : ∀ w : word S, ⟦w⟧ = ⟦reduce S w⟧
| []                            := rfl
| ((sum.inl x)::[])             := rfl
| ((sum.inr x)::[])             := rfl
| ((sum.inl x)::(sum.inl y)::t) :=
    show ⟦[sum.inl x, sum.inl y]⟧ * ⟦t⟧ = ⟦[sum.inl x, sum.inl y]⟧ * ⟦reduce S t⟧,
    from congr_arg _ $ reduce.sound t
| ((sum.inr x)::(sum.inr y)::t) :=
    show ⟦[sum.inr x, sum.inr y]⟧ * ⟦t⟧ = ⟦[sum.inr x, sum.inr y]⟧ * ⟦reduce S t⟧,
    from congr_arg _ $ reduce.sound t
| ((sum.inl x)::(sum.inr y)::t) := begin
    dsimp [reduce],
    by_cases x = y; simp [h],
    { change ⟦[sum.inl y]⟧ * ⟦[sum.inr y]⟧ * ⟦t⟧ = ⟦reduce S t⟧,
      have h1 : ⟦[sum.inl y]⟧ * ⟦[sum.inr y]⟧ = 1,
      { exact mul_inv_self _ },
      rw [h1, one_mul, reduce.sound t] },
    { change ⟦[sum.inl x, sum.inr y]⟧ * ⟦t⟧ = ⟦[sum.inl x, sum.inr y]⟧ * ⟦reduce S t⟧,
      rw reduce.sound t }
  end
| ((sum.inr x)::(sum.inl y)::t) := begin
    dsimp [reduce],
    by_cases x = y; simp [h],
    { change ⟦[sum.inr y]⟧ * ⟦[sum.inl y]⟧ * ⟦t⟧ = ⟦reduce S t⟧,
      have h1 : ⟦[sum.inr y]⟧ * ⟦[sum.inl y]⟧ = 1,
      { exact mul_inv_self _ },
      rw [h1, one_mul, reduce.sound t] },
    { change ⟦[sum.inr x, sum.inl y]⟧ * ⟦t⟧ = ⟦[sum.inr x, sum.inl y]⟧ * ⟦reduce S t⟧,
      rw reduce.sound t }
  end

theorem reduce.exact.mul.nil : ∀ p q : word S, [] = reduce S p →
  reduce S q = reduce S (p * q)
| [] q h := rfl
| ((sum.inl x)::(sum.inr y)::t) q h :=
  show reduce S q = reduce S (sum.inl x :: sum.inr y :: t * q),
  begin
    dsimp [reduce] at h ⊢,
    by_cases H : x = y,
    { rw [if_pos H] at h ⊢,
      exact reduce.exact.mul.nil _ _ h },
    { rw [if_neg H] at h ⊢,
      exact list.no_confusion h },
  end
| ((sum.inr x)::(sum.inl y)::t) q h :=
  show reduce S q = reduce S (sum.inr x :: sum.inl y :: t * q),
  begin
    dsimp [reduce] at h ⊢,
    by_cases H : x = y,
    { rw [if_pos H] at h ⊢,
      exact reduce.exact.mul.nil _ _ h },
    { rw [if_neg H] at h ⊢,
      exact list.no_confusion h },
  end

-- TODO
-- theorem reduce.exact : ∀ v w : word S, v ≈ w → reduce S v = reduce S w :=

theorem reduce.min : ∀ w : word S, (reduce S w).length ≤ w.length 
| []                            := dec_trivial
| ((sum.inl x)::[])             := dec_trivial
| ((sum.inr x)::[])             := dec_trivial
| ((sum.inl x)::(sum.inl y)::t) :=
    add_le_add_right (add_le_add_right (reduce.min t) 1) 1
| ((sum.inr x)::(sum.inr y)::t) :=
    add_le_add_right (add_le_add_right (reduce.min t) 1) 1
| ((sum.inl x)::(sum.inr y)::t) :=
  match (by apply_instance : decidable (x = y)) with
  | (decidable.is_true  h) := nat.le_succ_of_le $
      nat.le_succ_of_le $ by dsimp [reduce]; rw [if_pos h];
      exact reduce.min t
  | (decidable.is_false h) := by dsimp [reduce]; rw [if_neg h];
      exact add_le_add_right (add_le_add_right (reduce.min t) 1) 1
  end
| ((sum.inr x)::(sum.inl y)::t) :=
  match (by apply_instance : decidable (x = y)) with
  | (decidable.is_true  h) := nat.le_succ_of_le $
      nat.le_succ_of_le $ by dsimp [reduce];
        rw [if_pos h]; exact reduce.min t
  | (decidable.is_false h) := by dsimp [reduce]; rw [if_neg h];
      exact add_le_add_right (add_le_add_right (reduce.min t) 1) 1
  end

theorem reduce.idem : ∀ w : word S, reduce S (reduce S w) = reduce S w
| []                            := rfl
| ((sum.inl x)::[])             := rfl
| ((sum.inr x)::[])             := rfl
| ((sum.inl x)::(sum.inl y)::t) :=
    show sum.inl x :: sum.inl y :: reduce.{u} S (reduce S t)
      = sum.inl x :: sum.inl y :: reduce S t,
    from congr_arg _ $ congr_arg _ $ reduce.idem t
| ((sum.inr x)::(sum.inr y)::t) :=
    show sum.inr x :: sum.inr y :: reduce.{u} S (reduce S t)
      = sum.inr x :: sum.inr y :: reduce S t,
    from congr_arg _ $ congr_arg _ $ reduce.idem t
| ((sum.inl x)::(sum.inr y)::t) :=
  match (by apply_instance : decidable (x = y)) with
  | (decidable.is_true  h) := by dsimp [reduce];
      rw [if_pos h]; exact reduce.idem t
  | (decidable.is_false h) := by dsimp [reduce]; rw [if_neg h];
      dsimp [reduce]; rw [if_neg h];
      from congr_arg _ (congr_arg _ (reduce.idem t))
  end
| ((sum.inr x)::(sum.inl y)::t) :=
  match (by apply_instance : decidable (x = y)) with
  | (decidable.is_true  h) := by dsimp [reduce];
      rw [if_pos h]; exact reduce.idem t
  | (decidable.is_false h) := by dsimp [reduce]; rw [if_neg h];
      dsimp [reduce]; rw [if_neg h];
      from congr_arg _ (congr_arg _ (reduce.idem t))
  end

-- TODO
-- def to_word : free_group S → word S :=

end free_group
