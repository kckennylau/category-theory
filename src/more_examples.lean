import .natural_transformation

universes u v

namespace category

namespace examples

def Cat : category Σ α : Type u, category.{u v} α :=
{ Mor := λ C D, functor C.2 D.2,
  Comp := λ C D E, functor.comp C.2 D.2 E.2,
  Id := λ C, functor.id C.2,
  Hid_left := λ C D F, by cases F; refl,
  Hid_right := λ C D F, by cases F; refl,
  Hassoc := λ _ _ _ _ _ _ _, rfl, }

def Set_ : category Σ c d, Set.Mor punit d :=
coslice Set punit

def Set_.forgetful : functor Set_ Set :=
comma.right _ _ _ _ _

def Grp.forgetful : functor Grp Set_ :=
{ F := λ G, ⟨(), G.1, λ _, @has_one.one G.1 (@monoid.to_has_one G.1 (@group.to_monoid G.1 G.2))⟩,
  mor := λ G H f, ⟨(plift.up rfl, λ x, f.1 x),
    funext $ λ x, eq.symm $ @is_group_hom.one G.1 H.1 G.2 H.2 f.1 f.2⟩,
  Hid := λ G, rfl,
  Hcomp := λ G H K f g, rfl }

instance add_comm_group.to_comm_group (α : Type u) [add_comm_group α] : comm_group α :=
{ mul := (+),
  mul_assoc := add_assoc,
  one := 0,
  one_mul := zero_add,
  mul_one := add_zero,
  inv := has_neg.neg,
  mul_left_inv := add_left_neg,
  mul_comm := add_comm }

def Ab.forgetful : functor Ab Grp :=
{ F := λ G, ⟨G.1, by letI := G.2; apply_instance⟩,
  mor := λ G H, id,
  Hid := λ G, rfl,
  Hcomp := λ G H K f g, rfl }

def Cat.forgetful : functor Cat Set :=
{ F := λ C, C.1,
  mor := λ C D F, F.F,
  Hid := λ C, rfl,
  Hcomp := λ C D E F G, rfl }

def Preord.forgetful : functor Preord Set :=
{ F := λ C, C.1,
  mor := λ C D f, f.1,
  Hid := λ C, rfl,
  Hcomp := λ C D E F G, rfl }

def Top.forgetful : functor Top Set :=
{ F := λ C, C.1,
  mor := λ C D f, f.1,
  Hid := λ C, rfl,
  Hcomp := λ C D E F G, rfl }

def Top_ : category Σ c d, Top.Mor ⟨punit, ⊤⟩ d :=
coslice Top ⟨punit, ⊤⟩

def Set.binary_product (x y) : binary_product Set x y :=
{ obj := x × y,
  cone :=
  { mor := λ b f, bool.rec_on b f.1 f.2,
    Hcomp := λ b₁ b₂ ⟨hb⟩, by clear _x _fun_match;
      subst hb; funext; refl },
  proj := λ z f, ⟨λ t, (f.mor ff t, f.mor tt t),
    λ b, funext $ λ t, bool.rec_on b rfl rfl⟩,
  universal := λ z F, subsingleton.intro $ λ f g, subtype.eq $ funext $
    λ t, prod.ext.2 ⟨(congr_fun (f.2 ff) t).trans $ (congr_fun (g.2 ff) t).symm,
    (congr_fun (f.2 tt) t).trans $ (congr_fun (g.2 tt) t).symm⟩ }

def Set.product (ι : Type v) (f : ι → Type (max u v)) : product Set ι f :=
{ obj := Π i, f i,
  cone :=
  { mor := λ i f, f i,
    Hcomp := λ i₁ i₂ ⟨hi⟩, by clear _x _fun_match;
      subst hi; funext; refl },
  proj := λ z f, ⟨λ t i, f.mor i t, λ b, funext $ λ t, rfl⟩,
  universal := λ z F, subsingleton.intro $ λ f g, subtype.eq $ funext $
    λ t, funext $ λ i, (congr_fun (f.2 i) t).trans (congr_fun (g.2 i) t).symm }

def Grp.opposite : functor Grp Grp :=
{ F := λ G, ⟨G.1, by letI := G.2; exact
  { mul := λ x y, y * x,
    mul_assoc := λ x y z, (mul_assoc z y x).symm,
    one := 1,
    one_mul := mul_one,
    mul_one := one_mul,
    inv := has_inv.inv,
    mul_left_inv := mul_inv_self }⟩,
  mor := λ G H f, ⟨λ x, f.1 x, λ x y, f.2 y x⟩,
  Hid := λ G, subtype.eq rfl,
  Hcomp := λ G H K f g, subtype.eq rfl }

def Grp.natural_transformation : natural_transformation Grp Grp (functor.id Grp) Grp.opposite :=
{ mor := λ G, by letI := G.2; exact ⟨λ x, x⁻¹, λ x y, mul_inv_rev x y⟩,
  Hcomp := λ G H f, subtype.eq $ funext $ λ x, by letI := G.2; letI := H.2; exact f.2.inv x }

end examples

end category