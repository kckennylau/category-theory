import .natural_transformation .free_group .tensor_product

universes u v

namespace category

namespace examples

@[reducible] def Cat : category Σ α : Type u, category.{u v} α :=
{ Mor := λ C D, functor C.2 D.2,
  Comp := λ C D E, functor.comp C.2 D.2 E.2,
  Id := λ C, functor.id C.2,
  Hid_left := λ C D F, by cases F; refl,
  Hid_right := λ C D F, by cases F; refl,
  Hassoc := λ _ _ _ _ _ _ _, rfl, }

@[reducible] def Set_ : category Σ c d, Set.Mor punit d :=
coslice Set punit

@[reducible] def Set_.forgetful : functor Set_ Set :=
comma.right _ _ _ _ _

@[reducible] def Set_.free : functor Set Set_ :=
{ F := λ S, ⟨(), option S, λ x, none⟩ ,
  mor := λ S T f, ⟨(plift.up $ rfl, option.map f), funext $ λ x, rfl⟩,
  Hid := λ S, subtype.eq $ prod.ext.2 $ ⟨rfl, funext $ λ x, option.rec_on x rfl $ λ t, rfl⟩,
  Hcomp := λ S T U f g, by dsimp; congr; funext; cases x; funext; refl }

@[reducible] def Grp.forgetful : functor Grp Set_ :=
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

@[reducible] def Ab.forgetful : functor Ab Grp :=
{ F := λ G, ⟨G.1, by letI := G.2; apply_instance⟩,
  mor := λ G H, id,
  Hid := λ G, rfl,
  Hcomp := λ G H K f g, rfl }

@[reducible] def Cat.forgetful : functor Cat Set :=
{ F := λ C, C.1,
  mor := λ C D F, F.F,
  Hid := λ C, rfl,
  Hcomp := λ C D E F G, rfl }

@[reducible] def Preord.forgetful : functor Preord Set :=
{ F := λ C, C.1,
  mor := λ C D f, f.1,
  Hid := λ C, rfl,
  Hcomp := λ C D E F G, rfl }

@[reducible] def Top.forgetful : functor Top Set :=
{ F := λ C, C.1,
  mor := λ C D f, f.1,
  Hid := λ C, rfl,
  Hcomp := λ C D E F G, rfl }

@[reducible] def Top_ : category Σ c d, Top.Mor ⟨punit, ⊤⟩ d :=
coslice Top ⟨punit, ⊤⟩

@[reducible] def Set.binary_product (x y) : binary_product Set x y :=
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

@[reducible] def Set.product (ι : Type v) (f : ι → Type (max u v)) : product Set ι f :=
{ obj := Π i, f i,
  cone :=
  { mor := λ i f, f i,
    Hcomp := λ i₁ i₂ ⟨hi⟩, by clear _x _fun_match;
      subst hi; funext; refl },
  proj := λ z f, ⟨λ t i, f.mor i t, λ b, funext $ λ t, rfl⟩,
  universal := λ z F, subsingleton.intro $ λ f g, subtype.eq $ funext $
    λ t, funext $ λ i, (congr_fun (f.2 i) t).trans (congr_fun (g.2 i) t).symm }

@[reducible] def Grp.opposite : functor Grp Grp :=
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

@[reducible] def Grp.natural_transformation : natural_transformation Grp Grp (functor.id Grp) Grp.opposite :=
{ mor := λ G, by letI := G.2; exact ⟨λ x, x⁻¹, λ x y, mul_inv_rev x y⟩,
  Hcomp := λ G H f, subtype.eq $ funext $ λ x, by letI := G.2; letI := H.2; exact f.2.inv x }

@[reducible] def Set.product_functor (B : Type u) : functor Set Set :=
{ F := λ A, A × B,
  mor := λ A₁ A₂ f x, (f x.1, x.2),
  Hid := λ A, funext $ λ x, prod.ext.2 $ ⟨rfl, rfl⟩,
  Hcomp := λ A₁ A₂ A₃ f g, funext $ λ x, prod.ext.2 $ ⟨rfl, rfl⟩ }

@[reducible] def Set.Hom_functor_right (B : Type u) : functor Set Set :=
{ F := λ C, B → C,
  mor := λ C₁ C₂ f g t, f (g t),
  Hid := λ C, rfl,
  Hcomp := λ C₁ C₂ C₃ f g, rfl }

@[reducible] def Top.discrete : functor Set Top :=
{ F := λ S, ⟨S, ⊤⟩,
  mor := λ C D f, ⟨f, continuous_top⟩,
  Hid := λ C, rfl,
  Hcomp := λ C D E F G, rfl }

@[reducible] def Top.indiscrete : functor Set Top :=
{ F := λ S, ⟨S, ⊥⟩,
  mor := λ C D f, ⟨f, continuous_bot⟩,
  Hid := λ C, rfl,
  Hcomp := λ C D E F G, rfl }

@[reducible] def Grp.free : functor Set Grp :=
{ F := λ S, ⟨free_group S, free_group.group S⟩,
  mor := λ S T f, ⟨free_group.to_group S (free_group T) (free_group.of_type T ∘ f),
    free_group.to_group.is_group_hom _ _ _⟩,
  Hid := λ S, subtype.eq $ funext $ λ x, eq.symm $
    free_group.to_group.unique _ _ _ _ (λ x y, rfl) (λ x, rfl) _,
  Hcomp := λ S T U f g, subtype.eq $ funext $
    λ x, free_group.to_group.unique _ _ _ _
      (λ x y, by dsimp; rw [free_group.to_group.is_group_hom, free_group.to_group.is_group_hom])
      (λ x, by dsimp; rw [free_group.to_group.commutes, free_group.to_group.commutes]) _ }

@[reducible] def Mod.Hom_functor_right (R : Type u) [comm_ring R] 
  (N : Type v) [module R N] : functor (Mod R) (Mod R) :=
{ F := λ P, ⟨@linear_map _ N P.1 _ _ P.2, @linear_map.module _ N P.1 _ _ P.2⟩,
  mor := λ P₁ P₂ f, ⟨λ g, ⟨f.1 ∘ g.1, by letI := P₁.2; letI := P₂.2; apply is_linear_map.comp f.2 g.2⟩,
    { add := λ T₁ T₂, subtype.eq $ funext $ λ x, by letI := P₁.2; letI := P₂.2; from f.2.1 (T₁.1 x) (T₂.1 x),
      smul := λ c T₂, subtype.eq $ funext $ λ x, by letI := P₁.2; letI := P₂.2; from f.2.2 c (T₂.1 x) }⟩,
  Hid := λ C, subtype.eq $ funext $ λ T, subtype.eq $ rfl,
  Hcomp := λ C₁ C₂ C₃ f g, subtype.eq $ funext $ λ T, subtype.eq $ rfl }

@[reducible] noncomputable def Mod.tensor (R : Type u) [comm_ring R]
  (N : Type v) [module R N] : functor (Mod R) (Mod R) :=
{ F := λ M, ⟨@tensor_product _ M.1 N _ M.2 _, @tensor_product.module _ _ M.1 N M.2 _⟩,
  mor := λ M₁ M₂ f, ⟨@tensor_product.tprod_map _ _ M₁.1 M₂.1 N N M₁.2 M₂.2 _ _ f.1 f.2 id is_linear_map.id,
    @tensor_product.tprod_map.linear _ _ M₁.1 M₂.1 N N M₁.2 M₂.2 _ _ f.1 f.2 id is_linear_map.id⟩,
  Hid := λ M, subtype.eq $ eq.symm $ by letI := M.2; from tensor_product.universal_property.factor_unique _ _ is_linear_map.id (λ x y, rfl),
  Hcomp := λ M₁ M₂ M₃ f g, subtype.eq $ by letI := M₁.2; letI := M₂.2; letI := M₃.2;
    from tensor_product.universal_property.factor_unique _ _
      (is_linear_map.comp
        (tensor_product.universal_property.factor_linear _)
        (tensor_product.universal_property.factor_linear _))
      (λ x y, by dsimp; rw tensor_product.tprod_map.commutes;
        rw tensor_product.tprod_map.commutes; refl) }

end examples

end category