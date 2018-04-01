import .functor .morphism

universes u v w u₁ v₁ w₁ u₂ v₂ w₂

namespace category

@[reducible] def functor_category {α β} (C : category.{u v} α) (D : category.{u₁ v₁} β) : category (functor C D) :=
{ Mor := natural_transformation C D,
  Comp := natural_transformation.comp C D,
  Id := natural_transformation.id C D,
  Hid_left := λ F G fg, by cases fg; dsimp [natural_transformation.comp, natural_transformation.id];
    congr; funext; apply D.Hid_left,
  Hid_right := λ F G fg, by cases fg; dsimp [natural_transformation.comp, natural_transformation.id];
    congr; funext; apply D.Hid_right,
  Hassoc := λ F G H I hi gh fg, by cases fg; cases gh; cases hi;
    dsimp [natural_transformation.comp]; congr; funext; apply D.Hassoc }

@[reducible] def cone_category {α β} (J : category.{u v} α) (C : category.{u₁ v₁} β) (F : functor J C) :
  category Σ y : β, natural_transformation J C (functor.to_obj J C y) F :=
{ Mor := λ f g, { fg : C.Mor f.1 g.1 // ∀ x, C.Comp _ _ _ (g.2.mor x) fg = f.2.mor x},
  Comp := λ f g h gh fg, ⟨C.Comp f.1 g.1 h.1 gh.1 fg.1,
    λ x, by cases gh with gh1 gh2; cases fg with fg1 fg2;
    dsimp [functor.to_obj] at *; rw [← C.Hassoc, gh2, fg2]⟩,
  Id := λ f, ⟨C.Id f.1, λ x, C.Hid_right _ _ _⟩,
  Hid_left := λ f g fg, subtype.eq $ C.Hid_left _ _ _,
  Hid_right := λ f g fg, subtype.eq $ C.Hid_right _ _ _,
  Hassoc := λ f g h i hi gh fg, subtype.eq $ C.Hassoc _ _ _ _ _ _ _ }

structure limit {α β} (J : category.{u v} α)
  (C : category.{u₁ v₁} β) (F : functor J C) : Type (max u v u₁ v₁) :=
(obj : β)
(cone : natural_transformation J C (functor.to_obj J C obj) F)
(proj : Π (y) (f : natural_transformation J C (functor.to_obj J C y) F),
  category.Mor (cone_category J C F) ⟨y, f⟩ ⟨obj, cone⟩)
(universal : Π (y) (f : natural_transformation J C (functor.to_obj J C y) F),
  subsingleton $ category.Mor (cone_category J C F) ⟨y, f⟩ ⟨obj, cone⟩)

@[reducible] def binary_product {α} (C : category.{u v} α) (x y : α) :=
limit (discrete bool) C (functor.of_discrete C $ λ b, bool.rec_on b x y)

@[reducible] def product {α} (C : category.{u v} α) (ι) (f : ι → α) :=
limit (discrete ι) C (functor.of_discrete C f)

@[reducible] def product_category {α β} (C : category.{u v} α) (D : category.{u₁ v₁} β) : category (α × β) :=
{ Mor := λ x y, C.Mor x.1 y.1 × D.Mor x.2 y.2,
  Comp := λ x y z f g, (C.Comp _ _ _ f.1 g.1, D.Comp _ _ _ f.2 g.2),
  Id := λ x, (C.Id x.1, D.Id x.2),
  Hid_left := λ x y f, prod.ext.2 ⟨C.Hid_left _ _ _, D.Hid_left _ _ _⟩,
  Hid_right := λ x y f, prod.ext.2 ⟨C.Hid_right _ _ _, D.Hid_right _ _ _⟩,
  Hassoc := λ x y z w f g h, prod.ext.2 ⟨C.Hassoc _ _ _ _ _ _ _, D.Hassoc _ _ _ _ _ _ _⟩ }

@[reducible] def Hom {α} (C : category.{u v} α) : functor (product_category (dual C) C) examples.Set :=
{ F := λ x, C.Mor x.1 x.2,
  mor := λ x y F f, C.Comp _ _ _ (C.Comp _ _ _ F.2 f) F.1,
  Hid := λ x, funext $ λ z, by dsimp [product_category, dual]; rw [C.Hid_right, C.Hid_left]; refl,
  Hcomp := λ x y z f g, funext $ λ z, by dsimp [product_category, dual, examples.Set];
    rw [C.Hassoc, C.Hassoc, C.Hassoc, C.Hassoc, C.Hassoc]; refl }

@[reducible] def natural_isomorphism {α β} (C : category.{u v} α) (D : category.{u₁ v₁} β) :=
isomorphism (functor_category C D)

end category