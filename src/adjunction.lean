import .natural_transformation

universes u v w u₁ v₁ w₁ u₂ v₂ w₂

namespace category

@[reducible] def functor.Hom_right {α β} (C : category.{u v} α) (D : category.{u₁ v₁} β)
  (R : functor C D) : functor (product_category (dual D) C) examples.Set :=
{ F := λ x, D.Mor x.1 (R.F x.2),
  mor := λ x y F f, D.Comp _ _ _ (D.Comp _ _ _ (R.mor _ _ F.2) f) F.1,
  Hid := λ x, funext $ λ z, by dsimp [product_category, dual];
    rw [R.Hid, D.Hid_right, D.Hid_left]; refl,
  Hcomp := λ x y z f g, funext $ λ z, by dsimp [product_category, dual, examples.Set];
    rw [D.Hassoc, D.Hassoc, D.Hassoc, D.Hassoc, ← R.Hcomp, D.Hassoc]; refl }

@[reducible] def functor.Hom_left {α β} (C : category.{u v} α) (D : category.{u₁ v₁} β)
  (L : functor D C) : functor (product_category (dual D) C) examples.Set :=
{ F := λ x, C.Mor (L.F x.1) x.2,
  mor := λ x y F f, C.Comp _ _ _ (C.Comp _ _ _ F.2 f) (L.mor _ _ F.1),
  Hid := λ x, funext $ λ z, by dsimp [product_category, dual];
    rw [L.Hid, C.Hid_right, C.Hid_left]; refl,
  Hcomp := λ x y z f g, funext $ λ z, by dsimp [product_category, dual, examples.Set];
    rw [C.Hassoc, C.Hassoc, C.Hassoc, C.Hassoc, ← L.Hcomp, C.Hassoc]; refl }

structure adjunction {α β} (C : category.{u v} α) (D : category.{u v} β) : Type (max u v) :=
(left : functor D C)
(right : functor C D)
(Hom_iso : natural_isomorphism _ _ (functor.Hom_right C D right) (functor.Hom_left C D left))

end category