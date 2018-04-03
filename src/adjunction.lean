import .natural_transformation

universes u v w u₁ v₁ w₁ u₂ v₂ w₂

namespace category

@[reducible] def functor.Hom_left {α β} (C : category.{u v} α) (D : category.{u₁ v₁} β)
  (L : functor D C) : functor (product_category (dual D) C) examples.Set :=
{ F := λ x, C.Mor (L.F x.1) x.2,
  mor := λ x y F f, C.Comp _ _ _ (C.Comp _ _ _ F.2 f) (L.mor _ _ F.1),
  Hid := λ x, funext $ λ z, by dsimp [product_category, dual];
    rw [L.Hid, C.Hid_right, C.Hid_left]; refl,
  Hcomp := λ x y z f g, funext $ λ z, by dsimp [product_category, dual, examples.Set];
    rw [C.Hassoc, C.Hassoc, C.Hassoc, C.Hassoc, ← L.Hcomp, C.Hassoc]; refl }

@[reducible] def functor.Hom_right {α β} (C : category.{u v} α) (D : category.{u₁ v₁} β)
  (R : functor C D) : functor (product_category (dual D) C) examples.Set :=
{ F := λ x, D.Mor x.1 (R.F x.2),
  mor := λ x y F f, D.Comp _ _ _ (D.Comp _ _ _ (R.mor _ _ F.2) f) F.1,
  Hid := λ x, funext $ λ z, by dsimp [product_category, dual];
    rw [R.Hid, D.Hid_right, D.Hid_left]; refl,
  Hcomp := λ x y z f g, funext $ λ z, by dsimp [product_category, dual, examples.Set];
    rw [D.Hassoc, D.Hassoc, D.Hassoc, D.Hassoc, ← R.Hcomp, D.Hassoc]; refl }

structure adjunction {α β} (C : category.{u v} α) (D : category.{u v} β) : Type (max u v) :=
(left : functor D C)
(right : functor C D)
(Hom_iso : natural_isomorphism _ _ (functor.Hom_left C D left) (functor.Hom_right C D right))

section make

variables {α : Type u} {β : Type u}
variables (C : category.{u v} α) (D : category.{u v} β)
variables (left : functor D C) (right : functor C D)
variables (extend : Π x y, D.Mor x (right.F y) → C.Mor (left.F x) y)
variables (descend : Π x y, C.Mor (left.F x) y → D.Mor x (right.F y))
variables (descend_natural : ∀ (x₁ x₂ y₁ y₂) (cf : C.Mor x₁ x₂) (df : D.Mor y₂ y₁) (t : C.Mor (left.F y₁) x₁),
    descend _ _ (C.Comp _ _ _ (C.Comp _ _ _ cf t) (left.mor _ _ df))
  = D.Comp _ _ _ (D.Comp _ _ _ (right.mor x₁ x₂ cf) (descend _ _ t)) df)
variables (extend_natural : ∀ (x₁ x₂ y₁ y₂) (cf : C.Mor x₁ x₂) (df : D.Mor y₂ y₁) (t : D.Mor y₁ (right.F x₁)),
    extend _ _ (D.Comp _ _ _ (D.Comp _ _ _ (right.mor _ _ cf) t) df) =
    C.Comp _ _ _ (C.Comp _ _ _ cf (extend _ _ t)) (left.mor y₂ y₁ df))
variables (extend_descend : ∀ x y (f : C.Mor (left.F x) y), extend _ _ (descend _ _ f) = f)
variables (descend_extend : ∀ x y (f : D.Mor x (right.F y)), descend _ _ (extend _ _ f) = f)
include extend_descend descend_extend

def adjunction.make : adjunction C D :=
{ left := left,
  right := right,
  Hom_iso :=
  { to_mor :=
    { mor := λ x, descend x.1 x.2,
      Hcomp := λ x y f, funext $ λ t, descend_natural _ _ _ _ _ _ _ },
    inv_mor :=
    { mor := λ x, extend x.1 x.2,
      Hcomp := λ x y f, funext $ λ t, extend_natural _ _ _ _ _ _ _ },
    split_monomorphism := begin dsimp [natural_transformation.comp],
        congr, funext, dsimp, apply extend_descend end,
    split_epimorphism := begin dsimp [natural_transformation.comp],
        congr, funext, dsimp, apply descend_extend end } }

end make

section free_forgetful

variables {α : Type (u+1)} (C : category.{u+1 u} α)
variables (free : functor examples.Set.{u} C)
variables (forgetful : functor C examples.Set.{u})
variables (extend : Π x y, (x → (forgetful.F y)) → C.Mor (free.F x) y)
variables (descend : Π x y, C.Mor (free.F x) y → x → (forgetful.F y))
variables (descend_natural : ∀ (x₁ x₂ y₁ y₂) (cf : C.Mor x₁ x₂) (df : y₂ → y₁) (t : C.Mor (free.F y₁) x₁) z,
    descend _ _ (C.Comp _ _ _ (C.Comp _ _ _ cf t) (free.mor _ _ df)) z
  = (forgetful.mor x₁ x₂ cf) ((descend _ _ t) (df z)))
variables (extend_natural : ∀ (x₁ x₂ y₁ y₂) (cf : C.Mor x₁ x₂) (df : y₂ → y₁) (t : y₁ → forgetful.F x₁),
    extend _ _ ((forgetful.mor _ _ cf) ∘ t ∘ df) =
    C.Comp _ _ _ (C.Comp _ _ _ cf (extend _ _ t)) (free.mor y₂ y₁ df))
variables (extend_descend : ∀ x y (f : C.Mor (free.F x) y), extend _ _ (descend _ _ f) = f)
variables (descend_extend : ∀ x y (f : x → (forgetful.F y)), descend _ _ (extend _ _ f) = f)

def adjunction.free_forgetful : adjunction.{u+1 u} C examples.Set.{u} :=
adjunction.make _ _ free forgetful extend descend
  (λ _ _ _ _ _ _ _, funext $ λ _, descend_natural _ _ _ _ _ _ _ _)
  extend_natural
  extend_descend descend_extend

end free_forgetful

def adjunction.id {α} (C : category.{u v} α) : adjunction C C :=
adjunction.make _ _
  (functor.id C) (functor.id C)
  (λ x y, id) (λ x y, id)
  (λ _ _ _ _ _ _ _, rfl)
  (λ _ _ _ _ _ _ _, rfl)
  (λ _ _ _, rfl)
  (λ _ _ _, rfl)

def adjunction.comp {α β γ} (C : category.{u v} α)
  (D : category.{u v} β) (E : category.{u v} γ)
  (F : adjunction D E) (G : adjunction C D) :
  adjunction C E :=
{ left := functor.comp _ _ _ G.left F.left,
  right := functor.comp _ _ _ F.right G.right,
  Hom_iso :=
  { to_mor :=
    { mor := λ x z, F.3.1.1 (_, _) (G.3.1.1 (_, _) z),
      Hcomp := λ x y z, funext $ λ t,
        by have h1 := congr_fun (G.3.1.2 (F.1.1 x.1, x.2) (F.1.1 y.1, y.2) (F.1.2 _ _ z.1, z.2)) t;
        have h2 := congr_fun (F.3.1.2 (x.1, G.2.1 x.2) (y.1, G.2.1 y.2) (z.1, G.2.2 _ _ z.2)) (G.3.1.1 (_, _) t);
        dsimp at *; rw [h1, h2] },
    inv_mor :=
    { mor := λ x z, G.3.2.1 (_, _) (F.3.2.1 (_, _) z),
      Hcomp := λ x y z, funext $ λ t,
        by have h1 := congr_fun (F.3.2.2 (x.1, G.2.1 x.2) (y.1, G.2.1 y.2) (z.1, G.2.2 _ _ z.2)) t;
        have h2 := congr_fun (G.3.2.2 (F.1.1 x.1, x.2) (F.1.1 y.1, y.2) (F.1.2 _ _ z.1, z.2)) (F.3.2.1 (_, _) t);
        dsimp at *; rw [h1, h2] },
    split_monomorphism := by have h1 := congr_fun (natural_transformation.mk.inj F.3.3);
      have h2 := congr_fun (natural_transformation.mk.inj G.3.3);
      dsimp [natural_transformation.comp] at *; congr; funext x f;
      replace h1 := congr_fun (h1 (x.1, G.2.1 x.2)) (G.3.1.1 (_, _) f);
      replace h2 := congr_fun (h2 (F.1.1 x.1, x.2)) f;
      dsimp at *; rw [h1, h2],
    split_epimorphism := by have h1 := congr_fun (natural_transformation.mk.inj G.3.4);
      have h2 := congr_fun (natural_transformation.mk.inj F.3.4);
      dsimp [natural_transformation.comp] at *; congr; funext x f;
      replace h1 := congr_fun (h1 (F.1.1 x.1, x.2)) (F.3.2.1 (_, _) f);
      replace h2 := congr_fun (h2 (x.1, G.2.1 x.2)) f;
      dsimp at *; rw [h1, h2] } }

end category