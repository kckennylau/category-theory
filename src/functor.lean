import .examples

universes u v w u₁ v₁ w₁ u₂ v₂ w₂

namespace category

namespace functor

variables {α : Type u} (C : category.{u v} α)
variables {β : Type u₁} (D : category.{u₁ v₁} β)
variables {γ : Type u₂} (E : category.{u₂ v₂} γ)

@[reducible] def obj (x : α) : functor examples.one C :=
{ F := λ _, x,
  mor := λ _ _ _, C.Id x,
  Hid := λ _, rfl,
  Hcomp := λ _ _ _ _ _, C.Hid_left x x (C.Id x) }

@[reducible] def to_obj (y : β) : functor C D :=
{ F := λ _, y,
  mor := λ _ _ _, D.Id y,
  Hid := λ _, rfl,
  Hcomp := λ _ _ _ _ _, D.Hid_left y y (D.Id y) }

@[reducible] def of_discrete (f : α → β) : functor (discrete α) D :=
{ F := f,
  mor := λ x y hxy, eq.rec_on hxy.1 $ D.Id (f x),
  Hid := λ x, rfl,
  Hcomp := λ x y z ⟨hyz⟩ ⟨hxy⟩, by clear _fun_match _fun_match _x _x;
    subst hyz; subst hxy; dsimp; apply D.Hid_left }

end functor

@[reducible] def comma {α : Type u} (C : category.{u v} α)
  {β : Type u₁} (D : category.{u₁ v₁} β)
  {γ : Type u₂} (E : category.{u₂ v₂} γ)
  (F : functor C E) (G : functor D E) :
  category Σ c d, E.Mor (F.F c) (G.F d) :=
{ Mor := λ x y, { P : C.Mor x.1 y.1 × D.Mor x.2.1 y.2.1 //
      E.Comp (F.F x.1) (F.F y.1) (G.F y.2.1) y.2.2 (F.mor x.1 y.1 P.1)
    = E.Comp (F.F x.1) (G.F x.2.1) (G.F y.2.1) (G.mor x.2.1 y.2.1 P.2) x.2.2 },
  Comp := λ x y z P Q, ⟨(C.Comp x.1 y.1 z.1 P.1.1 Q.1.1, D.Comp x.2.1 y.2.1 z.2.1 P.1.2 Q.1.2),
    by rw [← F.Hcomp, ← G.Hcomp, E.Hassoc, ← Q.2, ← E.Hassoc, P.2, E.Hassoc]⟩,
  Id := λ x, ⟨(C.Id x.1, D.Id x.2.1), by rw [F.Hid, G.Hid, E.Hid_left, E.Hid_right]⟩,
  Hid_left := λ x y P, subtype.eq $ by dsimp; rw [C.Hid_left, D.Hid_left]; cases P.1; refl,
  Hid_right := λ x y P, subtype.eq $ by dsimp; rw [C.Hid_right, D.Hid_right]; cases P.1; refl,
  Hassoc := λ x y z w P Q R, subtype.eq $ by dsimp; rw [C.Hassoc, D.Hassoc] }

@[reducible] def arrow {α : Type u} (C : category.{u v} α) : category Σ c d, C.Mor c d :=
comma C C C (functor.id C) (functor.id C)

@[reducible] def slice {α : Type u} (C : category.{u v} α) (x : α) : category Σ c d, C.Mor c x :=
comma C examples.one C (functor.id C) (functor.obj C x)

@[reducible] def coslice {α : Type u} (C : category.{u v} α) (x : α) : category Σ c d, C.Mor x d :=
comma examples.one C C (functor.obj C x) (functor.id C)

namespace comma

variables {α : Type u} (C : category.{u v} α)
variables {β : Type u₁} (D : category.{u₁ v₁} β)
variables {γ : Type u₂} (E : category.{u₂ v₂} γ)
variables (F : functor C E) (G : functor D E)

@[reducible] def left : functor (comma C D E F G) C :=
{ F := λ x, x.1,
  mor := λ x y P, P.1.1,
  Hid := λ x, rfl,
  Hcomp := λ x y z P Q, rfl }

@[reducible] def right : functor (comma C D E F G) D :=
{ F := λ x, x.2.1,
  mor := λ x y P, P.1.2,
  Hid := λ x, rfl,
  Hcomp := λ x y z P Q, rfl }

@[reducible] def arrow : functor (comma C D E F G) (arrow E) :=
{ F := λ x, ⟨_, _, x.2.2⟩,
  mor := λ x y P, ⟨(F.mor _ _ P.1.1, G.mor _ _ P.1.2), P.2⟩,
  Hid := λ x, subtype.eq $ by dsimp [arrow, comma]; rw [F.Hid, G.Hid],
  Hcomp := λ x y z P Q, subtype.eq $ by dsimp [arrow, comma]; rw [F.Hcomp, G.Hcomp] }

end comma

end category