import algebra.group
import analysis.topology.continuity
import linear_algebra.linear_map_module
import algebra.group_power

universes u v w u₁ v₁ w₁ u₂ v₂ w₂

structure category (α : Type u) : Type (max u v + 1) :=
(Mor : Π x y : α, Type v)
(Comp : Π x y z, Mor y z → Mor x y → Mor x z)
(Id : Π x, Mor x x)
(Hid_left : ∀ x y (f : Mor x y), Comp _ _ _ (Id _) f = f)
(Hid_right : ∀ x y (f : Mor x y), Comp _ _ _ f (Id _) = f)
(Hassoc : ∀ x y z w (f : Mor z w) (g : Mor y z) (h : Mor x y), Comp _ _ _ (Comp _ _ _ f g) h = Comp _ _ _ f (Comp _ _ _ g h))

namespace category

def dual {α : Type u} (C : category α) : category α :=
{ Mor := λ x y, C.Mor y x,
  Comp := λ x y z f g, C.Comp z y x g f,
  Id := C.Id,
  Hid_left := λ x y, C.Hid_right y x,
  Hid_right := λ x y, C.Hid_left y x,
  Hassoc := λ x y z w f g h, eq.symm $ C.Hassoc w z y x h g f }

def discrete (α : Type u) : category α :=
{ Mor := λ x y, plift $ x = y,
  Comp := λ x y z hyz hxy, plift.up $ eq.trans hxy.down hyz.down,
  Id := λ x, plift.up $ eq.refl x,
  Hid_left := λ x y hxy, by cases hxy; refl,
  Hid_right := λ x y hxy, by cases hxy; refl,
  Hassoc := λ _ _ _ _ _ _ _, rfl }

namespace cone

variables {α : Type u} (C : category.{u v} α)

def Mor : option α → option α → Type v
| none y := punit
| _ none := ulift empty
| (some x) (some y) := C.Mor x y

def Comp : Π x y z, Mor C y z → Mor C x y → Mor C x z
| none none _ f _ := f
| none _ (some z) _ _ := punit.star
| (some x) (some y) (some z) f g := C.Comp x y z f g

def Id : Π x, Mor C x x
| none := punit.star
| (some x) := C.Id x

def Hid_left : ∀ x y f, Comp C x y y (Id C y) f = f
| none y f := by cases y; cases f; refl
| (some x) (some y) f := C.Hid_left x y f

def Hid_right : ∀ x y f, Comp C x x y f (Id C x) = f
| none y f := by cases y; cases f; refl
| (some x) (some y) f := C.Hid_right x y f

def Hassoc : ∀ x y z w f g h, Comp C x y w (Comp C y z w f g) h = Comp C x z w f (Comp C x y z g h)
| none none z w f g h := by cases z; cases w; refl
| none (some y) (some z) (some w) f g h := rfl
| (some x) (some y) (some z) (some w) f g h := C.Hassoc x y z w f g h

end cone

def cone {α : Type u} (C : category α) : category (option α) :=
{ Mor := cone.Mor C,
  Comp := cone.Comp C,
  Id := cone.Id C,
  Hid_left := cone.Hid_left C,
  Hid_right := cone.Hid_right C,
  Hassoc := cone.Hassoc C }

structure functor {α β} (C : category.{u v} α) (D : category.{u₁ v₁} β) :=
(F : α → β)
(mor : Π x y, C.Mor x y → D.Mor (F x) (F y))
(Hid : ∀ x, mor x x (C.Id x) = D.Id (F x))
(Hcomp : ∀ x y z f g, D.Comp (F x) (F y) (F z) (mor y z f) (mor x y g) = mor x z (C.Comp x y z f g))

namespace functor

variables {α : Type u} (C : category.{u v} α)
variables {β : Type u₁} (D : category.{u₁ v₁} β)
variables {γ : Type u₂} (E : category.{u₂ v₂} γ)

def id : functor C C :=
{ F := id,
  mor := λ x y, id,
  Hid := λ x, rfl,
  Hcomp := λ x y z f g, rfl }

def comp (F : functor D E) (G : functor C D) : functor C E :=
{ F := F.F ∘ G.F,
  mor := λ x y, F.mor (G.F x) (G.F y) ∘ G.mor x y,
  Hid := λ x, by simp [G.Hid, F.Hid],
  Hcomp := λ x y z f g, by simp [G.Hcomp, F.Hcomp] }

end functor

structure natural_transformation {α β} (C : category.{u v} α) (D : category.{u₁ v₁} β) (F G : functor C D) :=
(mor : Π x : α, D.Mor (F.F x) (G.F x))
(Hcomp : ∀ x y f, D.Comp _ _ _ (mor y) (F.mor _ _ f) = D.Comp _ _ _ (G.mor _ _ f) (mor x))

namespace natural_transformation

def id {α β} (C : category.{u v} α) (D : category.{u₁ v₁} β) (F : functor C D) :
  natural_transformation C D F F :=
{ mor := λ x, D.Id _,
  Hcomp := λ x y f, (D.Hid_left _ _ _).trans (D.Hid_right _ _ _).symm }

def comp {α β} (C : category.{u v} α) (D : category.{u₁ v₁} β) (F G H : functor C D)
  (gh : natural_transformation C D G H)
  (fg : natural_transformation C D F G) : natural_transformation C D F H :=
{ mor := λ x, D.Comp _ _ _ (gh.mor x) (fg.mor x),
  Hcomp := λ x y f, by rw [D.Hassoc, fg.Hcomp, ← D.Hassoc, gh.Hcomp, D.Hassoc] }

end natural_transformation

end category
