import .basic

universes u v

namespace category

variables {α : Type u} (C : category.{u v} α)
variables {x y z : α} (f : C.Mor x y)

@[reducible] def monomorphism : Prop :=
∀ {z : α} (g h : C.Mor z x) (H : C.Comp _ _ _ f g = C.Comp _ _ _ f h), g = h

@[reducible] def epimorphism : Prop :=
∀ {z : α} (g h : C.Mor y z) (H : C.Comp _ _ _ g f = C.Comp _ _ _ h f), g = h

@[reducible] def split_monomorphism : Type v :=
{ g : C.Mor y x // C.Comp _ _ _ g f = C.Id x }

@[reducible] def split_epimorphism : Type v :=
{ g : C.Mor y x // C.Comp _ _ _ f g = C.Id y }

variables x y

structure isomorphism : Type v :=
(to_mor : C.Mor x y)
(inv_mor : C.Mor y x)
(split_monomorphism : C.Comp _ _ _ inv_mor to_mor = C.Id x)
(split_epimorphism : C.Comp _ _ _ to_mor inv_mor = C.Id y)

@[refl] def isomorphism.refl : isomorphism C x x :=
⟨C.Id x, C.Id x, C.Hid_left _ _ _, C.Hid_right _ _ _⟩

@[symm] def isomorphism.symm (e : isomorphism C x y) : isomorphism C y x :=
⟨e.inv_mor, e.to_mor, e.split_epimorphism, e.split_monomorphism⟩

@[trans] def isomorphism.trans (e₁ : isomorphism C x y) (e₂ : isomorphism C y z) : isomorphism C x z :=
⟨C.Comp _ _ _ e₂.to_mor e₁.to_mor,
 C.Comp _ _ _ e₁.inv_mor e₂.inv_mor,
 by rw [C.Hassoc, ← C.Hassoc x y, e₂.split_monomorphism, C.Hid_left, e₁.split_monomorphism],
 by rw [C.Hassoc, ← C.Hassoc z y, e₁.split_epimorphism, C.Hid_left, e₂.split_epimorphism]⟩

end category