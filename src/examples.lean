import .basic

universes u v

namespace category

namespace examples

@[reducible] def Set : category (Type u) :=
{ Mor := λ S T, S → T,
  Comp := λ S T U, (∘),
  Id := @id,
  Hid_left := λ S T f, rfl,
  Hid_right := λ S T f, rfl,
  Hassoc := λ S T U V f g h, rfl }

@[reducible] def set : category Σ α : Type u, fintype α :=
{ Mor := λ S T, S.1 → T.1,
  Comp := λ S T U, (∘),
  Id := λ S, @id S.1,
  Hid_left := λ S T f, rfl,
  Hid_right := λ S T f, rfl,
  Hassoc := λ S T U V f g h, rfl }

@[reducible] def Mon : category Σ α : Type u, monoid α :=
{ Mor := λ G H, { f : G.1 → H.1 // by letI := G.2; letI := H.2;
    exact (∀ x y, f (x * y) = f x * f y) ∧ f 1 = 1 },
  Comp := λ G H K f g, ⟨f.1 ∘ g.1,
    λ x y, by dsimp; rw [g.2.1, f.2.1],
    by dsimp; rw [g.2.2, f.2.2]⟩,
  Id := λ G, ⟨id, λ x y, rfl, rfl⟩,
  Hid_left := λ G H f, subtype.eq rfl,
  Hid_right := λ G H f, subtype.eq rfl,
  Hassoc := λ G H K N f g h, subtype.eq rfl }

@[reducible] def Grp : category Σ α : Type u, group α :=
{ Mor := λ G H, { f : G.1 → H.1 // @is_group_hom _ _ G.2 H.2 f },
  Comp := λ G H K f g, ⟨f.1 ∘ g.1, λ x y, calc
          f.1 (g.1 _)
        = f.1 _ : congr_arg f.1 (g.2 x y)
    ... = _ : f.2 _ _⟩,
  Id := λ G, ⟨id, λ x y, rfl⟩,
  Hid_left := λ G H f, subtype.eq rfl,
  Hid_right := λ G H f, subtype.eq rfl,
  Hassoc := λ G H K N f g h, subtype.eq rfl }

@[reducible] def Top : category Σ α : Type u, topological_space α :=
{ Mor := λ X Y, { f : X.1 → Y.1 // @continuous _ _ X.2 Y.2 f },
  Comp := λ X Y Z f g, ⟨f.1 ∘ g.1, @continuous.comp X.1 Y.1 Z.1 X.2 Y.2 Z.2 g.1 f.1 g.2 f.2⟩,
  Id := λ X, ⟨id, @continuous_id X.1 X.2⟩,
  Hid_left := λ x y f, subtype.eq rfl,
  Hid_right := λ x y f, subtype.eq rfl,
  Hassoc := λ x y z w f g h, subtype.eq rfl }

@[reducible] def Ab : category Σ α : Type u, add_comm_group α :=
{ Mor := λ G H, { f : G.1 → H.1 // by letI := G.2; letI := H.2; exact ∀ x y, f (x + y) = f x + f y },
  Comp := λ G H K f g, ⟨f.1 ∘ g.1, λ x y, calc
          f.1 (g.1 _)
        = f.1 _ : congr_arg f.1 (g.2 x y)
    ... = _ : f.2 _ _⟩,
  Id := λ G, ⟨id, λ x y, rfl⟩,
  Hid_left := λ G H f, subtype.eq rfl,
  Hid_right := λ G H f, subtype.eq rfl,
  Hassoc := λ G H K N f g h, subtype.eq rfl }

@[reducible] def Mod (α : Type u) [ring α] : category Σ β : Type v, module α β :=
{ Mor := λ M N, @linear_map _ M.1 N.1 _ M.2 N.2,
  Comp := λ M N P f g, ⟨f.1 ∘ g.1, @is_linear_map.comp _ N.1 P.1 M.1 _ N.2 P.2 M.2 f.1 g.1 f.2 g.2⟩,
  Id := λ M, ⟨id, @is_linear_map.id _ M.1 _ M.2⟩,
  Hid_left := λ G H f, subtype.eq rfl,
  Hid_right := λ G H f, subtype.eq rfl,
  Hassoc := λ G H K N f g h, subtype.eq rfl }

@[reducible] def of_poset (α : Type u) [partial_order α] : category α :=
{ Mor := λ x y, plift $ x ≤ y,
  Comp := λ x y z hyz hxy, plift.up $ le_trans hxy.down hyz.down,
  Id := λ x, plift.up $ le_refl x,
  Hid_left := λ x y ⟨hxy⟩, rfl,
  Hid_right := λ x y ⟨hxy⟩, rfl,
  Hassoc := λ x y z w hzw hyz hxy, rfl }

@[reducible] def Preord : category Σ α : Type u, preorder α :=
{ Mor := λ S T, { f : S.1 → T.1 // @monotone S.1 T.1 S.2 T.2 f },
  Comp := λ S T U f g, ⟨f.1 ∘ g.1, @monotone_comp S.1 T.1 U.1 S.2 T.2 U.2 g.1 f.1 g.2 f.2⟩,
  Id := λ S, ⟨id, @monotone_id S.1 S.2⟩,
  Hid_left := λ S T f, subtype.eq rfl,
  Hid_right := λ S T f, subtype.eq rfl,
  Hassoc := λ S T U V f g h, subtype.eq rfl }

@[reducible] def zero : category empty :=
discrete empty

@[reducible] def one : category unit :=
discrete unit

@[reducible] def of_monoid (α : Type u) [monoid α] : category unit :=
{ Mor := λ _ _, α,
  Comp := λ _ _ _, (*),
  Id := λ _, 1,
  Hid_left := λ _ _, one_mul,
  Hid_right := λ _ _, mul_one,
  Hassoc := λ _ _ _ _, mul_assoc }

@[reducible] def to_monoid {α : Type u} (C: category α) (x : α) : monoid (C.Mor x x) :=
{ mul := C.Comp _ _ _,
  mul_assoc := C.Hassoc x x x x,
  one := C.Id x,
  one_mul := C.Hid_left x x,
  mul_one := C.Hid_right x x }

@[reducible] def two : category bool :=
{ Mor := λ x y, plift $ x → y,
  Comp := λ _ _ _ f g, plift.up $ f.down ∘ g.down,
  Id := λ x, plift.up $ @id x,
  Hid_left := λ _ _ ⟨_⟩, rfl,
  Hid_right := λ _ _ ⟨_⟩, rfl,
  Hassoc := λ _ _ _ _ _ _ _, rfl }

namespace par

variable α : Type u

inductive Mor : bool → bool → Type u
| id : ∀ b, Mor b b
| par : α → Mor ff tt

@[reducible] def Comp : Π x y z, Mor α y z → Mor α x y → Mor α x z
| ff ff _  f _ := f
| _  tt tt _ g := g

@[reducible] def Hid_left : ∀ x y f, Comp α x y y (Mor.id α y) f = f
| ff ff (Mor.id α b) := rfl
| ff tt _ := rfl
| tt tt (Mor.id α b) := rfl

@[reducible] def Hid_right : ∀ x y f, Comp α x x y f (Mor.id α x) = f
| ff ff (Mor.id α b) := rfl
| ff tt _ := rfl
| tt tt (Mor.id α b) := rfl

@[reducible] def Hassoc : ∀ x y z w f g h, Comp α x y w (Comp α y z w f g) h = Comp α x z w f (Comp α x y z g h)
| ff ff _  _  _ _ _ := rfl
| ff tt tt tt _ _ _ := rfl
| tt tt tt tt _ _ _ := rfl

end par

@[reducible] def par (α : Type u) : category bool :=
{ Mor := par.Mor α,
  Comp := par.Comp α,
  Id := par.Mor.id α,
  Hid_left := par.Hid_left α,
  Hid_right := par.Hid_right α,
  Hassoc := par.Hassoc α }

@[reducible] def two_mor : category bool :=
par bool

end examples

end category