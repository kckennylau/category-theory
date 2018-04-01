import .adjunction .more_examples

namespace category

namespace adjunction

namespace examples

@[reducible] def Set_Set : adjunction examples.Set_ examples.Set :=
{ left := examples.Set_.free,
  right := examples.Set_.forgetful,
  Hom_iso :=
  { to_mor :=
    { mor := λ x f, ⟨(plift.up $ by cases x.2.1; refl,
        λ t, option.rec_on t (x.2.2.2 punit.star) f),
        funext $ λ t, punit.rec_on t rfl⟩,
      Hcomp := λ x y f, begin
        funext,
        apply subtype.eq,
        apply prod.ext.2,
        split,
        { refl },
        { funext,
          cases t,
          { dsimp [option.map, option.bind] at *,
            rw [congr_fun f.2.2] },
          { refl } }
      end },
    inv_mor :=
    { mor := λ x f t, f.1.2 $ some t,
      Hcomp := λ x y f, by funext; dsimp [option.map, option.bind]; refl },
    split_monomorphism := by dsimp [natural_transformation.comp] at *; congr,
    split_epimorphism := begin
        dsimp [natural_transformation.comp] at *,
        congr,
        funext x f,
        apply subtype.eq,
        apply prod.ext.2,
        split,
        { cases f with f1 f2,
          cases f1 with f3 f4,
          cases f3,
          refl },
        { funext t,
          cases t,
          { apply congr_fun f.2 },
          { refl } }
      end } }

end examples

end adjunction

end category