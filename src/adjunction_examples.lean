import .adjunction .functor_examples

universes u v

namespace category

namespace examples

@[reducible] def Set_.free_forgetful : adjunction.{u+1 u} Set_ Set :=
adjunction.free_forgetful _
  Set_.free
  Set_.forgetful
  (λ S P f, ⟨(plift.up $ unit_eq _ _,
    λ t, option.rec_on t (P.2.2 punit.star) f),
    funext $ λ x, punit.rec_on x rfl⟩)
  (λ S P f x, f.1.2 $ some x)
  (λ P1 P2 S1 S2 f g t z, by dsimp [option.map, option.bind]; refl)
  (λ P1 P2 S1 S2 f g t, subtype.eq $ prod.ext.2 $ ⟨rfl, funext $ λ x,
    by cases x; dsimp [option.map, option.bind]; try {refl}; apply congr_fun f.2⟩)
  (λ S P f, subtype.eq $ prod.ext.2 $ ⟨by dsimp; cases f.1.1; congr,
    funext $ λ t, option.rec_on t
      (by dsimp; from congr_fun f.2 punit.star)
      (λ z, rfl)⟩)
  (λ S P f, rfl)

@[reducible] def Set.Prod_Hom (B : Type u) : adjunction Set Set :=
adjunction.make _ _
  (Set.product_functor B)
  (Set.Hom_functor_right B)
  (λ A C f x, f x.1 x.2)
  (λ A C f x y, f (x, y))
  (λ A₁ A₂ C₁ C₂ f g t, rfl)
  (λ A₁ A₂ C₁ C₂ f g t, rfl)
  (λ A C f, funext $ λ ⟨t₁, t₂⟩, rfl)
  (λ A C f, rfl)

@[reducible] def Top.free_forgetful : adjunction Top Set :=
adjunction.free_forgetful _
  Top.discrete
  Top.forgetful
  (λ S T f, ⟨f, continuous_top⟩)
  (λ S T f, f.1)
  (λ T₁ T₂ S₁ S₂ f g t z, rfl)
  (λ T₁ T₂ S₁ S₂ f g t, subtype.eq rfl)
  (λ S T f, subtype.eq rfl)
  (λ S T f, rfl)

@[reducible] def Top.forgetful_indiscrete : adjunction Set Top :=
adjunction.make _ _
  Top.forgetful
  Top.indiscrete
  (λ S T f, f.1)
  (λ S T f, ⟨f, continuous_bot⟩)
  (λ T₁ T₂ S₁ S₂ f g t, subtype.eq rfl)
  (λ T₁ T₂ S₁ S₂ f g t, rfl)
  (λ S T f, rfl)
  (λ S T f, subtype.eq rfl)

@[reducible] def Grp.free_forgetful : adjunction Grp Set :=
adjunction.free_forgetful _
  Grp.free
  (functor.comp _ _ _ Set_.forgetful Grp.forgetful)
  (λ S G f, ⟨@free_group.to_group _ _ G.2 f, @free_group.to_group.is_group_hom _ _ G.2 f⟩)
  (λ S G f x, f.1 $ free_group.of_type S x)
  (λ G₁ G₂ S₁ S₂ f g t z, rfl)
  (λ G₁ G₂ S₁ S₂ f g t, subtype.eq $ funext $ λ x, eq.symm $
    @free_group.to_group.unique S₂ G₂.1 G₂.2 (f.val ∘ t ∘ g)
      ((Grp.Comp (Grp.free.F S₂) (Grp.free.F S₁) G₂
        (Grp.Comp (Grp.free.F S₁) G₁ G₂ f
           ⟨@free_group.to_group S₁ G₁.1 G₁.2 t, @free_group.to_group.is_group_hom S₁ G₁.1 G₁.2 t⟩)
        (Grp.free.mor S₂ S₁ g)).val)
      (λ x y, by dsimp; rw [free_group.to_group.is_group_hom, free_group.to_group.is_group_hom, f.2])
      (λ x, by dsimp; rw [free_group.to_group.commutes, free_group.to_group.commutes]) _)
  (λ S G f, subtype.eq $ funext $ λ x, eq.symm $ @free_group.to_group.unique _ _ G.2 _ _ f.2 (λ x, rfl) _)
  (λ S G f, funext $ λ x, @free_group.to_group.commutes _ _ G.2 _ _)

@[reducible] noncomputable def Mod.Tensor_Hom (R : Type u) [comm_ring R]
  (N : Type v) [module R N] :
  adjunction (Mod R) (Mod R) :=
adjunction.make _ _
  (Mod.tensor R N)
  (Mod.Hom_functor_right R N)
  (λ M P T, ⟨@tensor_product.universal_property.factor R _ M.1 N P.1 M.2 _ P.2
      (λ x y, (T.1 x).1 y)
      { add_pair := by intros x y z; cases T with T HT; cases HT with HT1 HT2;
          from congr_fun (congr_arg subtype.val (HT1 x y)) z,
        pair_add := by intros x y z; letI := P.2; exact (T.1 x).2.1 y z,
        smul_pair := by intros r x y; cases T with T HT; cases HT with HT1 HT2;
          from congr_fun (congr_arg subtype.val (HT2 r x)) y,
        pair_smul := by intros r x y; letI := P.2; exact (T.1 x).2.2 r y },
    @tensor_product.universal_property.factor_linear R _ M.1 N P.1 M.2 _ P.2 _ _⟩)
  (λ M P T, ⟨λ x, ⟨λ y, T.1 $ @tensor_product.tprod _ _ _ _ M.2 _ x y,
    @is_bilinear_map.pair_linear _ _ _ _ _ M.2 _ P.2 _
      (by letI := M.2; letI := P.2; from is_bilinear_map.comp tensor_product.tprod.is_bilinear_map T.2) x⟩,
    { add := λ x y, subtype.eq $ funext $ λ z, by letI := M.2; letI := P.2;
        rcases T with ⟨T, HT1, HT2⟩; change T ((x + y) ⊗ₛ z) = T (x ⊗ₛ z) + T (y ⊗ₛ z);
        rw [tensor_product.add_tprod, HT1],
      smul := λ r x, subtype.eq $ funext $ λ y, by letI := M.2; letI := P.2;
        rcases T with ⟨T, HT1, HT2⟩; change T ((r • x) ⊗ₛ y) = r • T (x ⊗ₛ y);
        rw [tensor_product.smul_tprod, HT2] }⟩)
  (λ P₁ P₂ M₁ M₂ PT MT F, subtype.eq $ funext $ λ x, subtype.eq $
    funext $ λ y, by dsimp; rw [tensor_product.tprod_map.commutes]; refl)
  (λ P₁ P₂ M₁ M₂ PT MT F, subtype.eq $ eq.symm $ by letI := M₁.2; letI := M₂.2;
    letI := P₁.2; letI := P₂.2; letI := ((Mod.tensor R N).F M₁).2;
    from tensor_product.universal_property.factor_unique _ _
      (is_linear_map.comp (is_linear_map.comp PT.2 (tensor_product.universal_property.factor_linear _))
        (tensor_product.tprod_map.linear _ _))
      (λ x y, by dsimp; rw tensor_product.tprod_map.commutes;
        rw tensor_product.universal_property.factor_commutes; refl))
  (λ M P f, subtype.eq $ eq.symm $ by letI := M.2; letI := P.2;
    from tensor_product.universal_property.factor_unique _ _ f.2 (λ x y, rfl))
  (λ M P f, subtype.eq $ funext $ λ x, subtype.eq $ funext $ λ y,
    by dsimp; rw [tensor_product.universal_property.factor_commutes])

@[reducible] def GSet.free_forgetful (G : Type u) [group G] : adjunction (GSet G) Set.{u} :=
adjunction.free_forgetful _
  (GSet.product G)
  (GSet.forgetful G)
  (λ S X f, ⟨λ gs, by letI := X.2; from gs.1 ● f gs.2, λ g ⟨h, s⟩, by simp [act_act]; refl⟩)
  (λ S X f s, f.1 (1, s))
  (λ X₁ X₂ S₁ S₂ f g t z, rfl)
  (λ X₁ X₂ S₁ S₂ f g t, by simp; funext; simp; rw f.2)
  (λ S X f, subtype.eq $ by simp; funext; rw ← f.2; cases gs with g s;
    change f.1 (g * 1, s) = f.1 (g, s); congr; simp)
  (λ S X f, by simp)

@[reducible] def GSet.forgetful_func (G : Type u) [group G] : adjunction Set.{u} (GSet G) :=
adjunction.make _ _
  (GSet.forgetful G)
  (@GSet.func G _ G (group_action.examples.mul_left G))
  (λ X S f s, f.1 s 1)
  (λ X S f, ⟨λ s g, by letI := X.2; from f (g⁻¹ ● s),
    λ g x, by simp; funext h; dsimp [group_action.examples.func];
      simp [act_act]; congr; change h⁻¹ * g = (g⁻¹ * h)⁻¹; simp⟩)
  (λ S₁ S₂ X₁ X₂ f g t, by simp; funext s h; simp; rw g.2)
  (λ S₁ S₂ X₁ X₂ f g t, by simp)
  (λ X S f, by simp)
  (λ X S f, subtype.eq $ by dsimp; funext x g; rw f.2 (g⁻¹) x;
    dsimp [group_action.examples.func]; congr; rw inv_inv; apply mul_one)

end examples

end category