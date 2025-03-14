Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Subcategory.FullEquivalences.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Properties.AdjunctionsRepresentable.
Require Import UniMath.Bicategories.Morphisms.Properties.ContainsAdjEquiv.
Require Import Inverters.
Require Import InverterEquivalences.

Local Open Scope cat.

(**

  Suppose, we have a diagram as follows


                        ---- f₁ ---->
     p₁ ---- i₁ ----> x₁     V        y₁
                        ---- g₁ ---->
     |                |               |
     |                |               |
     lp      ≃        lx     ≃        ly
     |                |               |
     |                |               |
     V                V               V
                        ---- f₂ ---->
     p₂ ---- i₂ ----> x₂     V        y₂
                        ---- g₂ ---->
    |  |             |  |
    |  |             |  |
   fp=>gp    ≃      fx=>gx
    |  |             |  |
    |  |             |  |
    V  V             V  V
     p₃ ---- i₃ ----> x₃

  where the rows and columns are inverter cones, i₂ is pseudomonic and ly is
  conservative. If the rightmost column and the top row are inverters, then so
  is the leftmost column.

*)
Section StackedInverter.
  Context {B : bicat}
          {p₁ x₁ y₁ p₂ x₂ y₂ p₃ x₃ : B}
          {i₁ : p₁ --> x₁}
          {f₁ g₁ : x₁ --> y₁}
          {α₁ : f₁ ==> g₁}
          {inv_i₁α₁ : is_invertible_2cell (i₁ ◃ α₁)}
          (cone₁ :=  make_inverter_cone p₁ i₁ inv_i₁α₁)
          {i₂ : p₂ --> x₂}
          {f₂ g₂ : x₂ --> y₂}
          {α₂ : f₂ ==> g₂}
          (inv_i₂α₂ : is_invertible_2cell (i₂ ◃ α₂))
          (cone₂ :=  make_inverter_cone p₂ i₂ inv_i₂α₂)
          (lx : x₁ --> x₂)
          (ly : y₁ --> y₂)
          (lp : p₁ --> p₂)
          {fp gp : p₂ --> p₃}
          {αp : fp ==> gp}
          {inv_lpαp : is_invertible_2cell (lp ◃ αp)}
          (conep := make_inverter_cone p₁ lp inv_lpαp)
          {fx gx : x₂ --> x₃}
          {αx : fx ==> gx}
          {inv_lxαx : is_invertible_2cell (lx ◃ αx)}
          (conex := make_inverter_cone x₁ lx inv_lxαx)
          (i₃ : p₃ --> x₃)
          (Hi₂ : pseudomonic_1cell i₂)
          (Hly : conservative_1cell ly)
          (γ₁ : invertible_2cell (lp · i₂) (i₁ · lx))
          (γ₂ : invertible_2cell (lx · f₂) (f₁ · ly))
          (γ₃ : invertible_2cell (lx · g₂) (g₁ · ly))
          (γ₄ : invertible_2cell (i₂ · fx) (fp · i₃))
          (γ₅ : invertible_2cell (i₂ · gx) (gp · i₃))
          (H₁ : has_inverter_ump cone₁)
          (Hx : has_inverter_ump conex)
          (pα : (lx ◃ α₂) • γ₃ = γ₂ • (α₁ ▹ ly))
          (pα': (i₂ ◃ αx) • γ₅ = γ₄ • (αp ▹ i₃)).

 (* Let inverter_functor_stacked (q : B)
    : functor
        (@universal_inverter_cat B _ _ _ _ α₁ q)
        (hom q p₂)
    := functor_composite (universal_inverter_cat_morphism lx ly γ₂ γ₃ pα q)
         (adj_equivalence_inv (make_is_universal_inverter_cone _ H₂ q)).

  Let img_inclusion (q : B)
    : ∏ x : hom q p₂,
      sub_img_functor (inverter_functor_stacked q) x
      → (λ h : hom q p₂,
         make_hProp _ (isaprop_is_invertible_2cell (h ◃ αp)))
         (functor_identity (hom q p₂) x).
  Proof.
    intros h h_in_img; cbn - [universal_inverter_cat] in h_in_img |- *.
    use (squash_to_prop h_in_img).
    { apply isaprop_is_invertible_2cell. }
    apply uncurry.
    intros h' β.
    apply z_iso_to_inv2cell in β.
    use eq_is_invertible_2cell.
    { exact ((β^-1 ▹ fp) • (_ ◃ αp) • (β ▹ gp)). }
    { abstract (
    rewrite vcomp_whisker, vassocl, rwhisker_vcomp, vcomp_linv, id2_rwhisker;
    apply id2_right). }
    set (lwαp := _ ◃ αp).
    is_iso; try (apply property_from_invertible_2cell).
    apply Hi₃.
    cbn - [universal_inverter_cat] in lwap.
    subst lwαp.
    use eq_is_invertible_2cell.
    * exact (rassociator _ _ _ • ((_ ◃ γ₄^-1) • lassociator _ _ _ • ((_ · i₂) ◃ αx) • rassociator _ _ _ • (_ ◃ γ₅)) • lassociator _ _ _).
    * refine (!_).
    apply rassociator_to_lassociator_post.
    rewrite <- rwhisker_lwhisker_rassociator.
    apply maponpaths.
    refine (!_).
    rewrite ! vassocl.
    use vcomp_move_R_pM; is_iso.
    rewrite vassocr, <- lwhisker_lwhisker.
    rewrite vassocl, vassoc4.
    rewrite lassociator_rassociator, id2_right.
    simpl; rewrite 2 ! lwhisker_vcomp.
    apply maponpaths, pα'.
    * set (hi₂_αx := _ · i₂ ◃ αx).
    is_iso; try (apply property_from_invertible_2cell).
    subst hi₂_αx.
    use eq_is_invertible_2cell.
    { exact (((inverter_ump_mor_pr1 H₂ _ _) ▹ fx) • (rassociator _ _ _ • ((_ ◃ (lx ◃ αx)) • lassociator _ _ _)) • ((inverter_ump_mor_pr1 H₂ _ _)^-1 ▹ gx)). }
    { rewrite lwhisker_lwhisker, vassoc4.
    rewrite rassociator_lassociator, id2_right.
    rewrite vcomp_whisker, vassocl, rwhisker_vcomp, vcomp_rinv, id2_rwhisker.
    apply id2_right. }
    set (lxαx := lx ◃ αx).
    is_iso; apply property_from_invertible_2cell.
  Qed.

  Definition universal_inverter_cat_stacked (q : B)
    : functor
        (@universal_inverter_cat B _ _ _ _ α₁ q)
        (@universal_inverter_cat B _ _ _ _ αp q).
  Proof.
    refine (functor_composite (functor_full_img (inverter_functor_stacked q)) _).
    (*- exact (hom q p₂).
    - exact (functor_composite (universal_inverter_cat_morphism lx ly γ₂ γ₃ pα q) (adj_equivalence_inv (make_is_universal_inverter_cone _ H₂ q))).*)
    use full_sub_category_functor.
      + apply functor_identity.
      + apply img_inclusion.
  Defined.

  Let inverter_cone_γ₁ (q : B)
    : nat_z_iso
        (functor_composite (inverter_cone_functor cone₁ q)
           (universal_inverter_cat_morphism lx ly γ₂ γ₃ pα q))
        (functor_composite
           (functor_composite (inverter_cone_functor conep q) (sub_precategory_inclusion _ _))
           (inverter_cone_functor cone₂ q)).
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro h.
        apply morphism_in_full_subcat.
        cbn.
        exact (rassociator _ _ _ • ((h ◃ γ₁^-1) • lassociator _ _ _)).
      + abstract (
          intros h₁ h₂ α;
          apply eq_in_sub_precategory;
          cbn;
          rewrite vassocr, rwhisker_rwhisker_alt;
          rewrite vassocl, vassoc4;
          rewrite vcomp_whisker;
          rewrite <- vassoc4, <- rwhisker_rwhisker;
          apply vassoc4).
    - intro h.
      apply is_iso_full_sub.
      cbn.
      apply is_inv2cell_to_is_z_iso.
      is_iso.
  Defined.

  Let inv_unit_nat_z_iso₂ (q : B)
    : nat_z_iso
        (inverter_cone_functor conep q ∙ sub_precategory_inclusion _ _
         ∙ inverter_cone_functor cone₂ q ∙ adj_equivalence_inv (make_is_universal_inverter_cone cone₂ H₂ q))
        (inverter_cone_functor conep q ∙ sub_precategory_inclusion _ _).
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro h.
        exact (pre_whisker_nat_z_iso
                 (inverter_cone_functor conep q ∙ sub_precategory_inclusion _ _)
                 (nat_z_iso_inv (unit_nat_z_iso_from_adj_equivalence_of_cats (make_is_universal_inverter_cone _ H₂ q)))
               h).
      + intros h₁ h₂ α.
        apply nat_trans_ax.
    - intro h; cbn -[pre_whisker_nat_z_iso].
      exact (pr2_nat_z_iso
               (pre_whisker_nat_z_iso
                  (inverter_cone_functor conep q ∙ sub_precategory_inclusion _ _)
                  (nat_z_iso_inv (unit_nat_z_iso_from_adj_equivalence_of_cats (make_is_universal_inverter_cone _ H₂ q))))
             h).
  Defined.

  Let unit_nat_z_iso₂ (q : B)
    : nat_z_iso
        (inverter_cone_functor cone₁ q ∙ inverter_functor_stacked q)
        (inverter_cone_functor cone₁ q ∙ inverter_functor_stacked q
         ∙ inverter_cone_functor cone₂ q ∙ adj_equivalence_inv (make_is_universal_inverter_cone cone₂ H₂ q)).
  Proof.
    refine (nat_z_iso_comp _
             (pre_whisker_nat_z_iso
                (inverter_cone_functor cone₁ q ∙ inverter_functor_stacked q)
                (unit_nat_z_iso_from_adj_equivalence_of_cats (make_is_universal_inverter_cone cone₂ H₂ q)))).
    use make_nat_z_iso.
    - apply nat_trans_functor_id_right_inv.
    - intro h; cbn.
      apply is_invertible_2cell_id₂.
(*use make_nat_trans.
      + intro h.
        exact (pre_whisker
                 (inverter_cone_functor cone₁ q ∙ inverter_functor_stacked q)
                 (unit_nat_z_iso_from_adj_equivalence_of_cats (make_is_universal_inverter_cone cone₂ H₂ q))
               h).
      + abstract (intros h₁ h₂ α; apply nat_trans_ax).
    - intro h; cbn - [functor_composite].
      apply is_inv2cell_to_is_z_iso.
      exact (is_invertible_2cell_inv (inverter_ump_is_invertible_2cell H₂ _ _)).*)
  Defined.

  Definition counit_nat_z_iso₂ (q : B)
    : nat_z_iso
        (inverter_cone_functor cone₁ q ∙ inverter_functor_stacked q
         ∙ inverter_cone_functor cone₂ q)
        (inverter_cone_functor cone₁ q
         ∙ universal_inverter_cat_morphism lx ly γ₂ γ₃ pα q).
  Proof.
    refine (nat_z_iso_comp (nat_z_iso_comp _ (pre_whisker_nat_z_iso (inverter_cone_functor cone₁ q
    ∙ universal_inverter_cat_morphism lx ly γ₂ γ₃ pα q) (counit_nat_z_iso_from_adj_equivalence_of_cats (make_is_universal_inverter_cone _ H₂ q)))) _).
    - use make_nat_z_iso.
      + use make_nat_trans.
        * intro h; apply morphism_in_full_subcat.
          cbn; exact (id2 _).
        * intros h₁ h₂ α.
          apply eq_in_sub_precategory.
          cbn.
          exact (id2_right _ @ !id2_left _).
      + intro h; cbn.
        exact (iso_in_precat_is_iso_in_subcat _ _ _ _ (inv2cell_to_z_iso (id2_invertible_2cell _))).
    - use make_nat_z_iso.
      + use make_nat_trans.
        * intro h; apply morphism_in_full_subcat.
          cbn; exact (id2 _).
        * intros h₁ h₂ α.
          apply eq_in_sub_precategory.
          cbn.
          exact (id2_right _ @ !id2_left _).
      + intro h; cbn.
        exact (iso_in_precat_is_iso_in_subcat _ _ _ _ (inv2cell_to_z_iso (id2_invertible_2cell _))).
  Defined.


  Definition inverter_cone_functor_stacked (q : B)
    : nat_z_iso
        (inverter_cone_functor cone₁ q ∙ inverter_functor_stacked q)
        (functor_composite (inverter_cone_functor conep q) (sub_precategory_inclusion _ _)).
  Proof.
    refine (nat_z_iso_comp (nat_z_iso_comp (unit_nat_z_iso₂ q) (post_whisker_nat_z_iso _ (adj_equivalence_inv (make_is_universal_inverter_cone cone₂ H₂ q)))) (inv_unit_nat_z_iso₂ q)).
    exact (nat_z_iso_comp (counit_nat_z_iso₂ q) (inverter_cone_γ₁ q)).
    (*Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
    apply invertible_2cell_to_nat_z_iso.
    refine (comp_of_invertible_2cell
      (comp_of_invertible_2cell
      (comp_of_invertible_2cell _
      (rassociator_invertible_2cell _ _ _))
      (lwhisker_of_invertible_2cell _ (nat_z_iso_to_invertible_2cell _ _ (nat_z_iso_inv (unit_nat_z_iso_from_adj_equivalence_of_cats (make_is_universal_inverter_cone _ H₂ q))))))
      (runitor_invertible_2cell _)).
    refine (comp_of_invertible_2cell
              (comp_of_invertible_2cell
                 (comp_of_invertible_2cell
                    (rinvunitor_invertible_2cell _)
                    (lwhisker_of_invertible_2cell _ (nat_z_iso_to_invertible_2cell _ _ (unit_nat_z_iso_from_adj_equivalence_of_cats (make_is_universal_inverter_cone _ H₂ q)))))
                 (lassociator_invertible_2cell _ _ _))
              (rwhisker_of_invertible_2cell _ _)).
    refine (comp_of_invertible_2cell
            (comp_of_invertible_2cell
            (rassociator_invertible_2cell _ _ _)
            (lwhisker_of_invertible_2cell _ _))
            (nat_z_iso_to_invertible_2cell _ _ (inverter_cone_γ₁ q))).
    refine (comp_of_invertible_2cell
            (comp_of_invertible_2cell
            (rassociator_invertible_2cell _ _ _)
            (lwhisker_of_invertible_2cell _ (nat_z_iso_to_invertible_2cell _ _ (counit_nat_z_iso_from_adj_equivalence_of_cats (make_is_universal_inverter_cone _ H₂ q)))))
            (runitor_invertible_2cell _)).*)
  Defined.

  Definition is_universal_inverter_cone_stacked
    : is_universal_inverter_cone cone₁.
  Proof.
    intro q.
    use make_adj_equivalence_of_cats.
    - exact (functor_composite (universal_inverter_cat_stacked q) (adj_equivalence_inv (make_is_universal_inverter_cone _ Hp q))).
    - refine (nat_trans_comp _ _ _ (nat_trans_comp _ _ _ (unit_nat_z_iso_from_adj_equivalence_of_cats (make_is_universal_inverter_cone conep Hp q)) (post_whisker _ _)) (nat_trans_functor_assoc _ _ _)).
      use make_nat_trans.
      + intro h.
        apply morphism_in_full_subcat.
        exact (nat_z_iso_to_trans_inv (inverter_cone_functor_stacked q) h).
      + intros h₁ h₂ α.
        apply eq_in_sub_precategory.
        exact (nat_trans_ax (nat_z_iso_to_trans_inv (inverter_cone_functor_stacked q)) h₁ h₂ α).
- use make_nat_trans.
  + intro h.
    apply morphism_in_full_subcat.
    use (pseudomonic_1cell_inv_map Hlx).
    * refine (pr1 (inverter_cone_functor_γ₁ q ((universal_inverter_cat_stacked q
∙ adj_equivalence_inv (make_is_universal_inverter_cone conep Hp q)) h)) • _).
      refine ((inverter_ump_mor_pr1 Hp _ _ ▹ i₂) • _).
      exact (inverter_ump_mor_pr1 H₂ _ _).
    * is_iso; apply property_from_invertible_2cell.
  + admit.
- split; intro h.
+ apply eq_in_sub_precategory.
  cbn.
rewrite ! id2_left, ! id2_right.
- split; intro h.
+ cbn -[is_z_isomorphism].

  Definition has_inverter_ump_stacked
    : has_inverter_ump cone₁
    := universal_inverter_cone_has_ump _ is_universal_inverter_cone_stacked.*)

  Definition has_inverter_ump_1_stacked
    : has_inverter_ump_1 conep.
  Proof.
    intro q.
    set (q' := (universal_inverter_cat_morphism i₂ i₃ γ₄ γ₅ pα' q)
                 (inverter_cone_pr1 q ,, inverter_cone_is_invertible_cell q)).
    use make_inverter_1cell.
    - use (inverter_ump_mor H₁).
      + exact (inverter_ump_mor Hx (pr1 q') (pr2 q')).
      + apply (conservative_1cell_reflect_iso Hly).
        use eq_is_invertible_2cell.
        { exact (rassociator _ _ _ • ((_ ◃ γ₂^-1) • lassociator _ _ _ • (_ · lx ◃ α₂) • rassociator _ _ _ • (_ ◃ γ₃)) • lassociator _ _ _). }
        { abstract (
            refine (!_);
            apply rassociator_to_lassociator_post;
            rewrite <- rwhisker_lwhisker_rassociator;
            apply maponpaths;
            refine (!_);
            rewrite ! vassocl;
            use vcomp_move_R_pM; is_iso;
            rewrite vassocr, <- lwhisker_lwhisker;
            rewrite vassocl, vassoc4;
            rewrite lassociator_rassociator, id2_right;
            simpl; rewrite 2 ! lwhisker_vcomp;
            apply maponpaths, pα). }
        set (α₂' := _ ◃ α₂); is_iso; try (apply property_from_invertible_2cell); subst α₂'.
        use eq_is_invertible_2cell.
        { exact (((inverter_ump_mor_pr1 Hx _ _) ▹ f₂) • (rassociator _ _ _ • ((_ ◃ (_ ◃ α₂)) • lassociator _ _ _)) • ((inverter_ump_mor_pr1 Hx _ _)^-1 ▹ g₂)). }
        { abstract (
            rewrite lwhisker_lwhisker, vassoc4;
            rewrite rassociator_lassociator, id2_right;
            rewrite vcomp_whisker, vassocl, rwhisker_vcomp, vcomp_rinv, id2_rwhisker;
            apply id2_right). }
        set (α₂' := _ ◃ α₂); is_iso; subst α₂'.
        apply property_from_invertible_2cell.
    - use (make_invertible_2cell (is_invertible_2cell_pseudomonic_1cell_inv_map Hi₂ _ _)).
      + exact (rassociator _ _ _ • (_ ◃ γ₁) • lassociator _ _ _ • (inverter_ump_mor_pr1 H₁ _ _ ▹ lx) • inverter_ump_mor_pr1 Hx _ _).
      + is_iso; apply property_from_invertible_2cell.
  Defined.

  Definition has_inverter_ump_2_stacked
    : has_inverter_ump_2 conep.
  Proof.
    intros q u₁ u₂ β.
    use tpair.
    - apply (inverter_ump_cell H₁), (inverter_ump_cell Hx).
      exact (rassociator _ _ _ • (u₁ ◃ γ₁^-1) • lassociator _ _ _ • (β ▹ i₂)
             • rassociator _ _ _ • (u₂ ◃ γ₁) • lassociator _ _ _).
    - apply (pseudomonic_1cell_eq Hi₂).
      apply (vcomp_lcancel _ (is_invertible_2cell_lassociator _ _ _)).
      rewrite rwhisker_rwhisker.
      use (vcomp_lcancel (u₁ ◃ γ₁^-1)).
      { is_iso. }
      rewrite 2 ! vassocr, <- vcomp_whisker.
      apply (vcomp_lcancel _ (is_invertible_2cell_rassociator _ _ _)).
      rewrite ! vassocr, <- rwhisker_rwhisker_alt.
      rewrite (inverter_ump_cell_pr1 H₁), (inverter_ump_cell_pr1 Hx).
      refine (!_).
      apply rassociator_to_lassociator_post.
      use vcomp_move_L_Mp.
      { is_iso. }
      refine (!_).
      rewrite vassocl, lassociator_rassociator.
      apply id2_right.
  Defined.

  Definition has_inverter_ump_eq_stacked
    : has_inverter_ump_eq conep.
  Proof.
    intros b u₁ u₂ β φ₁ φ₂ q₁ q₂.
    apply (inverter_ump_eq_alt H₁), (inverter_ump_eq_alt Hx).
    apply (vcomp_rcancel _ (is_invertible_2cell_rassociator _ _ _)).
    rewrite 2 ! rwhisker_rwhisker_alt.
    apply maponpaths.
    use (vcomp_rcancel (u₂ ◃ γ₁^-1)).
    { is_iso. }
    rewrite 2 ! vcomp_whisker.
    apply maponpaths.
    apply (vcomp_rcancel _ (is_invertible_2cell_lassociator _ _ _)).
    rewrite <- 2 ! rwhisker_rwhisker.
    do 2 apply maponpaths.
    exact (q₁ @ !q₂).
  Qed.

  Definition has_inverter_ump_stacked
    : has_inverter_ump conep.
  Proof.
    repeat split.
    - exact has_inverter_ump_1_stacked.
    - exact has_inverter_ump_2_stacked.
    - exact has_inverter_ump_eq_stacked.
  Defined.
End StackedInverter.
