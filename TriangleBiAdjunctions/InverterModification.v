(* ******************************************************************************* *)
(** * Inverter of modifications
    Gabriel Merlin
    January 2025
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

(*From UniMath Require Import Bicategories.All.*)
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require UniMath.Bicategories.DisplayedBicats.Examples.DisplayedInserter.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import Bicategories.PseudoFunctors.PseudoFunctor.Notations.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.

Require Import Inverters.
Require Import InverterEquivalences.
Require Import MorePseudoTransformations.
Require Import PrePostCompositionByPseudoFunctor.

Local Open Scope cat.


Section InverterOfModification.
  Context {B₁ B₂ : bicat}
          {F₁ F₂ : psfunctor B₁ B₂}
          {ρ σ : pstrans F₁ F₂}
          (m : modification ρ σ).

  Section ConePseudoComponents.
    Context (cone : @inverter_cone _ _ _ _ _ m).

    Definition modification_inverter_cone_ob
      : psfunctor B₁ B₂
      := inverter_cone_ob cone.

    Definition modification_inverter_cone_pr1
      : pstrans modification_inverter_cone_ob F₁
      := inverter_cone_pr1 cone.

    Definition modification_inverter_cone_is_invertible_cell
      : is_invertible_modification (modification_inverter_cone_pr1 ◃ m)
      := inverter_cone_is_invertible_cell cone.

    Definition modification_inverter_cone_component_of
      : ∏ b : B₁, @inverter_cone _ _ _ _ _ (modcomponent_of m b)
      := λ b : B₁, make_inverter_cone (modification_inverter_cone_ob b)
                     (modification_inverter_cone_pr1 b)
                     (is_invertible_modcomponent_of _
                        modification_inverter_cone_is_invertible_cell b).
  End ConePseudoComponents.


  Section CellPseudoComponents.
    Context {cone₁ cone₂ : @inverter_cone _ _ _ _ _ m}
            (u : inverter_1cell cone₁ cone₂).

    Definition modification_inverter_1cell_mor
      : pstrans (modification_inverter_cone_ob cone₁)
          (modification_inverter_cone_ob cone₂)
      := inverter_1cell_mor u.

    Definition modification_inverter_1cell_pr1
      : invertible_modification
          (u · inverter_cone_pr1 cone₂)
          (inverter_cone_pr1 cone₁)
      := inverter_1cell_pr1 u.

    Definition modification_inverter_1cell_cell
      := modcomponent_eq (inverter_1cell_cell u).

    Definition modification_inverter_1cell_component_of
      : ∏ b : B₁,
        inverter_1cell (modification_inverter_cone_component_of cone₁ b)
          (modification_inverter_cone_component_of cone₂ b).
    Proof.
      intro b.
      use make_inverter_1cell.
      - exact (pscomponent_of modification_inverter_1cell_mor b).
      - exact (invertible_modcomponent_of modification_inverter_1cell_pr1 b).
    Defined.
  End CellPseudoComponents.


  Section UniversalMappingPropertyFromData.
    Context (cone : @inverter_cone _ _ _ _ _ m)
            (p : ∏ (b : B₁),
                 has_inverter_ump (modification_inverter_cone_component_of cone b)).

    Definition modification_inverter_cone_ump_1_from_data_mor_data_pscomponent
               (other_cone : @inverter_cone _ F₁ F₂ ρ σ m)
               (X : B₁)
      : modification_inverter_cone_ob other_cone X -->
        modification_inverter_cone_ob cone X
      := inverter_ump_mor (p X)
           (pscomponent_of (inverter_cone_pr1 other_cone) X)
           (is_invertible_modcomponent_of (inverter_cone_pr1 other_cone ◃ m)
             (inverter_cone_is_invertible_cell other_cone) X).

    Definition modification_inverter_cone_ump_1_from_data_mor_data_psnaturality
               (other_cone : @inverter_cone _ F₁ F₂ ρ σ m)
               (X Y : B₁)
               (f : B₁ ⟦ X, Y ⟧)
      : invertible_2cell
          (modification_inverter_cone_ump_1_from_data_mor_data_pscomponent other_cone X
           · # (modification_inverter_cone_ob cone) f)
          (# (modification_inverter_cone_ob other_cone) f
           · modification_inverter_cone_ump_1_from_data_mor_data_pscomponent other_cone Y).
    Proof.
      use (inverter_ump_invertible_2cell (p Y)).
      use make_invertible_2cell.
      + use (vcomp2 (rassociator _ _ _)).
        use (vcomp2 (lwhisker _ ((psnaturality_of (inverter_cone_pr1 cone) f)^-1))).
        use (vcomp2 (lassociator _ _ _)).
        use (vcomp2 (rwhisker (# F₁ f) (inverter_1cell_pr1 (inverter_ump_mor (p X) _ _)))).
        use (vcomp2 (psnaturality_of (inverter_cone_pr1 other_cone) f)).
        use (vcomp2 (lwhisker _
                      ((inverter_1cell_pr1
                          (inverter_ump_mor (p Y)
                            (pscomponent_of (inverter_cone_pr1 other_cone) Y)
                            (invertible_modcomponent_of
                              (make_invertible_2cell
                                (inverter_cone_is_invertible_cell other_cone))
                              Y)))^-1))).
        apply lassociator.
      + is_iso; apply property_from_invertible_2cell.
    Defined.

    Definition modification_inverter_cone_ump_1_from_data_mor_data
               (other_cone : @inverter_cone _ F₁ F₂ ρ σ m)
      : pstrans_data (inverter_cone_ob other_cone) (inverter_cone_ob cone)
      := make_pstrans_data
           (modification_inverter_cone_ump_1_from_data_mor_data_pscomponent other_cone)
           (modification_inverter_cone_ump_1_from_data_mor_data_psnaturality other_cone).

    Definition modification_inverter_cone_ump_1_from_data_mor_is_pstrans
               (other_cone : @inverter_cone _ F₁ F₂ ρ σ m)
      : is_pstrans (modification_inverter_cone_ump_1_from_data_mor_data other_cone).
    Proof.
      repeat split.
      - intros X Y f g α.
        use (inverter_ump_eq_alt (p Y)).
        rewrite <- 2 ! rwhisker_vcomp.
        simpl.

        rewrite 2 ! inverter_ump_cell_pr1 with (H := p Y).
        rewrite vassocr.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite vassocl, vassoc4.
        rewrite lwhisker_vcomp.
        rewrite <- psnaturality_inv_natural with (η := inverter_cone_pr1 cone).
        rewrite <- lwhisker_vcomp.
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite lwhisker_lwhisker.
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite <- vcomp_whisker.
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite psnaturality_natural with (η := inverter_cone_pr1 other_cone).
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite vcomp_whisker.
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite <- rwhisker_rwhisker.
        rewrite ! vassocr.
        reflexivity.
      - intro X.
        use (inverter_ump_eq_alt (p X)).
        rewrite <- rwhisker_vcomp.
        simpl;
        rewrite inverter_ump_cell_pr1 with (H := p X).
        rewrite vassocr.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite vassocl, vassoc4.
        rewrite lwhisker_vcomp.
        rewrite pstrans_id_inv_alt with (τ := inverter_cone_pr1 cone).
        rewrite <- lwhisker_vcomp.
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite lwhisker_lwhisker.
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite <- vcomp_whisker.
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite pstrans_id with (η := inverter_cone_pr1 other_cone).
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite vcomp_whisker.
        rewrite <- vassoc4.
        rewrite <- rwhisker_rwhisker.
        rewrite <- vassoc4, vassocl, vassoc4.
        rewrite vcomp_runitor.
        rewrite <- vassoc4.
        rewrite <- lwhisker_vcomp.
        rewrite <- vassoc4.
        rewrite rinvunitor_triangle.
        rewrite vassocr, <- vassoc4.
        rewrite rinvunitor_runitor, id2_right.
        rewrite lunitor_lwhisker.
        rewrite vassoc4.
        rewrite linvunitor_natural, hcomp_identity_left.
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite lwhisker_vcomp.
        rewrite vcomp_rinv, lwhisker_id2, id2_right.
        rewrite linvunitor_assoc.
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite rassociator_lassociator, id2_right.
        rewrite 2 ! rwhisker_vcomp.
        reflexivity.
      - intros X Y Z f g.
        use (inverter_ump_eq_alt (p Z)).
        rewrite <- rwhisker_vcomp.
        simpl (rwhisker _ _) at 2;
        rewrite inverter_ump_cell_pr1 with (H := p Z).

        rewrite vassocr.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite vassocl, vassoc4.
        rewrite lwhisker_vcomp.
        rewrite vassocl.
        rewrite pstrans_inv_comp_alt.
        rewrite 6 ! vassocr with (x := psfunctor_comp (inverter_cone_ob cone) f g ▹ _).
        rewrite rwhisker_vcomp, vcomp_rinv, id2_rwhisker, id2_left.

        rewrite <- lwhisker_vcomp.
        rewrite vassocl, vassocr, vassoc4.
        rewrite lwhisker_lwhisker.
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite <- vcomp_whisker.
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite pstrans_comp with (η := inverter_cone_pr1 other_cone).
        rewrite vassocr.
        symmetry; apply rassociator_to_lassociator_post.

        rewrite <- rwhisker_vcomp.
        rewrite vassocl.
        rewrite rwhisker_rwhisker_alt.
        rewrite vassocr.

        symmetry.
        rewrite vassocr, vassocl.
        rewrite vcomp_whisker.
        rewrite vassocr.
        apply maponpaths with (f := λ x, vcomp2 x _).
        rewrite vassocr, vassocl.
        rewrite <- lwhisker_lwhisker.
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite lwhisker_vcomp.
        rewrite 2 ! vassocr.
        symmetry; apply rassociator_to_lassociator_post.

        rewrite vassocl.
        rewrite inverse_pentagon, hcomp_identity_left, hcomp_identity_right.
        rewrite vassocr, rwhisker_vcomp.
        rewrite vassocl.
        rewrite lassociator_rassociator, id2_right.
        rewrite <- rwhisker_vcomp.
        rewrite vassocl, vassoc4.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite <- vassoc4.
        rewrite lwhisker_vcomp.
        simpl (rwhisker _ _) at 3;
        rewrite inverter_ump_cell_pr1 with (H := p Z).
        rewrite ! vassocl with (z := rassociator (# (modification_inverter_cone_ob other_cone) g) _ _).
        rewrite lassociator_rassociator, id2_right.

        rewrite <- rwhisker_vcomp.
        rewrite vassocl, vassoc4, vassocl.
        rewrite <- lwhisker_vcomp.
        rewrite vassoc4.
        rewrite rassociator_rassociator.
        rewrite vassocr, vassocl.
        rewrite <- lwhisker_vcomp.
        rewrite vassoc4.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite <- vassoc4, vassocl.
        rewrite <- rwhisker_vcomp.
        rewrite vassocl, vassoc4.
        rewrite rwhisker_rwhisker_alt.
        rewrite <- vassoc4, vassocr, vassoc4.
        rewrite vcomp_whisker.
        rewrite <- lwhisker_vcomp, vassoc4.
        rewrite <- lwhisker_vcomp, vassocr.
        apply maponpaths with (f := λ x, vcomp2 x _).
        symmetry; apply lassociator_to_rassociator_post.

        rewrite 2 ! vassocl, vassoc4.
        rewrite <- rwhisker_rwhisker.
        rewrite <- vassoc4.
        rewrite rwhisker_vcomp.
        rewrite vassocl, vassoc4.
        rewrite <- lassociator_lassociator.
        rewrite vassocr, vassocl.
        rewrite rwhisker_vcomp.
        rewrite vassocr, 3 ! vassocl, vassoc4.
        rewrite lwhisker_vcomp.
        rewrite vassocl with (z := lassociator _ _ _).
        rewrite rassociator_lassociator, id2_right.
        rewrite <- lwhisker_vcomp.
        rewrite 2 ! vassocl, vassocr, vassoc4.
        rewrite rwhisker_lwhisker.
        rewrite <- vassoc4.
        rewrite rwhisker_vcomp.
        rewrite vassocr.
        symmetry.

        rewrite vassocl.
        rewrite rwhisker_lwhisker.
        rewrite vassocl, vassoc4.
        rewrite <- inverse_pentagon_7.
        rewrite vassocr, vassocl.
        rewrite rwhisker_vcomp.
        rewrite vassocr, 2 ! vassocl, vassoc4.
        rewrite <- rwhisker_rwhisker.
        rewrite <- vassoc4.
        rewrite rwhisker_vcomp.
        simpl (rwhisker _ _) at 2;
        rewrite inverter_ump_cell_pr1 with (H := p Y).

        rewrite <- 3 ! vassoc4.
        rewrite vassocr with (y := rassociator _ _ _).
        rewrite lassociator_rassociator, id2_left.
        rewrite lwhisker_vcomp, vcomp_linv, lwhisker_id2, id2_right.
        rewrite <- rwhisker_vcomp.
        rewrite vassoc4.
        apply maponpaths with (f := λ x, vcomp2 x _).
        rewrite inverse_pentagon_7.
        rewrite vassocr.
        apply maponpaths with (f := λ x, vcomp2 x _).
        rewrite vassocl, vassoc4.
        rewrite <- lwhisker_lwhisker_rassociator.
        rewrite <- vassoc4.
        rewrite lwhisker_vcomp.
        rewrite vassocl, vassoc4.
        rewrite <- rassociator_rassociator.
        rewrite vassocr, vassocl.
        rewrite lwhisker_vcomp.
        rewrite vassocr.
        rewrite rwhisker_vcomp, lassociator_rassociator, id2_rwhisker, id2_left.
        rewrite vassocr.
        reflexivity.
    Qed.

    Definition modification_inverter_cone_ump_1_from_data
      : has_inverter_ump_1 cone.
    Proof.
      intro other_cone.
      use make_inverter_1cell.
      - refine (make_pstrans
                 (modification_inverter_cone_ump_1_from_data_mor_data _)
                 (modification_inverter_cone_ump_1_from_data_mor_is_pstrans _)).
      - use make_invertible_modification.
        + intro X.
          use (inverter_ump_mor_pr1 (p X)).
        + abstract (
          intros X Y f;
          simpl;
          rewrite inverter_ump_cell_pr1 with (H := p Y);
          rewrite <- 3 ! vassoc4 with (z := rassociator _ _ _);
          rewrite vassocl with (z := rassociator _ _ _);
          rewrite lassociator_rassociator, id2_right;
          rewrite <- 3 ! vassoc4;
          rewrite lwhisker_vcomp, vcomp_linv, lwhisker_id2, id2_right;
          rewrite vassocl, vassoc4;
          rewrite lassociator_rassociator, id2_right;
          rewrite vassocl, vassoc4;
          rewrite lwhisker_vcomp, vcomp_rinv, lwhisker_id2, id2_right;
          apply lassociator_to_rassociator_pre;
          reflexivity).
    Defined.


    Definition modification_inverter_cone_ump_2_from_data
      : has_inverter_ump_2 cone.
    Proof.
      intros F η₁ η₂ n.
      use tpair.
      - use make_modification.
        + intro X.
          exact (inverter_ump_cell (p X) (modcomponent_of n X)).
        + intros X Y f.
          use (inverter_ump_eq_alt (p Y)).
          abstract(
            rewrite <- rwhisker_vcomp;
            apply (vcomp_rcancel (rassociator _ _ _) (is_invertible_2cell_rassociator _ _ _));
            rewrite vassocl;
            rewrite <- rwhisker_lwhisker_rassociator;
            rewrite inverter_ump_cell_pr1 with (H := p Y);

            symmetry;
            rewrite <- rwhisker_vcomp;
            rewrite vassocl;
            apply (vcomp_lcancel (lassociator _ _ _) (is_invertible_2cell_lassociator _ _ _));
            rewrite vassocr;
            rewrite rwhisker_rwhisker;
            rewrite vassocl;

            apply (vcomp_lcancel (lwhisker _ (psnaturality_of (modification_inverter_cone_pr1 cone) f)) (is_invertible_2cell_lwhisker _ (property_from_invertible_2cell _)));
            rewrite vassocr;
            rewrite <- vcomp_whisker;
            rewrite vassocl;

            apply (vcomp_lcancel (rassociator _ _ _) (is_invertible_2cell_rassociator _ _ _));
            rewrite vassocr;
            rewrite <- rwhisker_rwhisker_alt;
            rewrite vassocl;
            rewrite inverter_ump_cell_pr1 with (H := p X);
            set (psnat_of_f := rassociator _ _ _ • _);
            replace psnat_of_f with (cell_from_invertible_2cell (psnaturality_of (compose η₂ (inverter_cone_pr1 cone)) f)) by (simpl; rewrite ! vassocl; reflexivity);
            rewrite <- (modnaturality_of n);

            simpl;
            rewrite 4 ! vassocl;
            reflexivity).
      - abstract (
          use modification_eq;
          intro X;
          apply inverter_ump_cell_pr1 with (H := p X)).
    Defined.

    Lemma modification_inverter_cone_ump_eq_from_data
      : has_inverter_ump_eq cone.
    Proof.
      intros F η₁ η₂ n l₁ l₂ r₁ r₂.
      use modification_eq.
      intro X.
      exact (inverter_ump_eq (p X) (modcomponent_of n X) (modcomponent_of l₁ X) (modcomponent_of l₂ X) (modcomponent_eq r₁ X) (modcomponent_eq r₂ X)).
    Qed.

    Definition modification_inverter_cone_ump_from_data
      : has_inverter_ump cone.
    Proof.
      repeat split.
      - exact modification_inverter_cone_ump_1_from_data.
      - exact modification_inverter_cone_ump_2_from_data.
      - exact modification_inverter_cone_ump_eq_from_data.
    Defined.
  End UniversalMappingPropertyFromData.

  Section InverterOfModificationFromData.
    Context (i : ∏ (b : B₁), B₂)
            (k : ∏ (b : B₁), i b --> F₁ b)
            (inv_km : ∏ (b : B₁), is_invertible_2cell (lwhisker (k b) (m b)))
            (p : ∏ (b : B₁), has_inverter_ump (make_inverter_cone (i b) (k b) (inv_km b))).

    Definition modification_inverter_ob_data
      : psfunctor_data B₁ B₂.
    Proof.
      use make_psfunctor_data.
      - exact i.
      - intros a b f.
        use (inverter_ump_mor_morphism (# F₁ f) (# F₂ f) (inv_of_invertible_2cell _) (inv_of_invertible_2cell _) (mod_inv_naturality_of m a b f) (p b) (k a) (inv_km a)).
        (*refine (toump_mor _ (p b) (k a) (inv_km a)).
        apply modnaturality_of.*)
      - intros a b f g η.
        apply (inverter_ump_cell (p b)).
        exact (inverter_ump_mor_pr1_morphism _ _ _ _ _ _ _ _ • (k a ◃ psfunctor_on_cells F₁ η) • (inverter_ump_mor_pr1_morphism _ _ _ _ _ _ _ _)^-1).
      - intro a.
        apply (inverter_ump_cell (p a)).
        exact (Bicat.lunitor _ • rinvunitor _ • (_ ◃ psfunctor_id F₁ a) • (inverter_ump_mor_pr1_morphism _ _ _ _ _ (p a) _ _)^-1).
      - intros a b c f g.
        use (inverter_ump_cell (p c)).
        exact
          (vcomp2
            (vcomp2
              (vcomp2
                (vcomp2
                  (vcomp2
                    (vcomp2
                      (rassociator _ _ _)
                      (_ ◃ inverter_ump_mor_pr1_morphism _ _ _ _ _ (p c) _ _))
                    (lassociator _ _ _))
                  (rwhisker _ (cell_from_invertible_2cell (inverter_ump_mor_pr1_morphism _ _ _ _ _ (p b) _ _))))
                (rassociator _ _ _))
              (k a ◃ (psfunctor_comp F₁ f g)))
            ((inverter_ump_mor_pr1_morphism _ _ _ _ _ (p c) _ _)^-1)).
    Defined.

    Definition modification_inverter_ob_is_ps
      : psfunctor_laws (modification_inverter_ob_data).
    Proof.
      repeat split.
      (* id2_law *)
      - intros a b f.
        refine (inverter_ump_eq (p b) _ _ _ _ (id2_rwhisker _ _)).
        cbn.
        rewrite inverter_ump_cell_pr1 with (H := (p b)).
        rewrite psfunctor_id2, lwhisker_id2, id2_right, vcomp_rinv.
        reflexivity.
      (* vcomp2_law *)
      - intros a b f g h α β.
        use (inverter_ump_eq_alt (p b)).
        rewrite <- rwhisker_vcomp.
        cbn; rewrite 3 ! inverter_ump_cell_pr1 with (H := (p b)).
        rewrite 2 ! vassocr.
        rewrite vassocl with (z := cell_from_invertible_2cell (inverter_ump_mor_pr1_morphism _ _ _ _ _ (p b) _ _)).
        rewrite vcomp_linv, id2_right.
        rewrite vassocl with (z := lwhisker (k a) _).
        rewrite lwhisker_vcomp.
        rewrite psfunctor_vcomp.
        reflexivity.
      (* lunitor_law *)
      - intros a b f.
        use (inverter_ump_eq_alt (p b)).
        rewrite <- 2 ! rwhisker_vcomp.
        cbn - [PseudoFunctorBicat.psfunctor_id].
        rewrite 2 ! inverter_ump_cell_pr1 with (H := (p b)).

        rewrite vassocl, vassoc4.
        rewrite vassocr with (y := cell_from_invertible_2cell (inverter_ump_mor_pr1_morphism _ _ _ _ _ (p b) _ _)).
        rewrite vassocl with (z := cell_from_invertible_2cell (inverter_ump_mor_pr1_morphism _ _ _ _ _ (p b) _ _)).
        rewrite vcomp_linv, id2_right.
        rewrite vassocl with (z := lwhisker (k a) _).
        rewrite lwhisker_vcomp.

        rewrite 5 ! vassocr.
        rewrite rwhisker_rwhisker_alt.
        rewrite vassocl with (y := rwhisker _ _) (z := lwhisker _ _).
        rewrite vcomp_whisker.
        rewrite vassocr.
        rewrite vassocl with (z := lassociator _ _ _).
        rewrite <- rwhisker_rwhisker.
        rewrite <- vassoc4.
        cbn; rewrite inverter_ump_cell_pr1 with (H := (p a)).
        rewrite rwhisker_vcomp.
        rewrite vassocl with (z := cell_from_invertible_2cell (inverter_ump_mor_pr1_morphism _ _ _ _ _ (p a) _ _)).
        rewrite vcomp_linv, id2_right.

        rewrite psfunctor_F_lunitor.
        rewrite 2 ! vassocr with (x := cell_from_invertible_2cell (psfunctor_comp F₁ (identity a) f)).
        rewrite vcomp_rinv, id2_left.

        rewrite <- vassoc4.
        (*rewrite vassocr with (z := lwhisker (k a) _).*)
        rewrite <- rwhisker_vcomp.
        rewrite vassocl with (y := rwhisker _ _).
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite vassoc4, <- vassoc4.
        rewrite lwhisker_vcomp.
        rewrite vassocr with (x := rwhisker _ _).
        rewrite rwhisker_vcomp, vcomp_rinv, id2_rwhisker, id2_left.

        rewrite lunitor_lwhisker.
        rewrite <- vassoc4.
        rewrite rwhisker_vcomp.
        rewrite vassocl with (z := Bicat.runitor (k a)).
        rewrite rinvunitor_runitor, id2_right.
        rewrite lunitor_triangle.
        rewrite vassocl with (x := rassociator _ _ _).
        rewrite vcomp_lunitor.
        rewrite vassocr.
        rewrite lunitor_assoc.
        rewrite vassocr, rassociator_lassociator, id2_left.
        rewrite vassocl, vcomp_rinv, id2_right.

        reflexivity.
      (* runitor_law *)
      - intros a b f.
        use (inverter_ump_eq_alt (p b)).
        rewrite <- 2 ! rwhisker_vcomp.
        cbn - [PseudoFunctorBicat.psfunctor_id];
        rewrite 2 ! inverter_ump_cell_pr1 with (H := (p b)).

        rewrite vassocl, vassoc4.
        rewrite vassocl with (y := (inverter_ump_mor_pr1_morphism _ _ _ _ _ (p b) _ _)^-1).
        rewrite vassocr with (x := (inverter_ump_mor_pr1_morphism _ _ _ _ _ (p b) _ _)^-1).
        rewrite vcomp_linv, id2_left.

        rewrite vassocl with (z := lwhisker (k a) _).
        rewrite lwhisker_vcomp.
        rewrite psfunctor_F_runitor.
        rewrite 2 ! vassocr with (x := cell_from_invertible_2cell (psfunctor_comp F₁ f (identity b))).
        rewrite vcomp_rinv, id2_left.

        rewrite 5 ! vassocr with (x := rwhisker (k b) _).
        rewrite <- rwhisker_lwhisker_rassociator.
        cbn; rewrite inverter_ump_cell_pr1 with (H := (p b)).
        (*rewrite vassoc4.*)
        rewrite vassocl with (y := lwhisker _ _) (z := lwhisker _ _).
        rewrite lwhisker_vcomp.
        rewrite vassocl with (y := inv_cell (inverter_ump_mor_pr1_morphism _ _ _ _ _ (p b) _ _)).
        rewrite vcomp_linv, id2_right.

        rewrite <- lwhisker_vcomp with (f := k a).
        rewrite vassocr, vassocl with (y := rassociator _ _ _).
        rewrite lwhisker_lwhisker_rassociator.
        rewrite vassocr, vassocl with (y := rwhisker _ _).
        rewrite vcomp_whisker.
        rewrite vassocr, vassocl with (y := lassociator _ _ _).
        rewrite <- lwhisker_lwhisker.
        rewrite <- vassoc4.
        rewrite vassocr, vassocl with (y := lwhisker _ _) (z := lwhisker _ _).
        rewrite lwhisker_vcomp.
        rewrite vassocl with (z := lwhisker (k b) _).
        rewrite lwhisker_vcomp, vcomp_rinv, lwhisker_id2, id2_right.

        rewrite <- lwhisker_vcomp.
        rewrite vassocr, <- vassoc4.
        rewrite rinvunitor_triangle.
        rewrite <- vassoc4.
        rewrite DisplayedInserter.vcomp_rinvunitor.
        rewrite vassocr.
        rewrite lunitor_lwhisker.
        rewrite <- vassoc4.
        rewrite <- left_unit_inv_assoc.
        rewrite <- vassoc4.
        rewrite lwhisker_vcomp, rinvunitor_runitor, lwhisker_id2, id2_right.
        rewrite vassocl, vcomp_rinv, id2_right.
        reflexivity.
      (* lassociator_law *)
      - intros a b c d f g h.
        use (inverter_ump_eq_alt (p d)).
        rewrite <- ! rwhisker_vcomp.
        set (Icomp1 := rwhisker _ (lwhisker _ _)).
        set (Icomp2 := rwhisker _ (rwhisker _ _)).
        cbn; rewrite 3 ! inverter_ump_cell_pr1 with (H := (p d)).

        rewrite vassocr, <- vassoc4, vassocl, vassoc4.
        rewrite vassocl with (y := (inverter_ump_mor_pr1_morphism _ _ _ _ _ (p d) _ _)^-1).
        rewrite vcomp_linv, id2_right.
        rewrite vassocl, vassoc4.
        rewrite vassocl with (z := lwhisker (k a) _).
        rewrite lwhisker_vcomp.

        rewrite 5 ! vassocr with (x := Icomp1).
        subst Icomp1.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite vassocl with (y := lwhisker _ _) (z := lwhisker _ _).
        rewrite lwhisker_vcomp.
        cbn; rewrite inverter_ump_cell_pr1 with (H := (p d)).
        rewrite vassocl with (y := (inverter_ump_mor_pr1_morphism _ _ _ _ _ (p d) _ _)^-1).
        rewrite vcomp_linv, id2_right.

        rewrite <- lwhisker_vcomp with (f := inverter_ump_mor_morphism _ _ _ _ _ (p b) (k a) (inv_km a)).
        rewrite <- vassoc4.
        rewrite lwhisker_lwhisker.
        rewrite vassocr, <- vassoc4.
        rewrite <- vcomp_whisker.
        rewrite 2 ! vassocr.
        rewrite vassocl with (z := rassociator _ _ _).
        rewrite <- lwhisker_lwhisker_rassociator.
        rewrite <- vassoc4.
        rewrite lwhisker_vcomp.
        rewrite vassocr with (x := lwhisker _ _).
        rewrite psfunctor_lassociator with (F := F₁).

        rewrite <- 2 ! lwhisker_vcomp with (f := k a).
        rewrite 2 ! vassocr with (x := rassociator _ _ _).
        rewrite lwhisker_hcomp with (α := lassociator _ _ _).
        rewrite inverse_pentagon_4, hcomp_identity_right.
        rewrite <- vassoc4 with (z := lwhisker (k a) _).
        rewrite rwhisker_lwhisker_rassociator.

        rewrite 2 ! vassocr.
        rewrite vassocl with (y := rwhisker _ _) (z := lassociator _ _ _).
        rewrite <- rwhisker_rwhisker.

        rewrite <- 4 ! lwhisker_vcomp.
        rewrite 4 ! vassocr with (x := rassociator _ _ _).
        rewrite lwhisker_hcomp, <- inverse_pentagon_3, hcomp_identity_right.

        rewrite <- vassoc4 with (x := rassociator _ _ _).
        rewrite lwhisker_lwhisker_rassociator.
        rewrite vassoc4 with (x := rassociator _ _ _).

        rewrite vassocr with (y := lassociator _ _ _).
        rewrite vassocl with (y := _ ◃ rassociator _ _ _).
        rewrite vassocl with (z := lassociator _ _ _).
        rewrite <- pentagon_6.

        rewrite vassocr with (y := lassociator _ _ _).
        rewrite vassocl with (z := lassociator _ _ _).
        rewrite rwhisker_lwhisker.
        rewrite vassocr with (y := lassociator _ _ _).

        rewrite 2 ! vassocr.
        do 4 (rewrite vassocl with (z := rwhisker _ _), rwhisker_vcomp).

        rewrite vassocl with (z := _ ◃ lassociator _ _ _).
        rewrite vassocl with (z := lassociator _ _ _).
        rewrite lwhisker_hcomp, <- inverse_pentagon_7, hcomp_identity_left.
        rewrite vassocr.
        rewrite vassocl with (z := rwhisker _ _), rwhisker_vcomp.

        (*RHS*)
        symmetry.
        rewrite vassocl.
        rewrite 6 ! vassocr with (x := Icomp2).
        subst Icomp2.
        rewrite rwhisker_rwhisker_alt.
        rewrite vassocl with (y := rwhisker _ _) (z := lwhisker _ _).
        rewrite vcomp_whisker.
        rewrite <- vassoc4.
        rewrite <- rwhisker_rwhisker.
        cbn; rewrite inverter_ump_cell_pr1 with (H := (p c)).
        rewrite vassocr with (z := rwhisker _ _).
        rewrite <- vassoc4.
        rewrite rwhisker_vcomp.
        rewrite vassocl with (y := (inverter_ump_mor_pr1_morphism _ _ _ _ _ (p c) _ _)^-1).
        rewrite vcomp_linv, id2_right.
        rewrite ! vassocr.
        reflexivity.
      (* lwhisker_law *)
      - intros a b c f g₁ g₂ α.
        use (inverter_ump_eq_alt (p c)).
        rewrite <- 2 ! rwhisker_vcomp.
        set (x := rwhisker _ (lwhisker _ _)).
        cbn; rewrite 3 ! inverter_ump_cell_pr1 with (H := (p c)).
        rewrite 2 ! vassocr.
        rewrite vassocl with (y := inv_cell _).
        rewrite vcomp_linv, id2_right.
        rewrite vassocl with (z := lwhisker (k a) _).
        rewrite lwhisker_vcomp, psfunctor_lwhisker.
        rewrite <- lwhisker_vcomp.
        rewrite vassocr, vassocl with (z := lwhisker (k a) (lwhisker _ _)).
        rewrite lwhisker_lwhisker_rassociator.
        rewrite vassocr, vassocl with (y := rwhisker _ _).
        rewrite vcomp_whisker.
        rewrite vassocr, vassocl with (x := rassociator _ _ _).
        rewrite <- vassoc4.
        rewrite <- lwhisker_lwhisker.
        rewrite vassoc4.
        rewrite lwhisker_vcomp.
        (* RHS *)
        rewrite 6 ! vassocr.
        subst x.
        rewrite <- rwhisker_lwhisker_rassociator.
        cbn; rewrite inverter_ump_cell_pr1 with (H := (p c)).
        rewrite vassocl with (y := lwhisker _ _) (z := lwhisker _ _).
        rewrite lwhisker_vcomp.
        rewrite vassocl with (y := inv_cell _).
        rewrite vcomp_linv, id2_right.
        reflexivity.
      (* rwhisker_law *)
      - intros a b c f g₁ g₂ α.
        use (inverter_ump_eq_alt (p c)).
        rewrite <- 2 ! rwhisker_vcomp.
        set (x := rwhisker _ (rwhisker _ _)).
        cbn; rewrite 3 ! inverter_ump_cell_pr1 with (H := (p c)).
        rewrite 2 ! vassocr.
        rewrite vassocl with (y := inv_cell _).
        rewrite vcomp_linv, id2_right.
        rewrite vassocl with (z := lwhisker (k a) _).
        rewrite lwhisker_vcomp, psfunctor_rwhisker.
        rewrite <- lwhisker_vcomp.

        rewrite vassocr, vassocl with (z := lwhisker (k a) (rwhisker _ _)).
        rewrite rwhisker_lwhisker_rassociator.
        rewrite vassocr, vassocl with (z := rwhisker _ _).
        rewrite rwhisker_vcomp.

        (* RHS *)
        rewrite 6 ! vassocr.
        subst x.
        rewrite rwhisker_rwhisker_alt.
        rewrite vassocl with (y := rwhisker _ _) (z := lwhisker _ _).
        rewrite vcomp_whisker.
        rewrite <- vassoc4.
        rewrite <- rwhisker_rwhisker.
        rewrite vassocr, <- vassoc4.
        rewrite rwhisker_vcomp.
        rewrite vassocr.
        cbn; rewrite inverter_ump_cell_pr1 with (H := (p b)).
        rewrite vassocl with (y := inv_cell _).
        rewrite vcomp_linv, id2_right.
        reflexivity.
    Qed.

    Definition modification_inverter_ob
      : psfunctor B₁ B₂.
    Proof.
      use make_psfunctor.
      - exact modification_inverter_ob_data.
      - exact modification_inverter_ob_is_ps.
      - split.
        + intro a.
          cbn; use (inverter_ump_is_invertible_2cell (p a)).
          is_iso.
          apply psfunctor_id.
        + intros a b c f g.
          cbn; use (inverter_ump_is_invertible_2cell (p c)).
          is_iso.
          * apply property_from_invertible_2cell.
          * apply property_from_invertible_2cell.
          * apply psfunctor_comp.
    Defined.

    Definition modification_inverter_pr1_data
      : pstrans_data modification_inverter_ob F₁.
    Proof.
      use make_pstrans_data.
      - exact k.
      - intros X Y f.
        use inv_of_invertible_2cell.
        exact (make_invertible_2cell (inverter_ump_mor_pr1_morphism _ _ _ _ _ (p Y) _ _)).
    Defined.

    Definition modification_inverter_pr1_is_pstrans
      : is_pstrans modification_inverter_pr1_data.
    Proof.
      repeat split.
      - intros X Y f g α.
        cbn; rewrite (inverter_ump_cell_pr1 (p Y)).
        rewrite 2 ! vassocr.
        rewrite vcomp_linv, id2_left.
        reflexivity.
      - intro X.
        cbn; rewrite (inverter_ump_cell_pr1 (p X)).
        rewrite 2 ! vassocl, 2 ! vassoc4.
        rewrite linvunitor_lunitor, id2_right.
        rewrite runitor_rinvunitor, id2_left.
        reflexivity.
      - intros X Y Z f g.
        cbn; rewrite (inverter_ump_cell_pr1 (p Z)).
        rewrite 5 ! vassocl with (x := rassociator _ _ _), vassocl, vassoc4.
        rewrite lassociator_rassociator, id2_right.
        rewrite 4 ! vassocl with (x := _ ◃ _), vassocl, vassoc4.
        rewrite lwhisker_vcomp, vcomp_linv, lwhisker_id2, id2_right.
        rewrite 3 ! vassocl with (x := lassociator _ (k Y) _), vassocl, vassoc4.
        rewrite rassociator_lassociator, id2_right.
        rewrite 2 ! vassocl with (x := _ ▹ _), vassocl, vassoc4.
        rewrite rwhisker_vcomp, vcomp_linv, id2_rwhisker, id2_right.
        rewrite 2 ! vassocr.
        rewrite lassociator_rassociator, id2_left.
        reflexivity.
    Qed.

    Definition modification_inverter_pr1
      : pstrans modification_inverter_ob F₁
      := make_pstrans modification_inverter_pr1_data
           modification_inverter_pr1_is_pstrans.

    Definition modification_inverter_is_invertible_cell
      : is_invertible_modification ((modification_inverter_pr1) ◃ m).
    Proof.
      use make_is_invertible_modification.
      exact inv_km.
    Defined.

    Definition modification_inverter_cone
      := make_inverter_cone modification_inverter_ob modification_inverter_pr1 modification_inverter_is_invertible_cell.

    Definition modification_inverter_ump
      := modification_inverter_cone_ump_from_data modification_inverter_cone p.
  End InverterOfModificationFromData.
End InverterOfModification.


Section LeftWhiskerOfModificationInverterCone.
  Context {B₁ B₂ B₃: bicat}
          {F₁ F₂ : psfunctor B₁ B₂}
          (G : psfunctor B₂ B₃)
          {ρ σ : pstrans F₁ F₂}
          {m : modification ρ σ}
          (cone : @inverter_cone _ _ _ _ _ m).

  Definition left_whisker_modification_inverter_cone
    := psfunctor_inverter_cone (post_comp_psfunctor G) cone.

  Definition left_whisker_modification_inverter_ump_on_data
             (p : ∏ (b : B₁),
                  has_inverter_ump
                    (modification_inverter_cone_component_of _ cone b))
             (HG : preserves_inverters G)
    : (∏ (b : B₁),
       has_inverter_ump
         (modification_inverter_cone_component_of _
           left_whisker_modification_inverter_cone b)).
  Proof.
    intro b.
    exact (HG _ _ _ _ _ _ (p b)).
  Defined.

  Definition left_whisker_modification_inverter_ump_from_data
             (p : ∏ (b : B₁),
                  has_inverter_ump
                    (modification_inverter_cone_component_of _ cone b))
             (HG : preserves_inverters G)
    : has_inverter_ump left_whisker_modification_inverter_cone
    := modification_inverter_cone_ump_from_data _
         left_whisker_modification_inverter_cone
         (left_whisker_modification_inverter_ump_on_data p HG).
End LeftWhiskerOfModificationInverterCone.


Section RightWhiskerOfModificationInverterCone.
  Context {B₁ B₂ B₃: bicat}
          (F : psfunctor B₁ B₂)
          {G₁ G₂ : psfunctor B₂ B₃}
          {ρ σ : pstrans G₁ G₂}
          {m : modification ρ σ}
          (cone : @inverter_cone _ _ _ _ _ m).

  Definition right_whisker_modification_inverter_cone
    := psfunctor_inverter_cone (pre_comp_psfunctor F) cone.

  Definition right_whisker_modification_inverter_ump_on_data
             (p : ∏ (b : B₂),
                  has_inverter_ump
                    (modification_inverter_cone_component_of _ cone b))
    : (∏ (b : B₁),
       has_inverter_ump
         (modification_inverter_cone_component_of _
            right_whisker_modification_inverter_cone b)).
  Proof.
    intro b.
    exact (p (F b)).
  Defined.

  Definition right_whisker_modification_inverter_ump_from_data
             (p : ∏ (b : B₂),
                  has_inverter_ump
                    (modification_inverter_cone_component_of _ cone b))
    : has_inverter_ump right_whisker_modification_inverter_cone
    := modification_inverter_cone_ump_from_data _
         right_whisker_modification_inverter_cone
         (right_whisker_modification_inverter_ump_on_data p).
End RightWhiskerOfModificationInverterCone.
