(* ******************************************************************************* *)
(** * Left whiskering of pseudonatural transformation starting from an identity
    Gabriel Merlin
    January 2025
 ********************************************************************************* *)
Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Modifications.Examples.Associativity.
Require Import MorePseudoTransformations.

Local Open Scope cat.
Local Open Scope bicategory.


Definition comp_rinvunitor_left_whisker_right_whisker
           {B₁ B₂ : bicat}
           {F₁ F₂ : psfunctor B₁ B₂}
           {G : psfunctor B₁ B₁}
           (σ : pstrans F₁ F₂)
           (τ : pstrans (id_psfunctor B₁) G)
  : invertible_modification (σ · (rinvunitor_pstrans F₂ · (F₂ ◅ τ)))
      (rinvunitor_pstrans F₁ · (F₁ ◅ τ) · (σ ▻ G))
  := comp_of_invertible_2cell
       (comp_of_invertible_2cell
         (comp_of_invertible_2cell
           (comp_of_invertible_2cell
             (lassociator_invertible_2cell _ _ _)
             (rwhisker_of_invertible_2cell _
               (inv_of_invertible_2cell (vcomp_rinvunitor_modification σ))))
           (rassociator_invertible_2cell _ _ _))
         (lwhisker_of_invertible_2cell _ (pstrans_script_pstrans σ τ)))
       (lassociator_invertible_2cell _ _ _).

Definition left_whisker_comp_rinvunitor_left_whisker
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₁}
           (G : psfunctor B₁ B₂)
           (H : psfunctor B₂ B₃)
           (σ : pstrans (id_psfunctor B₁) F)
  : invertible_modification
      ((H ◅ (rinvunitor_pstrans G · (G ◅ σ))) · lassociator_pstrans F G H)
      (rinvunitor_pstrans _ · (comp_psfunctor H G ◅ σ))
  := comp_of_invertible_2cell
       (comp_of_invertible_2cell
          (comp_of_invertible_2cell
             (comp_of_invertible_2cell
                (rwhisker_of_invertible_2cell _
                   (inv_of_invertible_2cell (left_whisker_comp_pstrans H _ _)))
                (rassociator_invertible_2cell _ _ _))
             (lwhisker_of_invertible_2cell _ (left_whisker_left_whisker G H σ)))
          (lassociator_invertible_2cell _ _ _))
       (rwhisker_of_invertible_2cell _ (rinvunitor_pstrans_triangle G H)).


Definition right_whisker_comp_runitor_left_whisker
           {B₁ B₂ B₃ : bicat}
           (F : psfunctor B₁ B₂)
           {G : psfunctor B₂ B₂}
           (H : psfunctor B₂ B₃)
           (σ : pstrans G (id_psfunctor B₂))
  : invertible_modification
      (H ◅ (σ ▻ F) · lunitor_pstrans F)
      (lassociator_pstrans F G H · ((H ◅ σ) · runitor_pstrans H ▻ F))
  := comp_of_invertible_2cell
       (comp_of_invertible_2cell
          (comp_of_invertible_2cell
             (comp_of_invertible_2cell
                (comp_of_invertible_2cell
                   (inv_of_invertible_2cell (left_whisker_comp_pstrans H _ _))
                   (lwhisker_of_invertible_2cell _
                      (inv_of_invertible_2cell (runitor_right_whisker F H))))
                (lassociator_invertible_2cell _ _ _))
             (rwhisker_of_invertible_2cell _ (right_whisker_left_whisker F H σ)))
          (rassociator_invertible_2cell _ _ _))
       (lwhisker_of_invertible_2cell _ (right_whisker_comp_pstrans F _ _)).

Definition right_whisker_comp_runitor_left_whisker_alt
           {B₁ B₂ B₃ : bicat}
           (F : psfunctor B₁ B₂)
           {G : psfunctor B₂ B₂}
           (H : psfunctor B₂ B₃)
           (σ : pstrans G (id_psfunctor B₂))
  : invertible_modification
      (rassociator_pstrans F G H · (H ◅ (σ ▻ F) · lunitor_pstrans F))
      ((H ◅ σ) · runitor_pstrans H ▻ F)
  := comp_of_invertible_2cell
       (comp_of_invertible_2cell
          (comp_of_invertible_2cell
             (comp_of_invertible_2cell
                (comp_of_invertible_2cell
                   (lwhisker_of_invertible_2cell _
                      (inv_of_invertible_2cell (left_whisker_comp_pstrans H _ _)))
                   (lassociator_invertible_2cell _ _ _))
                (rwhisker_of_invertible_2cell _ (right_whisker_left_whisker_rassociator F H σ)))
             (rassociator_invertible_2cell _ _ _))
          (lwhisker_of_invertible_2cell _ (lunitor_left_whisker F H)))
       (right_whisker_comp_pstrans F _ _).


Definition right_whisker_comp_rinvunitor_left_whisker
           {B₁ B₂ B₃ : bicat}
           (F : psfunctor B₁ B₂)
           {G : psfunctor B₂ B₂}
           (H : psfunctor B₂ B₃)
           (σ : pstrans (id_psfunctor B₂) G)
  : invertible_modification
      ((H ◅ linvunitor_pstrans F · (σ ▻ F)) · lassociator_pstrans F G H)
      (rinvunitor_pstrans H · (H ◅ σ) ▻ F)
  := comp_of_invertible_2cell
       (comp_of_invertible_2cell
          (comp_of_invertible_2cell
             (comp_of_invertible_2cell
                (comp_of_invertible_2cell
                   (rwhisker_of_invertible_2cell _
                      (inv_of_invertible_2cell (left_whisker_comp_pstrans H _ _)))
                   (rassociator_invertible_2cell _ _ _))
                (lwhisker_of_invertible_2cell _ (right_whisker_left_whisker F H σ)))
             (lassociator_invertible_2cell _ _ _))
          (rwhisker_of_invertible_2cell _ (linvunitor_left_whisker F H)))
       (right_whisker_comp_pstrans F _ _).

Definition right_whisker_comp_rinvunitor_left_whisker_alt
           {B₁ B₂ B₃ : bicat}
           (F : psfunctor B₁ B₂)
           {G : psfunctor B₂ B₂}
           (H : psfunctor B₂ B₃)
           (σ : pstrans (id_psfunctor B₂) G)
  : invertible_modification
      (H ◅ linvunitor_pstrans F · (σ ▻ F))
      ((rinvunitor_pstrans H · (H ◅ σ) ▻ F) · rassociator_pstrans F G H)
  := comp_of_invertible_2cell
       (comp_of_invertible_2cell
          (comp_of_invertible_2cell
             (rinvunitor_invertible_2cell _)
             (lwhisker_of_invertible_2cell _
                (inv_of_invertible_2cell (lassociator_rassociator_pstrans F G H))))
          (lassociator_invertible_2cell _ _ _))
       (rwhisker_of_invertible_2cell _ (right_whisker_comp_rinvunitor_left_whisker F H σ)).


Definition comp_linvunitor_right_whisker_left_whisker
           {B₁ B₂ : bicat}
           {F : psfunctor B₂ B₂}
           {G₁ G₂ : psfunctor B₁ B₂}
           (σ : pstrans (id_psfunctor B₂) F)
           (τ : pstrans G₁ G₂)
  : invertible_modification (linvunitor_pstrans G₁ · (σ ▻ G₁) · (F ◅ τ))
      (τ · (linvunitor_pstrans G₂ · (σ ▻ G₂)))
  := (comp_of_invertible_2cell
       (comp_of_invertible_2cell
         (comp_of_invertible_2cell
           (comp_of_invertible_2cell
             (rassociator_invertible_2cell _ _ _)
             (lwhisker_of_invertible_2cell _ (pstrans_script_pstrans σ τ)))
           (lassociator_invertible_2cell _ _ _))
         (rwhisker_of_invertible_2cell _ (vcomp_linvunitor_modification τ)))
       (rassociator_invertible_2cell _ _ _)).

Definition comp_linvunitor_right_whisker_right_whisker
           {B₁ B₂ B₃ : bicat}
           (F : psfunctor B₁ B₂)
           (G : psfunctor B₂ B₃)
           {H : psfunctor B₃ B₃}
           (σ : pstrans (id_psfunctor B₃) H)
  : invertible_modification
      ((linvunitor_pstrans G · (σ ▻ G) ▻ F) · rassociator_pstrans F G H)
      (linvunitor_pstrans (comp_psfunctor G F) · (σ ▻ comp_psfunctor G F))
  := comp_of_invertible_2cell
       (comp_of_invertible_2cell
          (comp_of_invertible_2cell
             (comp_of_invertible_2cell
                (rwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (right_whisker_comp_pstrans F _ _)))
                (rassociator_invertible_2cell _ _ _))
             (lwhisker_of_invertible_2cell _ (right_whisker_right_whisker_rassociator F G σ)))
         (lassociator_invertible_2cell _ _ _))
       (rwhisker_of_invertible_2cell _ (linvunitor_pstrans_triangle F G)).

Definition comp_linvunitor_right_whisker_right_whisker_alt
           {B₁ B₂ B₃ : bicat}
           (F : psfunctor B₁ B₂)
           (G : psfunctor B₂ B₃)
           {H : psfunctor B₃ B₃}
           (σ : pstrans (id_psfunctor B₃) H)
  : invertible_modification
      ((linvunitor_pstrans G · (σ ▻ G) ▻ F))
      (linvunitor_pstrans (comp_psfunctor G F) · (σ ▻ comp_psfunctor G F)
       · lassociator_pstrans F G H)
  := comp_of_invertible_2cell
      (comp_of_invertible_2cell
         (comp_of_invertible_2cell
            (rinvunitor_invertible_2cell _)
            (lwhisker_of_invertible_2cell _
               (inv_of_invertible_2cell (rassociator_lassociator_pstrans F G H))))
         (lassociator_invertible_2cell _ _ _))
      (rwhisker_of_invertible_2cell _ (comp_linvunitor_right_whisker_right_whisker F G σ)).
