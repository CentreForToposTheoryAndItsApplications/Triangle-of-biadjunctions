(* ************************************************************************* *)
(** * Pentagonators between pseudo transformations.
    Gabriel Merlin
    January 2025
 *************************************************************************** *)
Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Modifications.Examples.Associativity.

Require Import MorePseudoTransformations.
Require Import PrePostCompositionByPseudoFunctor.

Local Open Scope cat.

Section AssociativityPentagons.
  Context {B₁ B₂ B₃ B₄ B₅ : bicat}.
  Variables (F : psfunctor B₁ B₂)
            (G : psfunctor B₂ B₃)
            (H : psfunctor B₃ B₄)
            (I : psfunctor B₄ B₅).

  Definition lassociator_lassociator_pstrans
    : invertible_modification
        ((I ◅ lassociator_pstrans F G H) · lassociator_pstrans F (comp_psfunctor H G) I · (lassociator_pstrans G H I ▻ F))
        (lassociator_pstrans (comp_psfunctor G F) H I · lassociator_pstrans F G (comp_psfunctor I H)).
  Proof.
    (* Precompose by invertible modifications to make appear (rassociator_pstrans F G (comp_psfunctor I H) · lassociator_pstrans F G (comp_psfunctor I H)) on the lhs and the whisker. *)
    use (comp_of_invertible_2cell (rinvunitor_invertible_2cell _)).
    use (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (rassociator_lassociator_pstrans F G (comp_psfunctor I H))))).
    use (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _)).
    use rwhisker_of_invertible_2cell.

    (* Precompose by invertible modifications to make appear (rassociator_pstrans (comp_psfunctor G F) H I · lassociator_pstrans (comp_psfunctor G F) H I) on the lhs and the whisker. *)
    use (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ (rinvunitor_invertible_2cell _))).
    use (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (rassociator_lassociator_pstrans _ _ _))))).
    use (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _))).
    use (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _)).
    use (comp_of_invertible_2cell _ (lunitor_invertible_2cell _)).
    use rwhisker_of_invertible_2cell.

    (* Postcompose by invertible modifications to make appear (I ◅ lassociator_pstrans F G H) · (I ◅ rassociator_pstrans F G H) on the rhs. *)
    use (comp_of_invertible_2cell _ (left_whisker_id_pstrans _ _)).
    use (comp_of_invertible_2cell _ (psfunctor_invertible_modification I (lassociator_rassociator_pstrans _ _ _))).
    use (comp_of_invertible_2cell _ (left_whisker_comp_pstrans I _ _)).

    (* Postcompose by invertible modifications to make appear (lassociator_pstrans F (comp_psfunctor H G) I · rassociator_pstrans F (comp_psfunctor H G) I) on the rhs. *)
    use (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (runitor_invertible_2cell _))).
    use (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (lassociator_rassociator_pstrans _ _ _)))).
    use (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _))).
    use (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)).

    (* Postcompose by invertible modifications to make appear ((lassociator_pstrans G H I) ▻ F) · ((rassociator_pstrans G H I) ▻ F) on the rhs. *)
    use (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (runitor_invertible_2cell _))).
    use (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (id_pstrans_right_whisker _ _)))).
    use (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (invertible_modification_psfunctor F (lassociator_rassociator_pstrans _ _ _))))).
    use (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (right_whisker_comp_pstrans F _ _)))).
    use (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _))).
    use (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)).
    use (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _))).
    refine (lwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (rassociator_rassociator_pstrans F G H I))).
  Defined.


  Definition pentagon_2_pstrans
    : invertible_modification
        ((I ◅ lassociator_pstrans F G H) · lassociator_pstrans F (comp_psfunctor H G) I)
        (lassociator_pstrans (comp_psfunctor G F) H I · lassociator_pstrans F G (comp_psfunctor I H) · (rassociator_pstrans G H I ▻ F)).
  Proof.
    (* Precompose by invertible modifications to make appear (lassociator_pstrans G H I ▻ F) · (rassociator_pstrans G H I ▻ F) on the lhs. *)
    use (comp_of_invertible_2cell (rinvunitor_invertible_2cell _)).
    use (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (id_pstrans_right_whisker _ F)))).
    use (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ (invertible_modification_psfunctor F (inv_of_invertible_2cell (lassociator_rassociator_pstrans _ _ _))))).
    use (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (right_whisker_comp_pstrans F _ _)))).
    use (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _)).

    use rwhisker_of_invertible_2cell.
    apply lassociator_lassociator_pstrans.
  Defined.

  Definition inverse_pentagon_2_pstrans
    : invertible_modification
        (((lassociator_pstrans G H I) ▻ F) · rassociator_pstrans F G (comp_psfunctor I H))
        (rassociator_pstrans F (comp_psfunctor H G) I
        · (I ◅ rassociator_pstrans F G H)
        · lassociator_pstrans (comp_psfunctor G F) H I).
  Proof.
    (* Precompose by invertible modifications to make (lassociator_pstrans (comp_psfunctor G F) H I) appear to the right of (rassociator_pstrans F G (comp_psfunctor I H)). *)
    use (comp_of_invertible_2cell (rinvunitor_invertible_2cell _)).
    use (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (rassociator_lassociator_pstrans (comp_psfunctor G F) H I)))).
    use (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _)).

    (* Use right whiskering by (lassociator_pstrans (comp_psfunctor G F) H I). *)
    use rwhisker_of_invertible_2cell.
    use (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _)).

    (* Postcompose to make (lassociator_pstrans G H I ▻ F) appear to the left of (rassociator_pstrans F (comp_psfunctor H G) I). *)
    use (comp_of_invertible_2cell _ (lunitor_invertible_2cell _)).
    use (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (id_pstrans_right_whisker _ F))).
    use (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (invertible_modification_psfunctor F (lassociator_rassociator_pstrans G H I)))).
    use (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (right_whisker_comp_pstrans F _ _))).
    use (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)).

    use lwhisker_of_invertible_2cell.
    use (comp_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _)).
    use inv_of_invertible_2cell.
    apply rassociator_rassociator_pstrans.
  Defined.


  Definition inverse_pentagon_4_pstrans
    : invertible_modification
        (rassociator_pstrans (comp_psfunctor G F) H I · (I ◅ lassociator_pstrans F G H))
        (lassociator_pstrans F G (comp_psfunctor I H)
        · ((rassociator_pstrans G H I) ▻ F)
        · rassociator_pstrans F (comp_psfunctor H G) I).
  Proof.
    (* Precompose by invertible modifications to make (lassociator_pstrans F G (comp_psfunctor I H) · (rassociator_pstrans F G (comp_psfunctor I H)) appear on the lhs. *)
    use (comp_of_invertible_2cell (linvunitor_invertible_2cell _)).
    use (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (lassociator_rassociator_pstrans _ _ _)))).
    use (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _)).
    use (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)).
    use lwhisker_of_invertible_2cell.

    (* Postcompose to make (I ◅ rassociator_pstrans F G H) · (I ◅ lassociator_pstrans F G H) appear on the rhs. *)
    use (comp_of_invertible_2cell _ (runitor_invertible_2cell _)).
    use (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (left_whisker_id_pstrans _ _))).
    use (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (psfunctor_invertible_modification I (rassociator_lassociator_pstrans _ _ _)))).
    use (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (left_whisker_comp_pstrans I _ _))).
    use (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _)).
    use (comp_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _)).
    use rwhisker_of_invertible_2cell.

    use inv_of_invertible_2cell.
    apply rassociator_rassociator_pstrans.
  Defined.

  Definition inverse_pentagon_5_pstrans
    : invertible_modification
        ((I ◅ (rassociator_pstrans F G H)) · lassociator_pstrans (comp_psfunctor G F) H I)
        (lassociator_pstrans F (comp_psfunctor H G) I
        · (lassociator_pstrans G H I ▻ F)
        · rassociator_pstrans F G (comp_psfunctor I H)).
  Proof.
    (* Postcompose by invertible modifications to make (lassociator_pstrans (comp_psfunctor G F) H I) appear to the right of (rassociator_pstrans F G (comp_psfunctor I H)). *)
    use (comp_of_invertible_2cell _ (runitor_invertible_2cell _)).
    use (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (rassociator_lassociator_pstrans (comp_psfunctor G F) H I))).
    use (comp_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _)).

    (* Use right whiskering by (lassociator_pstrans (comp_psfunctor G F) H I). *)
    use rwhisker_of_invertible_2cell.
    do 2 use (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)).

    (* Precompose to make (lassociator_pstrans F (comp_psfunctor H G) I) appear to the left of (I ◅ rassociator_pstrans F G H). *)
    use (comp_of_invertible_2cell (linvunitor_invertible_2cell _)).
    use (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (lassociator_rassociator_pstrans F (comp_psfunctor H G) I)))).
    use (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _)).
    use lwhisker_of_invertible_2cell.

    (* Precompose to make (lassociator_pstrans G H I ▻ F) appear to the left of (rassociator_pstrans F G (comp_psfunctor I H)). *)
    use (comp_of_invertible_2cell (linvunitor_invertible_2cell _)).
    use (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (id_pstrans_right_whisker _ F)))).
    use (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (invertible_modification_psfunctor F (lassociator_rassociator_pstrans G H I))))).
    use (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (right_whisker_comp_pstrans F _ _)))).
    use (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _)).
    use lwhisker_of_invertible_2cell.

    use (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _)).
    apply rassociator_rassociator_pstrans.
  Defined.


  Definition inverse_pentagon_7_pstrans
    : invertible_modification
        (lassociator_pstrans F G (comp_psfunctor I H) · (rassociator_pstrans G H I ▻ F))
        (rassociator_pstrans (comp_psfunctor G F) H I · (I ◅ lassociator_pstrans F G H) · lassociator_pstrans F (comp_psfunctor H G) I).
  Proof.
    (* Precompose to make apear (rassociator_pstrans (comp_psfunctor G F) H I) · (lassociator_pstrans (comp_psfunctor G F) H I) on the rhs. *)
    use (comp_of_invertible_2cell (linvunitor_invertible_2cell _)).
    use (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (rassociator_lassociator_pstrans _ _ _)))).
    use (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _)).
    use (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)).
    use lwhisker_of_invertible_2cell.

    (* Postcompose to make apear (lassociator_pstrans G H I ▻ F) · (rassociator_pstrans G H I ▻ F) on the rhs. *)
    use (comp_of_invertible_2cell _ (runitor_invertible_2cell _)).
    use (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (id_pstrans_right_whisker _ _))).
    use (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (invertible_modification_psfunctor F (lassociator_rassociator_pstrans _ _ _)))).
    use (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (right_whisker_comp_pstrans F _ _))).
    use (comp_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _)).
    use (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _)).
    use rwhisker_of_invertible_2cell.

    use inv_of_invertible_2cell.
    apply lassociator_lassociator_pstrans.
  Defined.
End AssociativityPentagons.
