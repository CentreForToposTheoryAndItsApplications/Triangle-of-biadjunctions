(* ******************************************************************************* *)
(** * Tricategorical for pseudofunctors
    Gabriel Merlin
    January 2025

 Some of the tricategorical aspects of pseudofunctors are given here.

 ********************************************************************************* *)
Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Modifications.Examples.Associativity.
Require Import UniMath.Bicategories.Modifications.Examples.Unitality.

Local Open Scope cat.

Lemma pstrans_comp_whisker
      {C D : bicat}
      {F G : psfunctor C D}
      (η : pstrans F G)
      {X Y Z : C}
      (f: X --> Y) (g: Y --> Z) :
lwhisker (# F f) (psnaturality_of η g) = 
vcomp2
  (vcomp2
    (vcomp2
      (vcomp2
        (vcomp2
          (lassociator (# F f) (η Y) (# G g))
          (rwhisker (# G g) (inv_cell (psnaturality_of η f))))
        (rassociator (η X) (# G f) (# G g)))
      (vcomp2 (lwhisker (η X) (psfunctor_comp G f g)) (psnaturality_of η (f · g))))
    (rwhisker (η Z) (inv_cell (psfunctor_comp F f g))))
  (rassociator (# F f) (# F g) (η Z)).
Proof.
  rewrite pstrans_comp.
  rewrite ! vassocl with (z := rwhisker (η Z) (inv_cell (psfunctor_comp F f g))).
  rewrite rwhisker_vcomp.
  rewrite vcomp_rinv.
  rewrite id2_rwhisker.
  rewrite id2_right.
  rewrite ! vassocl with (z := rassociator (# F f) (# F g) (η Z)).
  rewrite lassociator_rassociator.
  rewrite id2_right.
  rewrite vassocl with (y := rassociator (η X) (# G f) (# G g)).
  rewrite ! vassocl with (x := lassociator (η X) (# G f) (# G g)).
  rewrite vassocr with (y := lassociator (η X) (# G f) (# G g)).
  rewrite rassociator_lassociator.
  rewrite id2_left.
  rewrite ! vassocl with (y := rwhisker (# G g) (inv_cell (psnaturality_of η f))).
  rewrite ! vassocl with (x := rwhisker (# G g) (psnaturality_of η f)).
  rewrite vassocr with (y := rwhisker (# G g) (psnaturality_of η f)).
  rewrite rwhisker_vcomp.
  rewrite vcomp_linv.
  rewrite id2_rwhisker.
  rewrite id2_left.
  rewrite vassocr.
  rewrite lassociator_rassociator.
  rewrite id2_left.
  reflexivity.
Qed.

Definition pstrans_script_pstrans_data
           {B₁ B₂ B₃ : bicat}
           {F₁ F₂ : psfunctor B₂ B₃}
           {G₁ G₂ : psfunctor B₁ B₂}
           (σ : pstrans F₁ F₂)
           (τ : pstrans G₁ G₂)
  : invertible_modification_data (comp_pstrans (σ ▻ G₁) (F₂ ◅ τ)) (comp_pstrans (F₁ ◅ τ) (σ ▻ G₂)).
Proof.
  red.
  intro.
  refine ((psnaturality_of σ (τ _))).
Defined.

Lemma invertible_2cell_of_rwhisker
      {B : bicat}
      {x y z : B}
      {f₁ f₂ : x --> y}
      (g : y --> z)
      (α : invertible_2cell f₁ f₂)
  : rwhisker g α = rwhisker_of_invertible_2cell g α.
Proof.
  reflexivity.
Defined.

Lemma invertible_2cell_of_rwhisker_inv
      {B : bicat}
      {x y z : B}
      {f₁ f₂ : x --> y}
      (g : y --> z)
      (α : invertible_2cell f₁ f₂)
  : rwhisker g (inv_cell α) = inv_cell (rwhisker_of_invertible_2cell g α).
Proof.
  reflexivity.
Defined.


Definition pstrans_script_pstrans_is_modification
           {B₁ B₂ B₃ : bicat}
           {F₁ F₂ : psfunctor B₂ B₃}
           {G₁ G₂ : psfunctor B₁ B₂}
           (σ : pstrans F₁ F₂)
           (τ : pstrans G₁ G₂)
  : is_modification (pstrans_script_pstrans_data σ τ).
Proof.
  intros X Y f; simpl.
  rewrite 4 ! vassocl with (x := rassociator (σ (G₁ X)) (# F₂ (τ X)) (# F₂ (# G₂ f))).
  apply lassociator_to_rassociator_pre.
  refine (!_).
  rewrite <- 2 ! rwhisker_vcomp.
  rewrite ! vassocr.
  apply lassociator_to_rassociator_post.
  use vcomp_move_R_Mp; is_iso.
  refine (maponpaths (λ x, x • _) (!_) @ _).
  { apply (pstrans_comp σ). }
  refine (!_).
  rewrite 5 ! vassocl with (x := σ (G₁ X) ◃ _).
  etrans.
  {
    apply maponpaths.
    refine (!_).
    apply (pstrans_comp σ).
  }
  rewrite vassocr, lwhisker_vcomp.
  rewrite vassocl, vcomp_linv, id2_right.
  rewrite <- lwhisker_vcomp, 2 ! vassocl.
  apply maponpaths, psnaturality_natural.
Qed.

Definition pstrans_script_pstrans
           {B₁ B₂ B₃ : bicat}
           {F₁ F₂ : psfunctor B₂ B₃}
           {G₁ G₂ : psfunctor B₁ B₂}
           (σ : pstrans F₁ F₂)
           (τ : pstrans G₁ G₂)
  : invertible_modification (comp_pstrans (σ ▻ G₁) (F₂ ◅ τ)) (comp_pstrans (F₁ ◅ τ) (σ ▻ G₂)).
Proof.
  use make_invertible_modification.
  - exact (pstrans_script_pstrans_data σ τ).
  - exact (pstrans_script_pstrans_is_modification σ τ).
Defined.


Definition vcomp_runitor_modification_data
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : invertible_modification_data
      (comp_pstrans (η ▻ id_psfunctor C) (runitor_pstrans G))
      (comp_pstrans (runitor_pstrans F) η).
Proof.
  intro X; cbn.
  use make_invertible_2cell.
  + exact (runitor (η X) • linvunitor (η X)).
  + is_iso.
Defined.

Definition vcomp_runitor_modification_is_modification
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : is_modification (vcomp_runitor_modification_data η).
Proof.
  intros X Y f; cbn.

  (* LHS *)
  rewrite <- lwhisker_vcomp.
  rewrite vassocr.
  rewrite lunitor_lwhisker.
  rewrite <- lwhisker_vcomp.
  rewrite vassocl, vassoc4.
  rewrite runitor_triangle.
  rewrite 2 ! vassocl, vassoc4.
  rewrite vcomp_runitor.
  rewrite <- vassoc4, 2 ! vassocl, vassoc4.
  rewrite rinvunitor_triangle.
  rewrite vassocl, vassoc4.
  rewrite rinvunitor_runitor, id2_right.

  (* RHS *)
  rewrite <- rwhisker_vcomp.
  rewrite vassocl.
  apply maponpaths.
  rewrite <- rwhisker_vcomp.
  rewrite <- vassoc4.
  rewrite vassocl, vassocr, vassoc4.
  rewrite lunitor_triangle.
  rewrite <- vassoc4.
  rewrite vcomp_lunitor.
  rewrite vassoc4.
  rewrite <- lunitor_triangle.
  rewrite vassoc4.
  rewrite rassociator_lassociator, id2_right.
  rewrite rwhisker_vcomp.
  rewrite linvunitor_lunitor, id2_rwhisker, id2_left.
  apply maponpaths.
  use inv_cell_eq; is_iso.
  refine (!_).
  apply runitor_rwhisker.
Qed.

Definition vcomp_runitor_modification
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : invertible_modification
      (comp_pstrans (η ▻ id_psfunctor C) (runitor_pstrans G))
      (comp_pstrans (runitor_pstrans F) η)
  := make_invertible_modification (vcomp_runitor_modification_data η)
       (vcomp_runitor_modification_is_modification η).


Definition vcomp_lunitor_modification
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : invertible_modification
      (comp_pstrans (id_psfunctor D ◅ η) (lunitor_pstrans G))
      (comp_pstrans (lunitor_pstrans F) η).
Proof.
  use make_invertible_modification.
  - intro X; cbn.
    use make_invertible_2cell.
    + exact (runitor (η X) • linvunitor (η X)).
    + is_iso.
  - intros X Y f; cbn.
    rewrite id2_left, id2_right.
    exact (vcomp_runitor_modification_is_modification η X Y f).
Defined.


Definition vcomp_rinvunitor_modification
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : invertible_modification
      (comp_pstrans (rinvunitor_pstrans F) (η ▻ id_psfunctor C))
      (comp_pstrans η (rinvunitor_pstrans G)).
Proof.
  use make_invertible_modification.
  - intro X.
    exact (comp_of_invertible_2cell (lunitor_invertible_2cell _)
            (rinvunitor_invertible_2cell _)).
  - intros X Y f; cbn.
    use vcomp_move_L_pM; is_iso.
    rewrite vassocr.
    use vcomp_move_R_Mp; is_iso.
    exact (!vcomp_runitor_modification_is_modification η X Y f).
Defined.


Definition vcomp_linvunitor_modification
           {C D : bicat}
           {F G : psfunctor C D}
           (η : pstrans F G)
  : invertible_modification
      (comp_pstrans (linvunitor_pstrans F) (id_psfunctor D ◅ η))
      (comp_pstrans η (linvunitor_pstrans G)).
Proof.
  use make_invertible_modification.
  - intro X.
    exact (comp_of_invertible_2cell (lunitor_invertible_2cell _)
            (rinvunitor_invertible_2cell _)).
  - intros X Y f; cbn.
    rewrite id2_left, id2_right.
    exact (modnaturality_of (cell_from_invertible_2cell (vcomp_rinvunitor_modification η)) X Y f).
Defined.


Definition lunitor_pstrans_triangle_data
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : invertible_modification_data
      (comp_pstrans (lassociator_pstrans F G (id_psfunctor D)) (lunitor_pstrans G ▻ F))
      (lunitor_pstrans (comp_psfunctor G F))
  := (λ X, lunitor_invertible_2cell _).

Definition lunitor_pstrans_triangle_is_modification
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : is_modification (lunitor_pstrans_triangle_data F G).
Proof.
  intros X Y f; cbn.
  rewrite <- lwhisker_vcomp.
  rewrite vassocr.
  rewrite lunitor_lwhisker.
  rewrite vassocl.
  rewrite lunitor_lwhisker.
  rewrite <- rwhisker_vcomp.
  rewrite vassocr.
  rewrite vassocl.
  rewrite rwhisker_vcomp.
  rewrite rinvunitor_runitor, id2_rwhisker, id2_right.
  rewrite vassocl.
  rewrite lunitor_triangle.
  rewrite vassocl.
  rewrite vcomp_lunitor.
  rewrite lunitor_runitor_identity.
  reflexivity.
Qed.

Definition lunitor_pstrans_triangle
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : invertible_modification
      (comp_pstrans (lassociator_pstrans F G (id_psfunctor D)) (lunitor_pstrans G ▻ F))
      (lunitor_pstrans (comp_psfunctor G F))
  := make_invertible_modification (lunitor_pstrans_triangle_data F G)
       (lunitor_pstrans_triangle_is_modification F G).


Definition runitor_pstrans_triangle_data
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : invertible_modification_data
      (comp_pstrans (rassociator_pstrans (id_psfunctor B) F G) (G ◅ runitor_pstrans F))
      (runitor_pstrans (comp_psfunctor G F))
  := (λ X, comp_of_invertible_2cell (lunitor_invertible_2cell _)
             (inv_of_invertible_2cell (psfunctor_id G (F X)))).

Definition runitor_pstrans_triangle_is_modification
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : is_modification (runitor_pstrans_triangle_data F G).
Proof.
  intros X Y f; cbn.
  rewrite <- lwhisker_vcomp with (x := lunitor _).
  rewrite vassocl, vassoc4.
  rewrite lunitor_lwhisker.
  rewrite vassocl with (z := rwhisker _ _).
  rewrite rwhisker_vcomp.
  rewrite vassocl with (y := rinvunitor _).
  rewrite rinvunitor_runitor, id2_right.
  rewrite vassocl with (z := rwhisker _ _).
  rewrite lunitor_triangle.
  rewrite <- lwhisker_vcomp.
  rewrite <- vassoc4.
  rewrite vcomp_lunitor.

  rewrite vassoc4, vassocl.
  rewrite vassocr with (z := rinvunitor _).
  use vcomp_move_L_Mp.
  { apply is_invertible_2cell_rinvunitor. }
  simpl.
  rewrite vassocl.
  rewrite <- psfunctor_F_runitor with (f := # F f).

  rewrite vcomp_lunitor.
  rewrite <- vassoc4.
  rewrite vassocl.
  rewrite <- psfunctor_vcomp.
  rewrite vassocl.
  rewrite rinvunitor_runitor, id2_right.

  rewrite vassocr.
  rewrite <- lunitor_triangle.
  rewrite <- vassoc4, vassocr.
  rewrite rassociator_lassociator, id2_left.

  rewrite psfunctor_F_lunitor.
  rewrite vassocl, vassoc4.
  rewrite vcomp_rinv, id2_right.
  rewrite vassocr.
  rewrite rwhisker_vcomp.
  reflexivity.
Qed.

Definition runitor_pstrans_triangle
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : invertible_modification
      (comp_pstrans (rassociator_pstrans (id_psfunctor B) F G) (G ◅ runitor_pstrans F))
      (runitor_pstrans (comp_psfunctor G F))
  := make_invertible_modification (runitor_pstrans_triangle_data F G)
       (runitor_pstrans_triangle_is_modification F G).


Definition left_unit_pstrans_assoc
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : invertible_modification (G ◅ runitor_pstrans F)
      (lassociator_pstrans (id_psfunctor B) F G · runitor_pstrans (comp_psfunctor G F))
  := comp_of_invertible_2cell
      (comp_of_invertible_2cell
        (comp_of_invertible_2cell
          (linvunitor_invertible_2cell _)
          (rwhisker_of_invertible_2cell (G ◅ runitor_pstrans F)
            (inv_of_invertible_2cell (lassociator_rassociator_pstrans (id_psfunctor B) F G))))
        (rassociator_invertible_2cell _ _ _))
      (lwhisker_of_invertible_2cell (lassociator_pstrans (id_psfunctor B) F G)
        (runitor_pstrans_triangle F G)).


Definition lunitor_left_whisker
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : invertible_modification
      (rassociator_pstrans F (id_psfunctor C) G · (G ◅ lunitor_pstrans F))
      (runitor_pstrans G ▻ F).
Proof.
  use make_invertible_modification.
  - intro X; cbn.
    exact (comp_of_invertible_2cell (lunitor_invertible_2cell _) (inv_of_invertible_2cell (psfunctor_id G _))).
  - intros X Y f; cbn.
    exact (runitor_pstrans_triangle_is_modification F G X Y f).
Defined.


Definition linvunitor_left_whisker_data
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : invertible_modification_data
      ((G ◅ linvunitor_pstrans F) · lassociator_pstrans F (id_psfunctor C) G)
      (rinvunitor_pstrans G ▻ F)
  := (λ X, comp_of_invertible_2cell (runitor_invertible_2cell _)
             (inv_of_invertible_2cell (psfunctor_id G (F X)))).

Definition linvunitor_left_whisker_is_modification
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : is_modification (linvunitor_left_whisker_data F G).
Proof.
  intros X Y f; cbn.
  rewrite <- lwhisker_vcomp.
  rewrite vassocr.
  rewrite lunitor_lwhisker.
  rewrite vassocl with (y := lwhisker (# G (identity (F X))) (rinvunitor (# G (# F f)))).
  rewrite rinvunitor_triangle.

  rewrite <- lwhisker_vcomp.
  rewrite vassocr.
  rewrite vassocl with (z := lwhisker (# G (# F f)) (Bicat.runitor (# G (identity (F Y))))).
  rewrite runitor_triangle.
  rewrite vassocl with (z := (Bicat.runitor (# G (# F f) · # G (identity (F Y))))).
  rewrite vcomp_runitor.
  rewrite vassocr.
  rewrite vassocl with (z := Bicat.runitor (# G (identity (F X)) · # G (# F f))).
  rewrite rinvunitor_runitor, id2_right.
  rewrite  2 ! vassocr.

  rewrite psfunctor_vcomp.
  rewrite psfunctor_rinvunitor.
  rewrite ! vassocr.
  rewrite vassocl with (y := cell_from_invertible_2cell (psfunctor_comp G (# F f) (identity (F Y)))).
  rewrite vcomp_rinv, id2_right.
  rewrite vassocl with (y := lwhisker (# G (# F f)) (psfunctor_id G (F Y))).
  rewrite lwhisker_vcomp, vcomp_rinv, lwhisker_id2, id2_right.

  rewrite psfunctor_F_lunitor.
  rewrite 2 ! vassocr.
  rewrite vassocl with (y := cell_from_invertible_2cell (psfunctor_comp G (identity (F X)) (# F f))).
  rewrite vcomp_rinv, id2_right.

  rewrite rwhisker_vcomp.
  reflexivity.
Qed.

Definition linvunitor_left_whisker
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : invertible_modification
      ((G ◅ linvunitor_pstrans F) · lassociator_pstrans F (id_psfunctor C) G)
      (rinvunitor_pstrans G ▻ F)
  := make_invertible_modification (linvunitor_left_whisker_data F G)
       (linvunitor_left_whisker_is_modification F G).


Definition runitor_right_whisker
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : invertible_modification
      (lassociator_pstrans F (id_psfunctor C) G · (runitor_pstrans G ▻ F))
      (G ◅ lunitor_pstrans F).
Proof.
  (* Postcompose by invertible modifications to make appear (lassociator_pstrans F (id_psfunctor C) G · rassociator_pstrans F (id_psfunctor C) G) on the rhs. *)
  use (comp_of_invertible_2cell _ (lunitor_invertible_2cell _)).
  use (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (lassociator_rassociator_pstrans _ _ _))).
  use (comp_of_invertible_2cell _ (inv_of_invertible_2cell (rassociator_invertible_2cell _ _ _))).

  use lwhisker_of_invertible_2cell.
  use inv_of_invertible_2cell.
  apply lunitor_left_whisker.
Defined.


Definition right_whisker_comp_pstrans
           {B C D : bicat}
           {F G H : psfunctor C D}
           (I : psfunctor B C)
           (η : pstrans F G)
           (θ : pstrans G H)
  : invertible_modification (comp_pstrans (η ▻ I) (θ ▻ I)) ((comp_pstrans η θ) ▻ I).
Proof.
  use make_invertible_modification.
  - intro X.
    exact (id2_invertible_2cell (comp_pstrans (η ▻ I) (θ ▻ I) X)).
  - abstract (
      intros X Y f; cbn;
      rewrite id2_rwhisker, lwhisker_id2, id2_left, id2_right;
      reflexivity).
Defined.

Definition id_pstrans_right_whisker
           {B C D : bicat}
           (F : psfunctor C D)
           (G : psfunctor B C)
  : invertible_modification (id_pstrans F ▻ G) (id_pstrans (comp_psfunctor F G)).
Proof.
  use make_invertible_modification.
  - intro X.
    apply id2_invertible_2cell.
  - abstract (
      intros X Y f; cbn;
      rewrite lwhisker_id2, id2_right, id2_rwhisker, id2_left;
      reflexivity).
Defined.

Definition inv_left_whisker_id_pstrans_data
           {B C D : bicat}
           (F : psfunctor C D)
           (G : psfunctor B C)
  : invertible_modification_data (id_pstrans (comp_psfunctor F G))
      (F ◅ id_pstrans G)
  := (λ X, psfunctor_id F (G X)).

Definition inv_left_whisker_id_pstrans_is_modification
           {B C D : bicat}
           (F : psfunctor C D)
           (G : psfunctor B C)
  : is_modification (inv_left_whisker_id_pstrans_data F G).
Proof.
  intros X Y f; cbn.
    refine (!_).
    rewrite psfunctor_vcomp.
    rewrite vassocr, vassoc4.
    rewrite psfunctor_F_lunitor.
    rewrite 2 ! vassoc4.
    rewrite vcomp_rinv, id2_right.
    rewrite rwhisker_vcomp.
    rewrite vcomp_rinv, id2_rwhisker, id2_left.
    rewrite psfunctor_rinvunitor.
    rewrite <- vassoc4.
    rewrite vcomp_rinv, id2_right.
    apply vassocr.
Qed.

Definition inv_left_whisker_id_pstrans
           {B C D : bicat}
           (F : psfunctor C D)
           (G : psfunctor B C)
  : invertible_modification (id_pstrans (comp_psfunctor F G)) (F ◅ id_pstrans G)
  := make_invertible_modification (inv_left_whisker_id_pstrans_data F G)
       (inv_left_whisker_id_pstrans_is_modification F G).

Definition left_whisker_id_pstrans
           {B C D : bicat}
           (F : psfunctor C D)
           (G : psfunctor B C)
  : invertible_modification (F ◅ id_pstrans G) (id_pstrans (comp_psfunctor F G))
  := inv_of_invertible_2cell (inv_left_whisker_id_pstrans F G).


Definition left_whisker_comp_pstrans_data
           {B C D : bicat}
           (F : psfunctor C D)
           {G H I : psfunctor B C}
           (η : pstrans G H)
           (θ : pstrans H I)
  : invertible_modification_data (comp_pstrans (F ◅ η) (F ◅ θ))
      (F ◅ (comp_pstrans η θ))
  := (λ X, psfunctor_comp F (η X) (θ X)).

Definition left_whisker_comp_pstrans_is_modification
           {B C D : bicat}
           (F : psfunctor C D)
           {G H I : psfunctor B C}
           (η : pstrans G H)
           (θ : pstrans H I)
  : is_modification (left_whisker_comp_pstrans_data F η θ).
Proof.
  intros X Y f; cbn.
  rewrite vassocl.
  refine (_ @ vassocl _ _ _).
  apply rhs_right_inv_cell.
  rewrite vassocl.
  refine (maponpaths _ (! psfunctor_rassociator F _ _ _) @ _).
  rewrite vassocl.
  etrans.
  { apply maponpaths.
    rewrite 2 ! vassocr.
    rewrite rwhisker_vcomp.
    refine (maponpaths (λ x, x • _) _ @ _).
    { rewrite vassocl.
      rewrite vcomp_linv, id2_right.
      rewrite <- rwhisker_vcomp.
      rewrite vassocl.
      rewrite <- psfunctor_rwhisker.
      apply idpath. }
  apply (!vassoc4 _ _ _ _). }
  rewrite vassocl.
  etrans.
  { apply maponpaths.
    rewrite 2 ! vassocr.
    rewrite <- psfunctor_lassociator.
    rewrite 2 ! vassocl.
    apply idpath. }

  rewrite vassocl, vassoc4.
  rewrite lwhisker_vcomp.

  refine (maponpaths (λ x, x • _) _ @ _).
  { rewrite vassocl, vcomp_linv, id2_right.
    rewrite <- lwhisker_vcomp.
    apply vassocr. }

  rewrite vassocl, vassoc4.
  rewrite <- psfunctor_lwhisker.
  rewrite <- vassoc4, vassocr.
  rewrite <- psfunctor_rassociator.
  rewrite ! vassocl.
  do 2 apply maponpaths.
  rewrite ! psfunctor_vcomp.
  reflexivity.
Qed.

Definition left_whisker_comp_pstrans
           {B C D : bicat}
           (F : psfunctor C D)
           {G H I : psfunctor B C}
           (η : pstrans G H)
           (θ : pstrans H I)
  : invertible_modification (comp_pstrans (F ◅ η) (F ◅ θ)) (F ◅ (comp_pstrans η θ))
  := make_invertible_modification (left_whisker_comp_pstrans_data F η θ)
       (left_whisker_comp_pstrans_is_modification F η θ).

Definition right_whisker_right_whisker_data
           {B₁ B₂ B₃ B₄ : bicat}
           (F : psfunctor B₁ B₂)
           (G : psfunctor B₂ B₃)
           {H₁ H₂ : psfunctor B₃ B₄}
           (η : pstrans H₁ H₂)
  : invertible_modification_data
      (comp_pstrans (lassociator_pstrans F G H₁) ((η ▻ G) ▻ F))
      (comp_pstrans (η ▻ comp_psfunctor G F) (lassociator_pstrans F G H₂))
  := (λ X, comp_of_invertible_2cell (lunitor_invertible_2cell _)
             (rinvunitor_invertible_2cell _)).


Definition right_whisker_right_whisker_is_modification
           {B₁ B₂ B₃ B₄ : bicat}
           (F : psfunctor B₁ B₂)
           (G : psfunctor B₂ B₃)
           {H₁ H₂ : psfunctor B₃ B₄}
           (η : pstrans H₁ H₂)
  : is_modification (right_whisker_right_whisker_data F G η).
Proof.
  intros X Y f; cbn.
  use vcomp_move_L_pM; is_iso.
  rewrite vassocr.
  use vcomp_move_R_Mp; is_iso.
  cbn.
  exact (!vcomp_runitor_modification_is_modification ((η ▻ G) ▻ F) X Y f).
Qed.

Definition right_whisker_right_whisker
           {B₁ B₂ B₃ B₄ : bicat}
           (F : psfunctor B₁ B₂)
           (G : psfunctor B₂ B₃)
           {H₁ H₂ : psfunctor B₃ B₄}
           (η : pstrans H₁ H₂)
  : invertible_modification (comp_pstrans (lassociator_pstrans F G H₁) ((η ▻ G) ▻ F))
      (comp_pstrans (η ▻ comp_psfunctor G F) (lassociator_pstrans F G H₂))
  := make_invertible_modification (right_whisker_right_whisker_data F G η)
       (right_whisker_right_whisker_is_modification F G η).

Definition right_whisker_right_whisker_rassociator
           {B₁ B₂ B₃ B₄ : bicat}
           (F : psfunctor B₁ B₂)
           (G : psfunctor B₂ B₃)
           {H₁ H₂ : psfunctor B₃ B₄}
           (η : pstrans H₁ H₂)
  : invertible_modification (comp_pstrans ((η ▻ G) ▻ F) (rassociator_pstrans F G H₂))
      (comp_pstrans (rassociator_pstrans F G H₁) (η ▻ comp_psfunctor G F)).
Proof.
  (* Precompose by invertible modifications to make (rassociator_pstrans F G H₁) appear to the left of ((η ▻ G) ▻ F). *)
  use (comp_of_invertible_2cell (linvunitor_invertible_2cell _)).
  use (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (rassociator_lassociator_pstrans F G H₁)))).
  use (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _)).

  (* Use left whiskering by (rassociator_pstrans F G H₁). *)
  use lwhisker_of_invertible_2cell.
  use (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _)).

  (* Postcompose to make (lassociator_pstrans F G H₂) appear to the right of (η ▻ comp_psfunctor G F). *)
  use (comp_of_invertible_2cell _ (runitor_invertible_2cell _)).
  use (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (lassociator_rassociator_pstrans F G H₂))).
  use (comp_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _)).
  refine (rwhisker_of_invertible_2cell _ (right_whisker_right_whisker _ _ _)).
Defined.

Definition left_whisker_left_whisker_data
           {B₁ B₂ B₃ B₄ : bicat}
           {F₁ F₂ : psfunctor B₁ B₂}
           (G : psfunctor B₂ B₃)
           (H : psfunctor B₃ B₄)
           (η : pstrans F₁ F₂)
  : invertible_modification_data (comp_pstrans (H ◅ (G ◅ η)) (lassociator_pstrans F₂ G H))
      (comp_pstrans (lassociator_pstrans F₁ G H) (comp_psfunctor H G ◅ η))
  := (λ X, comp_of_invertible_2cell (runitor_invertible_2cell _)
             (linvunitor_invertible_2cell _)).

Definition left_whisker_left_whisker_is_modification
           {B₁ B₂ B₃ B₄ : bicat}
           {F₁ F₂ : psfunctor B₁ B₂}
           (G : psfunctor B₂ B₃)
           (H : psfunctor B₃ B₄)
           (η : pstrans F₁ F₂)
  : is_modification (left_whisker_left_whisker_data G H η).
Proof.
  intros X Y f; cbn.
  refine (_ @ vcomp_runitor_modification_is_modification (H ◅ (G ◅ η)) X Y f @ _).
  { reflexivity. }
  cbn.
  apply maponpaths.
  rewrite 2 ! psfunctor_vcomp.
  rewrite 3 ! vassocr.
  reflexivity.
Qed.


Definition left_whisker_left_whisker
           {B₁ B₂ B₃ B₄ : bicat}
           {F₁ F₂ : psfunctor B₁ B₂}
           (G : psfunctor B₂ B₃)
           (H : psfunctor B₃ B₄)
           (η : pstrans F₁ F₂)
  : invertible_modification (comp_pstrans (H ◅ (G ◅ η)) (lassociator_pstrans F₂ G H))
      (comp_pstrans (lassociator_pstrans F₁ G H) (comp_psfunctor H G ◅ η))
  := make_invertible_modification (left_whisker_left_whisker_data G H η)
       (left_whisker_left_whisker_is_modification G H η).

Definition left_whisker_left_whisker_rassociator
           {B₁ B₂ B₃ B₄ : bicat}
           {F₁ F₂ : psfunctor B₁ B₂}
           (G : psfunctor B₂ B₃)
           (H : psfunctor B₃ B₄)
           (η : pstrans F₁ F₂)
  : invertible_modification (comp_pstrans (rassociator_pstrans F₁ G H) (H ◅ (G ◅ η)))
      (comp_pstrans (comp_psfunctor H G ◅ η) (rassociator_pstrans F₂ G H)).
Proof.
  use make_invertible_modification.
  - intro X.
    exact (comp_of_invertible_2cell (lunitor_invertible_2cell _)
             (rinvunitor_invertible_2cell _)).
  - intros X Y f; cbn.
    refine (_ @ modnaturality_of (cell_from_invertible_2cell (vcomp_rinvunitor_modification (H ◅ (G ◅ η)))) X Y f @ _).
    + reflexivity.
    + apply maponpaths; cbn.
      rewrite 2 ! psfunctor_vcomp.
      rewrite ! vassocr.
      reflexivity.
Defined.


Definition right_whisker_left_whisker
           {B₁ B₂ B₃ B₄ : bicat}
           (F : psfunctor B₁ B₂)
           {G₁ G₂ : psfunctor B₂ B₃}
           (H : psfunctor B₃ B₄)
           (η : pstrans G₁ G₂)
  : invertible_modification (comp_pstrans (H ◅ (η ▻ F)) (lassociator_pstrans F G₂ H))
      (comp_pstrans (lassociator_pstrans F G₁ H) ((H ◅ η) ▻ F)).
Proof.
  use make_invertible_modification.
  - intro X.
    exact (comp_of_invertible_2cell (runitor_invertible_2cell _)
             (linvunitor_invertible_2cell _)).
  - intros X Y f; cbn.
    refine (_ @ (vcomp_runitor_modification_is_modification (H ◅ (η ▻ F)) X Y f) @ _);
    reflexivity.
Defined.

Definition right_whisker_left_whisker_rassociator
           {B₁ B₂ B₃ B₄ : bicat}
           (F : psfunctor B₁ B₂)
           {G₁ G₂ : psfunctor B₂ B₃}
           (H : psfunctor B₃ B₄)
           (η : pstrans G₁ G₂)
  : invertible_modification (comp_pstrans (rassociator_pstrans F G₁ H) (H ◅ (η ▻ F)))
      (comp_pstrans ((H ◅ η) ▻ F) (rassociator_pstrans F G₂ H)).
Proof.
  use make_invertible_modification.
  - intro X.
    exact (comp_of_invertible_2cell (lunitor_invertible_2cell _)
             (rinvunitor_invertible_2cell _)).
  - intros X Y f; cbn.
    refine (_ @ modnaturality_of (cell_from_invertible_2cell (vcomp_rinvunitor_modification (H ◅ (η ▻ F)))) X Y f @ _);
    reflexivity.
Defined.

Definition rassociator_rassociator_pstrans
           {B₁ B₂ B₃ B₄ B₅ : bicat}
           (F : psfunctor B₁ B₂)
           (G : psfunctor B₂ B₃)
           (H : psfunctor B₃ B₄)
           (I : psfunctor B₄ B₅)
  : invertible_modification
      ((rassociator_pstrans G H I ▻ F) · rassociator_pstrans F (comp_psfunctor H G) I · (I ◅ rassociator_pstrans F G H))
      (rassociator_pstrans F G (comp_psfunctor I H) · rassociator_pstrans (comp_psfunctor G F) H I).
Proof.
  use make_invertible_modification.
  - intro.
    refine
      (comp_of_invertible_2cell
        (lwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (psfunctor_id I _)))
        (runitor_invertible_2cell _)).
  - red. intros X Y f. cbn.

    (* LHS *)
    rewrite psfunctor_vcomp.
    rewrite vassocr.
    rewrite psfunctor_F_lunitor.
    rewrite 2 ! vassocr.
    rewrite vcomp_rinv, id2_left.
    rewrite psfunctor_rinvunitor.
    rewrite <- vassoc4.
    rewrite vcomp_rinv, id2_right.

    rewrite vassocr.
    rewrite <- 5 ! lwhisker_vcomp.
    rewrite 4 ! vassocr.

    rewrite vassocl with (y := rassociator (# I (# H (# G (# F f)))) (identity (I (H (G (F Y)))) · identity (I (H (G (F Y))))) (# I (identity (H (G (F Y)))))).
    rewrite lwhisker_lwhisker_rassociator.
    rewrite vassocr.
    rewrite vassocl with (z := lwhisker _ ((psfunctor_id I (H (G (F Y)))) ^-1)%bicategory).
    rewrite vcomp_whisker.
    rewrite vassocr.

    rewrite vassocl with (z := lassociator (identity (I (H (G (F X)))) · identity (I (H (G (F X))))) (# I (# H (# G (# F f)))) (# I (identity (H (G (F Y)))))).
    rewrite lwhisker_lwhisker.
    rewrite vassocr.
    rewrite vassocl with (z := lwhisker (identity (I (H (G (F X)))) · identity (I (H (G (F X)))) · # I (# H (# G (# F f)))) ((psfunctor_id I (H (G (F Y)))) ^-1)%bicategory).
    rewrite lwhisker_vcomp with (f := identity (I (H (G (F X)))) · identity (I (H (G (F X)))) · # I (# H (# G (# F f)))).
    rewrite vcomp_rinv, lwhisker_id2, id2_right.

    rewrite vassocl with (y := lwhisker (identity (I (H (G (F X)))) · identity (I (H (G (F X))))) (rinvunitor (# I (# H (# G (# F f)))))).
    rewrite rinvunitor_triangle.
    rewrite vassocl with (z := lwhisker (# I (# H (# G (# F f)))) (Bicat.runitor (identity (I (H (G (F Y)))) · identity (I (H (G (F Y))))))).
    rewrite runitor_triangle.
    rewrite vassocl with (z := Bicat.runitor (# I (# H (# G (# F f))) · (identity (I (H (G (F Y)))) · identity (I (H (G (F Y))))))).
    rewrite vcomp_runitor.

    rewrite vassocr.
    rewrite vassocl with (z := Bicat.runitor (identity (I (H (G (F X)))) · identity (I (H (G (F X)))) · # I (# H (# G (# F f))))).
    rewrite rinvunitor_runitor, id2_right.

    rewrite lwhisker_hcomp with (α := Bicat.lunitor (# I (# H (# G (# F f))))).
    rewrite triangle_r.
    rewrite hcomp_identity_right.

    rewrite vassocr with (y := lassociator (identity (I (H (G (F X)))) · identity (I (H (G (F X))))) (identity (I (H (G (F X))))) (# I (# H (# G (# F f))))).
    rewrite vassocl with (z := lassociator (identity (I (H (G (F X)))) · identity (I (H (G (F X))))) (identity (I (H (G (F X))))) (# I (# H (# G (# F f))))).
    rewrite rwhisker_lwhisker.
    rewrite ! vassocr.
    rewrite rassociator_lassociator, id2_left.
    rewrite rwhisker_vcomp.
    reflexivity.
Defined.


Definition runitor_lunitor_id_psfunctor (C : bicat)
  : invertible_modification (runitor_pstrans (id_psfunctor C))
      (lunitor_pstrans (id_psfunctor C)).
Proof.
  use make_invertible_modification.
  - intro.
    apply id2_invertible_2cell.
  - abstract (
      intros X Y f; cbn;
      rewrite lwhisker_id2, id2_right, id2_rwhisker, id2_left;
      reflexivity).
Defined.

Definition linvunitor_rinvunitor_id_psfunctor (C : bicat)
  : invertible_modification (linvunitor_pstrans (id_psfunctor C))
      (rinvunitor_pstrans (id_psfunctor C)).
Proof.
  use make_invertible_modification.
  - intro.
    apply id2_invertible_2cell.
  - exact (modnaturality_of (cell_from_invertible_2cell (runitor_lunitor_id_psfunctor C))).
Defined.


Definition linvunitor_pstrans_triangle
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : invertible_modification
      (comp_pstrans (linvunitor_pstrans G ▻ F) (rassociator_pstrans F G (id_psfunctor D)))
      (linvunitor_pstrans (comp_psfunctor G F)).
Proof.
  use make_invertible_modification.
  - intro X.
    apply lunitor_invertible_2cell.
  - exact (lunitor_pstrans_triangle_is_modification F G).
Defined.


Definition rinvunitor_pstrans_triangle_data
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : invertible_modification_data
      (comp_pstrans (G ◅ rinvunitor_pstrans F) (lassociator_pstrans (id_psfunctor B) F G))
      (rinvunitor_pstrans (comp_psfunctor G F))
  := (λ X, comp_of_invertible_2cell
             (runitor_invertible_2cell _)
             (inv_of_invertible_2cell (psfunctor_id G (F X)))).

Definition rinvunitor_pstrans_triangle_is_modification
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : is_modification (rinvunitor_pstrans_triangle_data F G).
Proof.
  intros X Y f; cbn.

  (* RHS *)
  rewrite <- lwhisker_vcomp.
  rewrite vassocr.
  rewrite lunitor_lwhisker.
  rewrite <- lwhisker_vcomp.
  rewrite vassocl, vassoc4.
  rewrite runitor_triangle.
  rewrite 2 ! vassocl, vassoc4.
  rewrite vcomp_runitor.
  use vcomp_move_R_Mp; is_iso.
  rewrite vassocl, vassoc4.
  rewrite <- left_unit_assoc.
  rewrite 2 ! vassocl, vassoc4.
  rewrite lwhisker_vcomp.
  rewrite rinvunitor_runitor, lwhisker_id2, id2_right.

  (* LHS *)
  refine (!_).
  rewrite vassocl, <- rwhisker_vcomp, vassocl.
  apply maponpaths.
  apply vcomp_move_L_Vp.
  rewrite <- vassoc4.
  etrans.
  { apply maponpaths.
    rewrite vassocl.
    apply maponpaths.
    rewrite vassocr.
    refine (!_).
    apply psfunctor_rinvunitor. }
  rewrite vassocr, psfunctor_lunitor.
  rewrite ! vassocr.
  rewrite rwhisker_vcomp, vcomp_linv, id2_rwhisker, id2_left.
  rewrite psfunctor_vcomp.
  apply vassocl.
Qed.

Definition rinvunitor_pstrans_triangle
           {B C D : bicat}
           (F : psfunctor B C)
           (G : psfunctor C D)
  : invertible_modification
      (comp_pstrans (G ◅ rinvunitor_pstrans F) (lassociator_pstrans (id_psfunctor B) F G))
      (rinvunitor_pstrans (comp_psfunctor G F))
  := make_invertible_modification (rinvunitor_pstrans_triangle_data F G)
       (rinvunitor_pstrans_triangle_is_modification F G).
