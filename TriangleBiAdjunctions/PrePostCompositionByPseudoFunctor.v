(* ******************************************************************************* *)
(** * Pre/post-composition by a pseudofunctor are pseudofunctors
    Gabriel Merlin
    January 2025
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Modifications.Modification.

Require Import MorePseudoTransformations.

Local Open Scope cat.

Section PreCompositionByPseudoFunctor.
  Context {B₁ B₂ B₃ : bicat}
          (F : psfunctor B₁ B₂).

  (* Right whiskering of pseudo-functor by a modification *)
  Definition modification_psfunctor
             {G₁ G₂ : psfunctor B₂ B₃}
             {η₁ η₂ : pstrans G₁ G₂}
             (m : modification η₁ η₂)
    : modification (η₁ ▻ F) (η₂ ▻ F).
  Proof.
    use make_modification.
    - intro X.
      exact (m (F X)).
    - intros X Y f; cbn.
      apply modnaturality_of.
  Defined.

  Lemma vcomp_modification_psfunctor
        {G₁ G₂ : psfunctor B₂ B₃}
        {η₁ η₂ η₃ : pstrans G₁ G₂}
        (m₁ : modification η₁ η₂)
        (m₂ : modification η₂ η₃)
    : modification_psfunctor (vcomp2 m₁ m₂) =
      vcomp2 (modification_psfunctor m₁) (modification_psfunctor m₂).
  Proof.
    use modification_eq.
    intro.
    reflexivity.
  Qed.

  Lemma id_pstrans_psfunctor
        {G₁ G₂ : psfunctor B₂ B₃}
        (η : pstrans G₁ G₂)
    : modification_psfunctor (id2 η) = id2 (η ▻ F).
  Proof.
    use modification_eq.
    intro.
    reflexivity.
  Qed.

  Definition pre_comp_psfunctor_data
    : psfunctor_data (psfunctor_bicat B₂ B₃) (psfunctor_bicat B₁ B₃).
  Proof.
    use make_psfunctor_data.
    - intro G; exact (comp_psfunctor G F).
    - intros G₁ G₂ η; exact (right_whisker F η).
    - intros G₁ G₂ η₁ η₂ m; exact (modification_psfunctor m).
    - intro G; exact (id2 (id_pstrans (comp_psfunctor G F))).
    - intros G₁ G₂ G₃ η₁ η₂.
      exact (cell_from_invertible_2cell (right_whisker_comp_pstrans F η₁ η₂)).
  Defined.

  Lemma pre_comp_psfunctor_is_ps
    : psfunctor_laws pre_comp_psfunctor_data.
  Proof.
    repeat split.
    - intros G₁ G₂ η.
      apply id_pstrans_psfunctor.
    - intros G₁ G₂ η₁ η₂ η₃ m n.
      apply vcomp_modification_psfunctor.
    - intros G₁ G₂ η.
      use modification_eq.
      intro; cbn.
      rewrite id2_rwhisker.
      rewrite 2 ! id2_left.
      reflexivity.
    - intros G₁ G₂ η.
      use modification_eq.
      intro; cbn.
      rewrite lwhisker_id2.
      rewrite 2 ! id2_left.
      reflexivity.
    - intros G₁ G₂ G₃ G₄ η₁ η₂ η₃.
      use modification_eq.
      intro; cbn.
      rewrite lwhisker_id2, id2_rwhisker, ! id2_right.
      apply id2_left.
    - intros G₁ G₂ G₃ η₁ η₂₁ η₂₂ m.
      use modification_eq.
      intro; cbn.
      rewrite id2_left, id2_right.
      reflexivity.
    - intros G₁ G₂ G₃ η₁ η₂₁ η₂₂ m.
      use modification_eq.
      intro; cbn.
      rewrite id2_left, id2_right.
      reflexivity.
  Qed.

  Definition pre_comp_psfunctor
    : psfunctor (psfunctor_bicat B₂ B₃) (psfunctor_bicat B₁ B₃).
  Proof.
    use make_psfunctor.
    - exact pre_comp_psfunctor_data.
    - exact pre_comp_psfunctor_is_ps.
    - split.
      + intro G.
        use make_is_invertible_modification.
        intro.
        apply is_invertible_2cell_id₂.
      + intros G₁ G₂ G₃ η₁ η₂.
        use make_is_invertible_modification.
        intro.
        apply is_invertible_2cell_id₂.
  Defined.

  (* Derived constructions. *)
  Definition is_invertible_modification_psfunctor
             {G₁ G₂ : psfunctor B₂ B₃}
             {η₁ η₂ : pstrans G₁ G₂}
             (m : invertible_modification η₁ η₂)
    : is_invertible_modification (modification_psfunctor (cell_from_invertible_2cell m))
    := psfunctor_is_iso pre_comp_psfunctor m.

  Definition invertible_modification_psfunctor
             {G₁ G₂ : psfunctor B₂ B₃}
             {η₁ η₂ : pstrans G₁ G₂}
             (m : invertible_modification η₁ η₂)
    : invertible_modification (η₁ ▻ F) (η₂ ▻ F)
    := psfunctor_inv2cell pre_comp_psfunctor m.
End PreCompositionByPseudoFunctor.


Section PostCompositionByPseudoFunctor.
  Context {B₁ B₂ B₃ : bicat}
          (G : psfunctor B₂ B₃).

  (* Application à gauche d'un pseudo-foncteur à une modification. *)
  Definition psfunctor_modification
             {F₁ F₂ : psfunctor B₁ B₂}
             {η₁ η₂ : pstrans F₁ F₂}
             (m : modification η₁ η₂)
    : modification (G ◅ η₁) (G ◅ η₂).
  Proof.
    use make_modification.
    - red.
      intro X.
      exact (psfunctor_on_cells G (m X)).
    - red.
      intros X Y f.
      cbn.
      rewrite 2 ! vassocr.
      rewrite <- psfunctor_rwhisker.
      apply rhs_right_inv_cell.
      rewrite vassocl.
      rewrite <- psfunctor_lwhisker.
      rewrite vassocr.
      rewrite vassocl with (z := cell_from_invertible_2cell (psfunctor_comp G (# F₁ f) (η₁ Y))).
      rewrite vcomp_linv, id2_right.
      rewrite vassocl.
      rewrite <- psfunctor_vcomp.
      rewrite modnaturality_of.
      rewrite psfunctor_vcomp.
      rewrite vassocr.
      reflexivity.
  Defined.

  Lemma vcomp_psfunctor_modification
        {F₁ F₂ : psfunctor B₁ B₂}
        {η₁ η₂ η₃ : pstrans F₁ F₂}
        (m₁ : modification η₁ η₂)
        (m₂ : modification η₂ η₃)
    : psfunctor_modification (vcomp2 m₁ m₂) =
      vcomp2 (psfunctor_modification m₁) (psfunctor_modification m₂).
  Proof.
    use modification_eq.
    intro.
    cbn.
    apply psfunctor_vcomp.
  Qed.

  Lemma psfunctor_id_pstrans
        {F₁ F₂ : psfunctor B₁ B₂}
        (η : pstrans F₁ F₂)
    : psfunctor_modification (id2 η) = id2 (G ◅ η).
  Proof.
    use modification_eq.
    intro; cbn.
    apply psfunctor_id2.
  Qed.


  Definition post_comp_psfunctor_data
    : psfunctor_data (psfunctor_bicat B₁ B₂) (psfunctor_bicat B₁ B₃).
  Proof.
    use make_psfunctor_data.
    - intro F; exact (comp_psfunctor G F).
    - intros F₁ F₂ η; exact (left_whisker G η).
    - intros F₁ F₂ η₁ η₂ m; exact (psfunctor_modification m).
    - intro F; exact (cell_from_invertible_2cell (inv_left_whisker_id_pstrans G F)).
    - intros F₁ F₂ F₃ η₁ η₂.
      exact (cell_from_invertible_2cell (left_whisker_comp_pstrans G η₁ η₂)).
  Defined.

  Lemma post_comp_psfunctor_is_ps
    : psfunctor_laws post_comp_psfunctor_data.
  Proof.
    repeat split.
    - intros F₁ F₂ η.
      apply psfunctor_id_pstrans.
    - intros F₁ F₂ η₁ η₂ η₃ m n.
      apply vcomp_psfunctor_modification.
    - intros F₁ F₂ η.
      use modification_eq.
      intro; cbn.
      apply psfunctor_lunitor.
    - intros F₁ F₂ η.
      use modification_eq.
      intro; cbn.
      apply psfunctor_runitor.
    - intros F₁ F₂ F₃ F₄ η₁ η₂ η₃.
      use modification_eq.
      intro; cbn.
      apply psfunctor_lassociator.
    - intros G₁ G₂ G₃ η₁ η₂₁ η₂₂ m.
      use modification_eq.
      intro; cbn.
      apply psfunctor_lwhisker.
    - intros G₁ G₂ G₃ η₁ η₂₁ η₂₂ m.
      use modification_eq.
      intro; cbn.
      apply psfunctor_rwhisker.
  Qed.

  Definition post_comp_psfunctor
    : psfunctor (psfunctor_bicat B₁ B₂) (psfunctor_bicat B₁ B₃).
  Proof.
    use make_psfunctor.
    - exact post_comp_psfunctor_data.
    - exact post_comp_psfunctor_is_ps.
    - split.
      + intro F.
        exact (property_from_invertible_2cell (inv_left_whisker_id_pstrans G F)).
      + intros F₁ F₂ F₃ η₁ η₂.
        exact (property_from_invertible_2cell (left_whisker_comp_pstrans G η₁ η₂)).
  Defined.

  (* Derived constructions. *)
  Definition is_invertible_psfunctor_modification
             {F₁ F₂ : psfunctor B₁ B₂}
             {η₁ η₂ : pstrans F₁ F₂}
             (m : invertible_modification η₁ η₂)
    : is_invertible_modification (psfunctor_modification (cell_from_invertible_2cell m))
    := psfunctor_is_iso post_comp_psfunctor m.

  Definition psfunctor_invertible_modification
             {F₁ F₂ : psfunctor B₁ B₂}
             {η₁ η₂ : pstrans F₁ F₂}
             (m : invertible_modification η₁ η₂)
    : invertible_modification (G ◅ η₁) (G ◅ η₂)
    := psfunctor_inv2cell post_comp_psfunctor m.
End PostCompositionByPseudoFunctor.
