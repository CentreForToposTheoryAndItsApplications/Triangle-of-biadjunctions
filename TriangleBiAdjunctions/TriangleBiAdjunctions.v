(* ******************************************************************************* *)
(** * Triangle of biadjunctions
    Gabriel Merlin
    January 2025
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
(*Require Import UniMath.CategoryTheory.Core.Isos.*)
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
(*Require Import UniMath.CategoryTheory.Equivalences.Core.*)

(*Require Import UniMath.Bicategories.All.*)
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import Bicategories.PseudoFunctors.PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Modifications.Examples.Associativity.
Require Import UniMath.Bicategories.Modifications.Examples.Unitality.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Properties.

Require Import MorePseudoTransformations.
Require Import Inverters.
Require Import InverterEquivalences.
Require Import InverterModification.
Require Import StackedInverters.
Require Import PrePostCompositionByPseudoFunctor.
Require Import AssociativityPentagonsOfPseudoTransformations.
Require Import PseudoFunctorsPreserveEquivalence.
Require Import WhiskeringUnitality.

Local Open Scope cat.
Local Open Scope bicategory.

Definition linvunitor_left_adjoint_equivalence
           {B₁ B₂ : bicat}
           (F : psfunctor B₁ B₂)
  : left_adjoint_equivalence (linvunitor_pstrans F).
Proof.
  use make_adjoint_equivalence.
  - exact (lunitor_pstrans F).
  - exact (inv_of_invertible_2cell (linvunitor_lunitor_pstrans F)).
  - exact (cell_from_invertible_2cell (lunitor_linvunitor_pstrans F)).
  - apply modification_eq.
    intro; cbn.
    rewrite 2 ! vassocl, vassoc4.
    rewrite <- lunitor_is_lunitor_lwhisker.
    rewrite <- lunitor_triangle.
    rewrite vassoc4.
    rewrite rassociator_lassociator, id2_right.
    rewrite 2 ! vassocl, vassoc4.
    rewrite rwhisker_vcomp, linvunitor_lunitor, id2_rwhisker, id2_right.
    rewrite runitor_lunitor_identity.
    apply linvunitor_lunitor.
  - apply modification_eq.
    intro; cbn.
    rewrite 2 ! vassocl, vassoc4.
    rewrite lunitor_triangle.
    rewrite lunitor_is_lunitor_lwhisker.
    rewrite 2 ! vassocl, vassoc4.
    rewrite lwhisker_vcomp, linvunitor_lunitor, lwhisker_id2, id2_right.
    rewrite lunitor_runitor_identity.
    apply rinvunitor_runitor.
  - apply property_from_invertible_2cell.
  - apply property_from_invertible_2cell.
Defined.

Definition rassociator_left_adjoint_equivalence
           {B₁ B₂ B₃ B₄ : bicat}
           (F₁ : psfunctor B₁ B₂)
           (F₂ : psfunctor B₂ B₃)
           (F₃ : psfunctor B₃ B₄)
  : left_adjoint_equivalence (rassociator_pstrans F₁ F₂ F₃).
Proof.
  use make_adjoint_equivalence.
  - exact (lassociator_pstrans F₁ F₂ F₃).
  - exact (inv_of_invertible_2cell (rassociator_lassociator_pstrans F₁ F₂ F₃)).
  - exact (cell_from_invertible_2cell (lassociator_rassociator_pstrans F₁ F₂ F₃)).
  - apply modification_eq.
    intro; cbn.
    rewrite 2 ! vassocl, vassoc4.
    rewrite lunitor_lwhisker.
    rewrite 2 ! vassocl, vassoc4.
    rewrite rwhisker_vcomp, runitor_lunitor_identity.
    rewrite linvunitor_lunitor, id2_rwhisker, id2_right.
    apply linvunitor_lunitor.
  - apply modification_eq.
    intro; cbn.
    rewrite 2 ! vassocl, vassoc4.
    rewrite lunitor_runitor_identity, runitor_rwhisker.
    rewrite 2 ! vassocl, vassoc4.
    rewrite lwhisker_vcomp.
    rewrite linvunitor_lunitor, lwhisker_id2, id2_right.
    apply rinvunitor_runitor.
  - apply property_from_invertible_2cell.
  - apply property_from_invertible_2cell.
Defined.

Definition id1_left_adjoint_equivalence
           {B' : bicat}
           (a : B')
  : left_adjoint_equivalence (identity a).
Proof.
  use (make_adjoint_equivalence (identity a)).
  - exact (identity a).
  - apply rinvunitor.
  - apply Bicat.lunitor.
  - abstract(
      rewrite 2 ! vassocl, vassoc4;
      rewrite lunitor_lwhisker;
      rewrite 2 ! vassocl, vassoc4;
      rewrite rwhisker_vcomp;
      rewrite rinvunitor_runitor, id2_rwhisker, id2_right;
      rewrite runitor_lunitor_identity;
      apply linvunitor_lunitor).
  - abstract(
      rewrite lunitor_runitor_identity;
      rewrite 2 ! vassocl, vassoc4;
      rewrite runitor_rwhisker;
      rewrite 2 ! vassocl, vassoc4;
      rewrite lwhisker_vcomp;
      rewrite lunitor_runitor_identity;
      rewrite rinvunitor_runitor, lwhisker_id2, id2_right;
      apply rinvunitor_runitor).
  - apply is_invertible_2cell_rinvunitor.
  - apply is_invertible_2cell_lunitor.
Defined.

Section TriangleOfLeftBiadjunctions.
Context {A B C : bicat}
        {L : psfunctor B A}
        (G : psfunctor B C)
        {N : psfunctor C A}
        (F : left_biadj_data L)
        (H : left_biadj_data N)
        (Γ : adjoint_equivalence (comp_psfunctor G F) (biadj_right_adjoint H)).

  Let Φ := biadj_unit F.
  Let Ψ := biadj_unit H.
  Let Y := biadj_counit H.

  Let GΦ
    : G --> comp_psfunctor (comp_psfunctor G F) L
    := rinvunitor_pstrans G · (G ◅ Φ) · lassociator_pstrans L F G.
  Let Y'
    : comp_psfunctor N (comp_psfunctor G F) --> id_psfunctor A
    := (N ◅ arrow_of_adjunction Γ) · Y.
  Let Y'L
    : comp_psfunctor (comp_psfunctor N (comp_psfunctor G F)) L --> L
    := (Y' ▻ L) · lunitor_pstrans L.
  Let Θ
    : (comp_psfunctor N G) --> L
    := (N ◅ GΦ) · lassociator_pstrans L (comp_psfunctor G F) N · Y'L.

  Let ΦFL
    : comp_psfunctor F L --> comp_psfunctor (comp_psfunctor F L) (comp_psfunctor F L)
    := linvunitor_pstrans (comp_psfunctor F L) · (Φ ▻ comp_psfunctor F L).
  Let ΦFN
    : comp_psfunctor F N --> comp_psfunctor (comp_psfunctor F L) (comp_psfunctor F N)
    := linvunitor_pstrans (comp_psfunctor F N) · (Φ ▻ comp_psfunctor F N).

  Let Ψ'
    : id_psfunctor C --> comp_psfunctor (comp_psfunctor G F) N
    := Ψ · (left_adjoint_right_adjoint Γ ▻ N).
  Let Ψ''
    : id_psfunctor C --> comp_psfunctor G (comp_psfunctor F N)
    := Ψ' · rassociator_pstrans N F G.
  Let NΨ''
    : N --> comp_psfunctor N (comp_psfunctor G (comp_psfunctor F N))
    := rinvunitor_pstrans N · (N ◅ Ψ'').
  Let FNΨ''
    : comp_psfunctor F N --> comp_psfunctor (comp_psfunctor F N) (comp_psfunctor G (comp_psfunctor F N))
    := rinvunitor_pstrans _ · (comp_psfunctor F N ◅ Ψ'').

  (* Θ' in the article.*)
  Let FΘ
    : comp_psfunctor (comp_psfunctor F N) G --> comp_psfunctor F L
    := rassociator_pstrans G N F · (F ◅ Θ).

  Let Ξ
    : comp_psfunctor F N --> comp_psfunctor (comp_psfunctor F L) (comp_psfunctor F N)
    := FNΨ'' · lassociator_pstrans (comp_psfunctor F N) G (comp_psfunctor F N)
       · (FΘ ▻ comp_psfunctor F N).

  (* Construction of a biadjunction between N and GF with unit Y' and counit Ψ'. *)
  Let GF
    : left_biadj_data N.
  Proof.
    use make_biadj_data.
    - exact (make_biadj_unit_counit (comp_psfunctor G F) Ψ' Y').
    - refine (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ _)
                (biadj_triangle_l H)).
      (* Expand N ◅ Ψ'. *)
      refine (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (left_whisker_comp_pstrans N _ _))) _).
      refine (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _) (lwhisker_of_invertible_2cell _ _)).

      (* Exchange the left and right whiskers by N. *)
      refine (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _) _).
      refine (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (right_whisker_left_whisker N N _)) _).
      refine (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _) (lwhisker_of_invertible_2cell _ _)).

      (* Factor under a common _ ▻ N. *)
      refine (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _) _).
      refine (rwhisker_of_invertible_2cell _ (comp_of_invertible_2cell (right_whisker_comp_pstrans N _ _) (invertible_modification_psfunctor N _))).

      (* Apply the left triangle law of Γ. *)
      refine (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _) _).
      refine (comp_of_invertible_2cell (rwhisker_of_invertible_2cell Y _) (lunitor_invertible_2cell Y)).
      refine (comp_of_invertible_2cell _ (left_whisker_id_pstrans N H)).
      exact (comp_of_invertible_2cell (left_whisker_comp_pstrans N _ _) (psfunctor_invertible_modification N (left_equivalence_counit_iso Γ))).

    - refine (comp_of_invertible_2cell _ (inv_of_invertible_2cell (left_equivalence_unit_iso Γ))).

      (* Expand Ψ' ▻ (comp_psfunctor G F). *)
      refine (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ _) _).
      {
        refine (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (right_whisker_comp_pstrans (comp_psfunctor G F) _ _))) _).
        exact (rassociator_invertible_2cell _ _ _).
      }

      (* Put together linvunitor_pstrans with (Ψ ▻ comp_psfunctor G F). *)
      refine (comp_of_invertible_2cell (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _) (lwhisker_of_invertible_2cell _ _)) _).
      {
        (* Exchange the left and right whiskers by GF and N. *)
        refine (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _) _).
        refine (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (right_whisker_right_whisker_rassociator (comp_psfunctor G F) N _)) _).
        refine (comp_of_invertible_2cell (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _) (lwhisker_of_invertible_2cell _ _)) _).

        {
          (* Exchange Γ and Y'. *)
          refine (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _) _).
          refine (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (pstrans_script_pstrans _ Y')) _).

          (* Modify the runitor. *)
          refine (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _) _).
          refine (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ (vcomp_runitor_modification _)) _).

          (* Expand H ◅ Y'. *)
          refine (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (left_whisker_comp_pstrans H _ _))) _).
          exact (rassociator_invertible_2cell _ _ _).
        }

        (* Put together the successive left whiskers. *)
        refine (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _) _).
        refine (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (left_whisker_left_whisker_rassociator N H _)) _).
        exact (rassociator_invertible_2cell _ _ _).
      }

      (* Exchange Ψ and Γ. *)
      refine (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _) _).
      refine (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (comp_linvunitor_right_whisker_left_whisker Ψ _)) _).
      refine (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _) (lwhisker_of_invertible_2cell _ _)).

      (* Make appear biadj_triangle_r_lhs on the right side. *)
      refine (comp_of_invertible_2cell _ (lunitor_invertible_2cell _)).
      refine (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (biadj_triangle_r H))).

      (* Apply associativity. *)
      refine (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _) _).
      do 3 refine (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ _) (lassociator_invertible_2cell _ _ _)).
      exact (lassociator_invertible_2cell _ _ _).
  Defined.


  (** Construction of the diagram with φ₁ and φ₂. *)
  (* Θ'' in the article.*)
  Let FLFΘ
    : comp_psfunctor (comp_psfunctor (comp_psfunctor F L) (comp_psfunctor F N)) G -->
      comp_psfunctor (comp_psfunctor F L) (comp_psfunctor F L)
    := rassociator_pstrans G (comp_psfunctor F N) (comp_psfunctor F L)
        · (comp_psfunctor F L ◅ FΘ).

  Let ΦFNG
    : comp_psfunctor (comp_psfunctor F N) G -->
      comp_psfunctor (comp_psfunctor F L) (comp_psfunctor (comp_psfunctor F N) G)
    := linvunitor_pstrans (comp_psfunctor (comp_psfunctor F N) G)
       · (Φ ▻ comp_psfunctor (comp_psfunctor F N) G).

  Let φ₁₁
    : invertible_modification ((ΦFN ▻ G) · FLFΘ)
        (ΦFNG · (comp_psfunctor F L ◅ FΘ))
    := comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _)
         (rwhisker_of_invertible_2cell _
            (comp_linvunitor_right_whisker_right_whisker G _ Φ)).

  Let φ₁₂
    : invertible_modification
        (ΦFNG · (comp_psfunctor F L ◅ FΘ))
        (FΘ · ΦFL)
    := (comp_linvunitor_right_whisker_left_whisker Φ _).

  (* φ₁ in the article.*)
  Let ΦFΘ
    : invertible_modification ((ΦFN ▻ G) · FLFΘ) (FΘ · ΦFL)
    := comp_of_invertible_2cell φ₁₁ φ₁₂.

  Let FLΦ
    : comp_psfunctor F L --> comp_psfunctor (comp_psfunctor F L) (comp_psfunctor F L)
    := rinvunitor_pstrans (comp_psfunctor F L) · ((comp_psfunctor F L) ◅ Φ).
  Let FNGΦ
    : comp_psfunctor (comp_psfunctor F N) G --> comp_psfunctor (comp_psfunctor (comp_psfunctor F N) G) (comp_psfunctor F L)
    := rinvunitor_pstrans _ · (comp_psfunctor (comp_psfunctor F N) G ◅ Φ).

  Let φ₂₄
    : invertible_modification (FNGΦ · (FΘ ▻ comp_psfunctor F L))
        (FΘ · FLΦ)
    := inv_of_invertible_2cell (comp_rinvunitor_left_whisker_right_whisker _ _).


  Let φ'₂₁
    : invertible_modification (((FΘ ▻ comp_psfunctor F N) ▻ G) · FLFΘ)
        (rassociator_pstrans _ _ _
        · ((comp_psfunctor (comp_psfunctor F N) G) ◅ FΘ)
        · (FΘ ▻ comp_psfunctor F L)).
  Proof.
    (* Exchange the FΘs.*)
    refine (comp_of_invertible_2cell
              (comp_of_invertible_2cell
                (comp_of_invertible_2cell _
                  (rassociator_invertible_2cell _ _ _))
                (lwhisker_of_invertible_2cell _ (pstrans_script_pstrans FΘ FΘ)))
              (lassociator_invertible_2cell _ _ _)).
    (* Factor the right whiskers. *)
    refine (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _)
              (rwhisker_of_invertible_2cell _
                (right_whisker_right_whisker_rassociator G (comp_psfunctor F N) FΘ))).
  Defined.

  Let φ₂₁
    : invertible_modification ((Ξ ▻ G) · FLFΘ)
        ((FNΨ'' · lassociator_pstrans _ _ _ ▻ G)
        · rassociator_pstrans _ _ _
        · ((comp_psfunctor (comp_psfunctor F N) G) ◅ FΘ)
        · (FΘ ▻ comp_psfunctor F L)).
  Proof.
    (* Use associativity to make appear the term of φ'₂₁ on the right side and
       apply it. *)
    refine (comp_of_invertible_2cell
              (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _))
              (rwhisker_of_invertible_2cell _
                 (lassociator_invertible_2cell _ _ _))).
    refine (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ φ'₂₁)).
    (* Eliminate FLFΘ on both sides. *)
    refine (comp_of_invertible_2cell (rwhisker_of_invertible_2cell FLFΘ _)
              (rassociator_invertible_2cell _ _ _)).
  (*(* Apply ξ. *)
    exact (comp_of_invertible_2cell (invertible_modification_psfunctor G ξ)
             (inv_of_invertible_2cell (right_whisker_comp_pstrans G FNΨ _))).*)
    (* Factor the common right whisker. *)
    exact (inv_of_invertible_2cell (right_whisker_comp_pstrans G _ _)).
  Defined.

  (* The term of φ₂₁ and the source of φ₂₄ share a common (FΘ ▻ comp_psfunctor F L),
  which can thus be factored. *)

  Let ΨG
    : G --> comp_psfunctor (comp_psfunctor H N) G
    := linvunitor_pstrans G · (Ψ ▻ G).
  Let Ψ'G
    : G --> comp_psfunctor (comp_psfunctor (comp_psfunctor G F) N) G
    := linvunitor_pstrans G · (Ψ' ▻ G).
  Let Ψ''G
    : G --> comp_psfunctor (comp_psfunctor G (comp_psfunctor F N)) G
    := linvunitor_pstrans G · (Ψ'' ▻ G).

  Let ξ₁
    : invertible_modification
        ((FNΨ'' · lassociator_pstrans _ _ _ ▻ G) · rassociator_pstrans _ _ _)
        ((comp_psfunctor F N ◅ Ψ''G · rassociator_pstrans _ _ _)
         · lassociator_pstrans _ _ _).
  Proof.
    (* Decompose the left whisker by FN and apply a pentagon. *)
    refine (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (left_whisker_comp_pstrans (comp_psfunctor F N) Ψ''G _))).
    refine (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)).
    refine (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (inverse_pentagon_5_pstrans _ _ _ _)))).

    (* Factor by the common rassociator_pstrans and
       (lassociator_pstrans _ _ _ ▻ G). *)
    refine (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ _)
              (rassociator_invertible_2cell _ _ _)).
    refine (comp_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _)).
    refine (comp_of_invertible_2cell
              (inv_of_invertible_2cell (right_whisker_comp_pstrans G _ _))
              (rwhisker_of_invertible_2cell _ _)).

    (* Reverse the left and right whiskers. *)
    exact (inv_of_invertible_2cell (right_whisker_comp_rinvunitor_left_whisker G (comp_psfunctor F N) _)).
  Defined.

  Let φ₂₂
    : invertible_modification
        ((FNΨ'' · lassociator_pstrans _ _ _ ▻ G) · rassociator_pstrans _ _ _
         · ((comp_psfunctor (comp_psfunctor F N) G) ◅ FΘ))
        ((comp_psfunctor F N ◅ Ψ''G · rassociator_pstrans _ _ _ · (G ◅ FΘ))
         · lassociator_pstrans _ _ _)
    := comp_of_invertible_2cell
        (comp_of_invertible_2cell
          (comp_of_invertible_2cell
            (comp_of_invertible_2cell
              (rwhisker_of_invertible_2cell _ ξ₁)
              (rassociator_invertible_2cell _ _ _))
            (lwhisker_of_invertible_2cell _
              (inv_of_invertible_2cell
                (left_whisker_left_whisker G (comp_psfunctor F N) _))))
          (lassociator_invertible_2cell _ _ _))
        (rwhisker_of_invertible_2cell _ (left_whisker_comp_pstrans _ _ _)).

  (* Having put almost everything under a common left whisker by FN, it only
  remains to exhibit an invertible modification from
  (Ψ''G · rassociator_pstrans _ _ _ · (G ◅ FΘ)) to (G ◅ Φ).*)

  Let φ₂₃₁
    : invertible_modification
        (Ψ''G · rassociator_pstrans _ _ _ · (G ◅ FΘ))
        (Ψ'G · rassociator_pstrans _ _ _ · rassociator_pstrans _ _ _ · (G ◅ (F ◅ Θ))).
  Proof.
    (* Expand FΘ on the left side and factor the common (G ◅ (F ◅ Θ)). *)
    refine (comp_of_invertible_2cell
              (comp_of_invertible_2cell
                 (lwhisker_of_invertible_2cell _
                    (inv_of_invertible_2cell (left_whisker_comp_pstrans G _ _)))
                 (lassociator_invertible_2cell _ _ _))
              (rwhisker_of_invertible_2cell _ _)).
    (* Apply a pentagon on the right side. *)
    refine (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)).
    refine (comp_of_invertible_2cell _
              (lwhisker_of_invertible_2cell _
                 (rassociator_rassociator_pstrans G N F G))).
    (* Eliminate the rassociator_pstrans appearing on both sides. *)
    do 2 refine (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ _) (rassociator_invertible_2cell _ _ _)).
    (* Factor the right whisker by G. *)
    refine (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ _) (lassociator_invertible_2cell _ _ _)).
    exact (inv_of_invertible_2cell (right_whisker_comp_pstrans G Ψ' _)).
  Defined.

  Let φ₂₃₂
    : invertible_modification
        (Ψ'G · rassociator_pstrans _ _ _ · rassociator_pstrans _ _ _ · (G ◅ (F ◅ Θ)))
        (Ψ'G · rassociator_pstrans _ _ _ · (comp_psfunctor G F ◅ Θ) · rassociator_pstrans _ _ _)
    := comp_of_invertible_2cell
         (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _)
            (lwhisker_of_invertible_2cell _
               (left_whisker_left_whisker_rassociator F G Θ)))
         (lassociator_invertible_2cell _ _ _).

  Let GFY'
    : comp_psfunctor (comp_psfunctor G F) (comp_psfunctor N (comp_psfunctor G F))
      --> comp_psfunctor G F
    := (comp_psfunctor G F ◅ Y') · runitor_pstrans _.

  Let φ'₂₃₃
    : invertible_modification
        (rassociator_pstrans _ _ _ · (comp_psfunctor G F ◅ Θ))
        (((comp_psfunctor (comp_psfunctor G F) N ◅ GΦ) · lassociator_pstrans _ _ _ · (rassociator_pstrans _ _ _ · GFY' ▻ L))).
  Proof.
    (* Developp the right whisker by L and apply a pentagon. *)
    refine (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (right_whisker_comp_pstrans L _ GFY'))).
    refine (comp_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _)).
    refine (comp_of_invertible_2cell _
              (rwhisker_of_invertible_2cell _
                 (comp_of_invertible_2cell
                       (comp_of_invertible_2cell
                          (rassociator_invertible_2cell _ _ _)
                          (lwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (inverse_pentagon_7_pstrans _ _ _ _))))
                    (lassociator_invertible_2cell _ _ _)))).

    (* Permute left and right whiskers on Y'. *)
    refine (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)).
    refine (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (right_whisker_comp_runitor_left_whisker L (comp_psfunctor G F) Y'))).

    (* Factor the left whisker by GF. *)
    refine (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _))).
    refine (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)).
    refine (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (left_whisker_comp_pstrans _ _ Y'L)))).

    (* Decompose the left whisker by GFN. *)
    refine (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (left_whisker_left_whisker_rassociator N _ GΦ))).
    refine (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ _) (lassociator_invertible_2cell _ _ _)).

    (* Apply associators. *)
    refine (comp_of_invertible_2cell (psfunctor_invertible_modification _ _) (inv_of_invertible_2cell (left_whisker_comp_pstrans _ _ _))).
    exact (rassociator_invertible_2cell _ _ _).
  Defined.

  Let Ψ'GF
    : comp_psfunctor G F -->
      comp_psfunctor (comp_psfunctor (comp_psfunctor G F) N) (comp_psfunctor G F)
    := linvunitor_pstrans _ · (Ψ' ▻ comp_psfunctor G F).

  Let φ''₂₃₃
    : invertible_modification
        (Ψ'G · (comp_psfunctor (comp_psfunctor G F) N ◅ GΦ) · lassociator_pstrans _ _ _)
        (GΦ · (Ψ'GF ▻ L))
    := comp_of_invertible_2cell
         (comp_of_invertible_2cell
            (rwhisker_of_invertible_2cell _
               (comp_linvunitor_right_whisker_left_whisker Ψ' GΦ))
            (rassociator_invertible_2cell _ _ _))
         (lwhisker_of_invertible_2cell GΦ
            (inv_of_invertible_2cell
               (comp_linvunitor_right_whisker_right_whisker_alt L
                  (comp_psfunctor G F) Ψ'))).

  Let φ₂₃₃
    : invertible_modification
        (Ψ'G · rassociator_pstrans _ _ _ · (comp_psfunctor G F ◅ Θ))
        (GΦ · (Ψ'GF · rassociator_pstrans _ _ _ · GFY' ▻ L)).
  Proof.
    (* Develop the left whisker by L. *)
    refine (comp_of_invertible_2cell _
              (lwhisker_of_invertible_2cell GΦ
                 (comp_of_invertible_2cell
                    (right_whisker_comp_pstrans L Ψ'GF _)
                    (invertible_modification_psfunctor L (lassociator_invertible_2cell _ _ _))))).
    (* Apply φ''₂₃₃. *)
    refine (comp_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _)).
    refine (comp_of_invertible_2cell _
              (rwhisker_of_invertible_2cell _
                 (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _)
                    φ''₂₃₃))).
    (* Apply φ'₂₃₃. *)
    refine (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)).
    exact (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _)
             (lwhisker_of_invertible_2cell Ψ'G φ'₂₃₃)).
  Defined.

  Let φ₂₃₄
    : invertible_modification
        (GΦ · (Ψ'GF · rassociator_pstrans _ _ _ · GFY' ▻ L)) GΦ.
  Proof.
    refine (comp_of_invertible_2cell (lwhisker_of_invertible_2cell GΦ _)
              (runitor_invertible_2cell GΦ)).
    refine (comp_of_invertible_2cell (invertible_modification_psfunctor L _) (id_pstrans_right_whisker (comp_psfunctor G F) L)).

    (* Apply the right triangle law. *)
    refine (comp_of_invertible_2cell _ (biadj_triangle_r GF)).
    exact (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _) (rassociator_invertible_2cell _ _ _)).
  Defined.


  Let φ'₂₃
    : invertible_modification
        (Ψ''G · rassociator_pstrans G (comp_psfunctor F N) G · (G ◅ FΘ))
        (rinvunitor_pstrans G · (G ◅ Φ))
    := comp_of_invertible_2cell
         (comp_of_invertible_2cell
            (comp_of_invertible_2cell
               (comp_of_invertible_2cell
                  (comp_of_invertible_2cell φ₂₃₁ φ₂₃₂)
                  (rwhisker_of_invertible_2cell _ (comp_of_invertible_2cell φ₂₃₃ φ₂₃₄)))
               (rassociator_invertible_2cell _ _ _))
            (lwhisker_of_invertible_2cell _ (lassociator_rassociator_pstrans L F G)))
         (runitor_invertible_2cell _).

  Let φ₂₃
    : invertible_modification
      ((comp_psfunctor F N
        ◅ Ψ''G · rassociator_pstrans G (comp_psfunctor F N) G · (G ◅ FΘ))
       · lassociator_pstrans (comp_psfunctor F L) G (comp_psfunctor F N))
      FNGΦ
    := comp_of_invertible_2cell
         (rwhisker_of_invertible_2cell _
            (psfunctor_invertible_modification (comp_psfunctor F N) φ'₂₃))
         (left_whisker_comp_rinvunitor_left_whisker G (comp_psfunctor F N) Φ).

  Let φ₂
    : invertible_modification ((Ξ ▻ G) · FLFΘ) (FΘ · FLΦ)
    := comp_of_invertible_2cell (comp_of_invertible_2cell φ₂₁ (rwhisker_of_invertible_2cell (FΘ ▻ comp_psfunctor F L) (comp_of_invertible_2cell φ₂₂ φ₂₃))) φ₂₄.


  Section LiftingOfLeftBiadjoint.
    Context (μ : modification ΦFN Ξ)
            {M : psfunctor C B}
            {Λ : M --> comp_psfunctor F N}
            {inv_Λμ : is_invertible_2cell (lwhisker Λ μ)}
            (inverter_ump_M : has_inverter_ump
                                (make_inverter_cone M Λ inv_Λμ))
            (inverter_ump_GM
               : has_inverter_ump
                    (left_whisker_modification_inverter_cone G
                       (make_inverter_cone M Λ inv_Λμ))).

    Definition biadj_lift_left_adjoint
      : psfunctor C B
      := M.

    Let inverter_cone_M := make_inverter_cone M Λ inv_Λμ.
    Let inverter_cone_MG := right_whisker_modification_inverter_cone G inverter_cone_M.
    Let inverter_cone_GM := left_whisker_modification_inverter_cone G inverter_cone_M.

    Definition left_biadj_lift_unit
               (inv_GμΨ : is_invertible_2cell (lwhisker Ψ'' (psfunctor_modification G μ)))
      : pstrans (id_psfunctor C) (comp_psfunctor G M)
      := inverter_ump_mor inverter_ump_GM Ψ'' inv_GμΨ.

    Let inv_ΛGFΘν
        (ν : modification ΦFL FLΦ)
        (comp_ν_μG : vcomp2 (lwhisker FΘ ν) (inv_of_invertible_2cell φ₂) =
                     vcomp2 (inv_of_invertible_2cell ΦFΘ)
                        (rwhisker FLFΘ (modification_psfunctor G μ)))
      : is_invertible_2cell (lwhisker ((Λ ▻ G) · FΘ) ν)
      := inverter_cone_is_invertible_cell_morphism FΘ FLFΘ
           (inv_of_invertible_2cell ΦFΘ) (inv_of_invertible_2cell φ₂)
           comp_ν_μG inverter_cone_MG.

    Definition left_biadj_lift_counit
               {ν : modification ΦFL FLΦ}
               {inv_Φν : is_invertible_2cell (lwhisker Φ ν)}
               (inverter_ump_IdB : has_inverter_ump (make_inverter_cone (id_psfunctor B) Φ inv_Φν))
               (comp_ν_μG : vcomp2 (lwhisker FΘ ν) (inv_of_invertible_2cell φ₂) =
                            vcomp2 (inv_of_invertible_2cell ΦFΘ)
                              (rwhisker FLFΘ (modification_psfunctor G μ)))
      : comp_psfunctor M G --> id_psfunctor B
      := inverter_ump_mor inverter_ump_IdB ((Λ ▻ G) · FΘ) (inv_ΛGFΘν ν comp_ν_μG).

    Section TriangleLaws.
      Context (inv_GμΨ : is_invertible_2cell (lwhisker Ψ'' (psfunctor_modification G μ)))
              {ν : modification ΦFL FLΦ}
              {inv_Φν : is_invertible_2cell (lwhisker Φ ν)}
              (inverter_ump_IdB : has_inverter_ump
                                    (make_inverter_cone (id_psfunctor B) Φ
                                       inv_Φν))
              (comp_ν_μG : vcomp2 (lwhisker FΘ ν) (inv_of_invertible_2cell φ₂) =
                           vcomp2 (inv_of_invertible_2cell ΦFΘ)
                             (rwhisker FLFΘ (modification_psfunctor G μ)))
              (ff_GΦ : fully_faithful_1cell (G ◅ Φ))
              (ff_ΦFN : fully_faithful_1cell ΦFN).

      Let Ω := (left_biadj_lift_unit inv_GμΨ).
      Let ω : invertible_modification (Ω · (G ◅ Λ)) Ψ''
        := inverter_ump_mor_pr1 inverter_ump_GM Ψ'' inv_GμΨ.
      Let Σ := left_biadj_lift_counit inverter_ump_IdB comp_ν_μG.
      Let σ : invertible_modification (Σ · Φ) ((Λ ▻ G) · FΘ)
        := inverter_ump_mor_pr1 inverter_ump_IdB ((Λ ▻ G) · FΘ) (inv_ΛGFΘν ν comp_ν_μG).

      Definition left_biadj_lift_unit_counit_left_biadj
        : left_biadj_unit_counit M
        := make_biadj_unit_counit G Ω Σ.

      (* Right triangle law *)
      Let trl₁
        : invertible_modification
            ((biadj_triangle_r_lhs left_biadj_lift_unit_counit_left_biadj) · (rinvunitor_pstrans G · (G ◅ Φ)))
            (linvunitor_pstrans G · ((Ω ▻ G) · (rassociator_pstrans G M G · (G ◅ (Λ ▻ G) · FΘ)))).
      Proof.
        refine (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ _)))).
        { do 4 refine (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _) (lwhisker_of_invertible_2cell _ _)).
          refine (comp_of_invertible_2cell _ (lunitor_invertible_2cell (G ◅ Φ))).
          exact (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _) (rwhisker_of_invertible_2cell _ (runitor_rinvunitor_pstrans _))). }
        exact (comp_of_invertible_2cell (left_whisker_comp_pstrans G _ _) (psfunctor_invertible_modification G σ)).
      Defined.

      Let trl₂
        : invertible_modification
            ((Ω ▻ G) · (rassociator_pstrans G M G · (G ◅ (Λ ▻ G) · FΘ)))
            ((Ψ'' ▻ G) · (rassociator_pstrans G (comp_psfunctor F N) G · (G ◅ FΘ))).
      Proof.
        (* Modify Ψ₀ using ω and decompose the right whisker by G. *)
        refine (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (comp_of_invertible_2cell (right_whisker_comp_pstrans G _ _) (invertible_modification_psfunctor G ω)))).

        (* Factor by (Ω ▻ G) on both sides. *)
        refine (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ _) (lassociator_invertible_2cell _ _ _)).

        (* Exchange the left and right whiskers by G. *)
        (*unfold left_whisker_modification_inverter_cone, left_whisker_modification_inverter_pr1, inverter_cone_pr1, make_inverter_cone.
        cbn [pr1 pr2].*)
        refine (comp_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _)).
        refine (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ (right_whisker_left_whisker_rassociator _ _ _))).
        refine (comp_of_invertible_2cell (lwhisker_of_invertible_2cell _ _) (lassociator_invertible_2cell _ _ _)).

        (* Gather under a common left whisker by G. *)
        exact (inv_of_invertible_2cell (left_whisker_comp_pstrans G (Λ ▻ G) FΘ)).
      Defined.

      Let trl₃
        : invertible_modification
            (linvunitor_pstrans G · ((Ψ'' ▻ G) · (rassociator_pstrans G (comp_psfunctor F N) G · (G ◅ FΘ))))
            (Ψ''G · rassociator_pstrans G (comp_psfunctor F N) G · (G ◅ FΘ))
        := comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _)
             (lassociator_invertible_2cell _ _ _).

      (* Now, φ'₂₃ can be directly applied. *)
      Let trl
        : invertible_modification
            (biadj_triangle_r_lhs left_biadj_lift_unit_counit_left_biadj
             · (rinvunitor_pstrans G · (G ◅ Φ)))
            (rinvunitor_pstrans G · (G ◅ Φ))
        := comp_of_invertible_2cell
             (comp_of_invertible_2cell
                (comp_of_invertible_2cell trl₁
                   (lwhisker_of_invertible_2cell _ trl₂))
                trl₃) φ'₂₃.

      Definition left_biadj_lift_triangle_r_law
        : biadj_triangle_r_law left_biadj_lift_unit_counit_left_biadj.
      Proof.
        (* Make appear (rinvunitor_pstrans G) and (runitor_pstrans G) on both
           sides and then whisker by (runitor_pstrans G). *)
        refine (comp_of_invertible_2cell _ (rinvunitor_runitor_pstrans G)).
        refine (comp_of_invertible_2cell
                  (comp_of_invertible_2cell
                     (comp_of_invertible_2cell
                        (rinvunitor_invertible_2cell _)
                        (lwhisker_of_invertible_2cell _
                           (inv_of_invertible_2cell (rinvunitor_runitor_pstrans G))))
                     (lassociator_invertible_2cell _ _ _))
                  (rwhisker_of_invertible_2cell _ _)).

        (*(* Use the universal property of G. *)
        use (inverter_ump_invertible_2cell inverter_ump_G).*)
        (* Use the fully faithfulness of G ◅ Φ. *)
        refine (make_invertible_2cell (is_invertible_2cell_pseudomonic_1cell_inv_map (fully_faithful_is_pseudomonic ff_GΦ) _ (property_from_invertible_2cell _))).
        exact (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _) trl).
      Defined.

      (* Left triangle law *)
      Let ΦM
        : M --> comp_psfunctor (comp_psfunctor F L) M
        := linvunitor_pstrans M · (Φ ▻ M).

      Let ff_FLΛ_ΦM : fully_faithful_1cell (ΦM · (comp_psfunctor F L ◅ Λ)).
      Proof.
        use fully_faithful_invertible.
        - exact (Λ · ΦFN).
        - exact (inv_cell (property_from_invertible_2cell (comp_linvunitor_right_whisker_left_whisker Φ Λ))).
        - is_iso.
        - use comp_fully_faithful.
          + exact (inverter_fully_faithful _ _ inverter_ump_M).
          + exact ff_ΦFN.
      Qed.

      Let tll₁
        : invertible_modification
            (biadj_triangle_l_lhs left_biadj_lift_unit_counit_left_biadj
              · (ΦM · (comp_psfunctor F L ◅ Λ)))
            (rinvunitor_pstrans M · ((M ◅ Ω) · lassociator_pstrans M G M)
              · (((Λ ▻ G) · FΘ) ▻ M) · (comp_psfunctor F L ◅ Λ)).
      Proof.
        (* Eliminate (comp_psfunctor F L ◅ Λ) from both sides. *)
        refine (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _) (rwhisker_of_invertible_2cell _ _)).

        (* Apply associativity on the left side to eliminate common part. *)
        refine (comp_of_invertible_2cell (rwhisker_of_invertible_2cell ΦM _) _).
        {
          exact (comp_of_invertible_2cell (lwhisker_of_invertible_2cell (rinvunitor_pstrans M) (lassociator_invertible_2cell _ _ _)) (lassociator_invertible_2cell _ _ _)).
        }
        refine (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _) (lwhisker_of_invertible_2cell _ _)).

        (* Modify ((Λ ▻ G) · FΘ) by universal property. *)
        refine (comp_of_invertible_2cell _
                  (comp_of_invertible_2cell
                     (right_whisker_comp_pstrans M Σ Φ)
                     (invertible_modification_psfunctor M σ))).

        (* Eliminate (Φ ▻ M) from both sides. *)
        refine (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _) (rwhisker_of_invertible_2cell (Φ ▻ M) _)).

        (* Simplify lunitor_pstrans and linvunitor_pstrans. *)
        exact (comp_of_invertible_2cell
                 (comp_of_invertible_2cell
                    (rassociator_invertible_2cell _ _ _)
                    (lwhisker_of_invertible_2cell _ (lunitor_linvunitor_pstrans _)))
                 (runitor_invertible_2cell (Σ ▻ M))).
      Defined.

      Let tll₂
        : invertible_modification
            (rinvunitor_pstrans M · ((M ◅ Ω) · lassociator_pstrans M G M)
              · ((Λ ▻ G) · FΘ ▻ M) · (comp_psfunctor F L ◅ Λ))
            (rinvunitor_pstrans M · (M ◅ Ψ'') · lassociator_pstrans _ _ _
              · ((Λ ▻ G) · FΘ ▻ comp_psfunctor F N)).
      Proof.
        (* Exchange ((Λ ▻ G) · FΘ) and Λ, then eliminate ((Λ ▻ G) · FΘ
          ▻ comp_psfunctor F N). *)
        refine (comp_of_invertible_2cell
                  (comp_of_invertible_2cell
                     (rassociator_invertible_2cell _ _ _)
                     (lwhisker_of_invertible_2cell _ (pstrans_script_pstrans _ Λ)))
                   _).
        refine (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _) (rwhisker_of_invertible_2cell _ _)).

        (* Apply the universal property of M and decompose the left whisker by M. *)
        refine (comp_of_invertible_2cell _
                  (rwhisker_of_invertible_2cell _
                     (comp_of_invertible_2cell
                        (rassociator_invertible_2cell _ _ _)
                        (lwhisker_of_invertible_2cell _
                           (comp_of_invertible_2cell
                              (left_whisker_comp_pstrans M Ω (G ◅ Λ))
                              (psfunctor_invertible_modification M ω)))))).

        (* Gather the left whiskers by M and G in a single one. *)
        refine (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)).
        refine (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell _ (inv_of_invertible_2cell (left_whisker_left_whisker G M Λ)))).

        (* Apply associativity. *)
        exact (comp_of_invertible_2cell (rwhisker_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)) (rassociator_invertible_2cell _ _ _)).
      Defined.

      Let tll₃
        : invertible_modification
            (rinvunitor_pstrans M · (M ◅ Ψ'') · lassociator_pstrans _ _ _
              · ((Λ ▻ G) · FΘ ▻ comp_psfunctor F N))
            (Λ · FNΨ'' · lassociator_pstrans _ _ _ · (FΘ ▻ comp_psfunctor F N)).
      Proof.
        (* Eliminate (FΘ ▻ comp_psfunctor F N) from both sides. *)
        refine (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ _)).
        {
          exact (comp_of_invertible_2cell
                   (lwhisker_of_invertible_2cell _
                      (inv_of_invertible_2cell (right_whisker_comp_pstrans _ (Λ ▻ G) FΘ)))
                   (lassociator_invertible_2cell _ _ _)).
        }

        (* Gather the left whiskers by G and (comp_psfunctor F N) in a single one. *)
        refine (comp_of_invertible_2cell _ (rwhisker_of_invertible_2cell _ _)).
        {
          exact (comp_of_invertible_2cell
                  (comp_of_invertible_2cell
                     (rassociator_invertible_2cell _ _ _)
                     (lwhisker_of_invertible_2cell _
                        (right_whisker_right_whisker (comp_psfunctor F N) G Λ)))
                  (lassociator_invertible_2cell _ _ _)).
        }

        (* Exchange Λ and Ψ''. *)
        exact (inv_of_invertible_2cell (comp_rinvunitor_left_whisker_right_whisker Λ Ψ'')).
      Defined.

      Let tll₄
        : invertible_modification
            (Λ · FNΨ'' · lassociator_pstrans _ _ _ · (FΘ ▻ comp_psfunctor F N))
            (ΦM · (comp_psfunctor F L ◅ Λ)).
      Proof.
        apply inv_of_invertible_2cell.

        (* Make Ξ appear. *)
        refine (comp_of_invertible_2cell
                  (comp_of_invertible_2cell _
                     (lassociator_invertible_2cell _ _ _))
                  (rwhisker_of_invertible_2cell _
                     (lassociator_invertible_2cell _ _ _))).
        (*(* Modify using ξ. *)
        refine (comp_of_invertible_2cell
                  (comp_of_invertible_2cell
                     (comp_of_invertible_2cell _ (lwhisker_of_invertible_2cell Λ ξ))
                     (lassociator_invertible_2cell _ _ _))
                  (rwhisker_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _))).*)

        (* Modify using Λμ. *)
        refine (comp_of_invertible_2cell _ (make_invertible_2cell inv_Λμ)).

        (* Exchange Φ and Λ. *)
        exact (comp_linvunitor_right_whisker_left_whisker Φ Λ).
      Defined.

      Let tll
        : invertible_modification
            (biadj_triangle_l_lhs left_biadj_lift_unit_counit_left_biadj
              · (ΦM · (comp_psfunctor F L ◅ Λ)))
            (ΦM · (comp_psfunctor F L ◅ Λ))
        := comp_of_invertible_2cell
             (comp_of_invertible_2cell
                (comp_of_invertible_2cell tll₁ tll₂) tll₃) tll₄.

      Definition left_biadj_lift_triangle_l_law
        : biadj_triangle_l_law left_biadj_lift_unit_counit_left_biadj.
      Proof.
        (* Use full faithfulness. *)
        refine (make_invertible_2cell (is_invertible_2cell_pseudomonic_1cell_inv_map (fully_faithful_is_pseudomonic ff_FLΛ_ΦM) _ _)).
        exact (comp_of_invertible_2cell tll (linvunitor_invertible_2cell _)).
      Defined.

      Definition left_biadj_lift_data
        : left_biadj_data M
        := make_biadj_data left_biadj_lift_unit_counit_left_biadj
              left_biadj_lift_triangle_l_law
              left_biadj_lift_triangle_r_law.
    End TriangleLaws.
  End LiftingOfLeftBiadjoint.

  Definition objectwise_left_biadj_lift_data
             (μ : modification ΦFN Ξ)
             {M_on_objects : ∏ (c : C), B}
             {Λ_on_objects : ∏ (c : C), M_on_objects c --> F (N c)}
             {inv_Λμ_on_objects
                : ∏ (c : C), is_invertible_2cell (lwhisker (Λ_on_objects c) (μ c))}
             (inverter_ump_M_on_objects
                : ∏ (c : C),
                  has_inverter_ump
                    (make_inverter_cone (M_on_objects c) (Λ_on_objects c)
                    (inv_Λμ_on_objects c)))
             (G_lex : preserves_inverters G)
             (inv_GμΨ : is_invertible_2cell (lwhisker Ψ'' (psfunctor_modification G μ)))
             (ν : modification ΦFL FLΦ)
             {inv_Φν : is_invertible_2cell (lwhisker Φ ν)}
             (inverter_ump_IdB_on_objects : ∏ (b : B), has_inverter_ump (modification_inverter_cone_component_of _ (make_inverter_cone (id_psfunctor B) Φ inv_Φν) b))
             (comp_ν_μG :
                vcomp2 (lwhisker FΘ ν) (inv_of_invertible_2cell φ₂) =
                vcomp2 (inv_of_invertible_2cell ΦFΘ)
                  (rwhisker FLFΘ (modification_psfunctor G μ)))
    : left_biadj_data
        (modification_inverter_ob μ M_on_objects Λ_on_objects inv_Λμ_on_objects
           inverter_ump_M_on_objects).
  Proof.
    use left_biadj_lift_data.
    - exact μ.
    - apply modification_inverter_pr1.
    - apply modification_inverter_is_invertible_cell.
    - apply modification_inverter_ump.
    - apply left_whisker_modification_inverter_ump_from_data.
      + exact inverter_ump_M_on_objects.
      + exact G_lex.
    - exact inv_GμΨ.
    - exact ν.
    - exact inv_Φν.
    - apply modification_inverter_cone_ump_from_data.
      exact inverter_ump_IdB_on_objects.
    - exact comp_ν_μG.
    - exact (inverter_fully_faithful _ _
              (left_whisker_modification_inverter_ump_from_data G _
                 inverter_ump_IdB_on_objects G_lex)).
    - use comp_fully_faithful.
      + apply adj_equiv_fully_faithful, linvunitor_left_adjoint_equivalence.
      + exact (inverter_fully_faithful _ _
                 (right_whisker_modification_inverter_ump_from_data _ _
                    inverter_ump_IdB_on_objects)).
  Defined.
End TriangleOfLeftBiadjunctions.
