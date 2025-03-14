(****************************************************************************

 Inverters in bicategories

 Contents
 1. Cones
 2. The universal mapping property
 3. The universal property gives an equivalence of categories
 4. Bicategories with inverters
 5. Inverters are fully faithful
 6. Pseudofunctors preversing inverters

****************************************************************************)
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.

Local Open Scope cat.

Section Inverters.
  Context {B : bicat}
          {b₁ b₂ : B}
          {f g : b₁ --> b₂}
          {α : f ==> g}.

  (**
   1. Cones
   *)
  Definition inverter_cone
    : UU
    := ∑ (i : B)
         (m : i --> b₁),
       is_invertible_2cell (m ◃ α).

  Definition make_inverter_cone
            (i : B)
            (m : i --> b₁)
            (inv_mα : is_invertible_2cell (m ◃ α))
    : inverter_cone
    := i ,, m ,, inv_mα.

  Coercion inverter_cone_ob
           (cone : inverter_cone)
    : B
    := pr1 cone.

  Definition inverter_cone_pr1
             (cone : inverter_cone)
    : cone --> b₁
    := pr12 cone.

  Definition inverter_cone_is_invertible_cell
             (cone : inverter_cone)
    : is_invertible_2cell (inverter_cone_pr1 cone ◃ α)
    := pr22 cone.

  (** Morphisms of cones *)
  Definition inverter_1cell
             (cone₁ cone₂ : inverter_cone)
    : UU
    := ∑ (k : cone₁ --> cone₂),
       invertible_2cell
         (k · inverter_cone_pr1 cone₂)
         (inverter_cone_pr1 cone₁).

  Definition make_inverter_1cell
             {cone₁ cone₂ : inverter_cone}
             (k : cone₁ --> cone₂)
             (β : invertible_2cell
                    (k · inverter_cone_pr1 cone₂)
                    (inverter_cone_pr1 cone₁))
    : inverter_1cell cone₁ cone₂
    := k ,, β.

  Coercion inverter_1cell_mor
           {cone₁ cone₂ : inverter_cone}
           (u : inverter_1cell cone₁ cone₂)
    : cone₁ --> cone₂
    := pr1 u.

  Definition inverter_1cell_pr1
             {cone₁ cone₂ : inverter_cone}
             (u : inverter_1cell cone₁ cone₂)
    : invertible_2cell
        (u · inverter_cone_pr1 cone₂)
        (inverter_cone_pr1 cone₁)
    := pr12 u.

  Definition inverter_1cell_cell
             {cone₁ cone₂ : inverter_cone}
             (u : inverter_1cell cone₁ cone₂)
    : (_ ◃ (inverter_cone_pr1 cone₂ ◃ α))
       • lassociator _ _ _
       • (inverter_1cell_pr1 u ▹ g)
       =
       lassociator _ _ _
       • (inverter_1cell_pr1 u ▹ f)
       • (inverter_cone_pr1 cone₁ ◃ α).
  Proof.
    rewrite lwhisker_lwhisker, vassocl, <- vcomp_whisker.
    apply vassocr.
  Qed.

  (**
   2. The universal mapping property
   *)
  Section UniversalMappingProperty.
    Context (cone : inverter_cone).

    Definition has_inverter_ump_1
      : UU
      := ∏ (other_cone : inverter_cone),
         inverter_1cell other_cone cone.

    Definition has_inverter_ump_2
      : UU
      := ∏ (x : B)
           (u₁ u₂ : x --> cone)
           (β : u₁ · inverter_cone_pr1 cone
                ==>
                u₂ · inverter_cone_pr1 cone),
         ∑ (ζ : u₁ ==> u₂),
         ζ ▹ inverter_cone_pr1 cone = β.

    Definition has_inverter_ump_eq
      : UU
      := ∏ (x : B)
           (u₁ u₂ : x --> cone)
           (β : u₁ · inverter_cone_pr1 cone
                ==>
                u₂ · inverter_cone_pr1 cone)
           (φ₁ φ₂ : u₁ ==> u₂)
           (q₁ : φ₁ ▹ inverter_cone_pr1 cone = β)
           (q₂ : φ₂ ▹ inverter_cone_pr1 cone = β),
         φ₁ = φ₂.

    Definition has_inverter_ump
      : UU
      := has_inverter_ump_1 × has_inverter_ump_2 × has_inverter_ump_eq.
  End UniversalMappingProperty.

  Section Projections.
    Context {cone : inverter_cone}
            (H : has_inverter_ump cone).

    Definition inverter_ump_mor
               {i : B}
               (m : i --> b₁)
               (inv_mα : is_invertible_2cell (m ◃ α))
      : i --> cone
      := pr1 H (make_inverter_cone i m inv_mα).

    Definition inverter_ump_mor_pr1
               {i : B}
               (m : i --> b₁)
               (inv_mα : is_invertible_2cell (m ◃ α))
      : invertible_2cell
          (inverter_ump_mor m inv_mα · inverter_cone_pr1 cone)
          m
      := inverter_1cell_pr1 (pr1 H (make_inverter_cone i m inv_mα)).

    Definition inverter_ump_mor_cell
               {i : B}
               (m : i --> b₁)
               (inv_mα : is_invertible_2cell (m ◃ α))
      : (_ ◃ (inverter_cone_pr1 cone ◃ α))
        • lassociator _ _ _
        • (inverter_ump_mor_pr1 m inv_mα ▹ g)
        =
        lassociator _ _ _
        • (inverter_ump_mor_pr1 m inv_mα ▹ f)
        • (m ◃ α)
      := inverter_1cell_cell (pr1 H (make_inverter_cone i m inv_mα)).

    Definition inverter_ump_cell
               {x : B}
               {u₁ u₂ : x --> cone}
               (β : u₁ · inverter_cone_pr1 cone
                    ==>
                    u₂ · inverter_cone_pr1 cone)
      : u₁ ==> u₂
      := pr1 (pr12 H x u₁ u₂ β).

    Definition inverter_ump_cell_pr1
               {x : B}
               {u₁ u₂ : x --> cone}
               (β : u₁ · inverter_cone_pr1 cone
                    ==>
                    u₂ · inverter_cone_pr1 cone)
      : inverter_ump_cell β ▹ inverter_cone_pr1 cone = β
      := pr2 (pr12 H x u₁ u₂ β).

    Definition inverter_ump_eq
               {x : B}
               {u₁ u₂ : x --> cone}
               (β : u₁ · inverter_cone_pr1 cone
                    ==>
                    u₂ · inverter_cone_pr1 cone)
               (φ₁ φ₂ : u₁ ==> u₂)
               (q₁ : φ₁ ▹ inverter_cone_pr1 cone = β)
               (q₂ : φ₂ ▹ inverter_cone_pr1 cone = β)
      : φ₁ = φ₂
      := pr22 H x u₁ u₂ β φ₁ φ₂ q₁ q₂.

    Definition inverter_ump_eq_alt
               {x : B}
               {u₁ u₂ : x --> cone}
               (φ₁ φ₂ : u₁ ==> u₂)
               (q : φ₁ ▹ inverter_cone_pr1 cone
                    =
                    φ₂ ▹ inverter_cone_pr1 cone)
      : φ₁ = φ₂.
    Proof.
      use inverter_ump_eq.
      - exact (φ₁ ▹ inverter_cone_pr1 cone).
      - apply idpath.
      - exact (!q).
    Qed.

    Definition inverter_ump_is_invertible_2cell
               {x : B}
               {u₁ u₂ : x --> cone}
               (β : u₁ · inverter_cone_pr1 cone
                    ==>
                    u₂ · inverter_cone_pr1 cone)
               (inv_β : is_invertible_2cell β)
      : is_invertible_2cell (inverter_ump_cell β).
    Proof.
      use make_is_invertible_2cell.
      - use (inverter_ump_cell (inv_β ^-1)).
      - use inverter_ump_eq_alt.
        rewrite <- rwhisker_vcomp.
        rewrite 2 ! inverter_ump_cell_pr1.
        rewrite vcomp_rinv, id2_rwhisker.
        reflexivity.
      - use inverter_ump_eq_alt.
        rewrite <- rwhisker_vcomp.
        rewrite 2 ! inverter_ump_cell_pr1.
        rewrite vcomp_linv, id2_rwhisker.
        reflexivity.
    Defined.

    Definition inverter_ump_invertible_2cell
               {x : B}
               {u₁ u₂ : x --> cone}
               (β : invertible_2cell
                      (u₁ · inverter_cone_pr1 cone)
                      (u₂ · inverter_cone_pr1 cone))
      : invertible_2cell u₁ u₂
      := make_invertible_2cell (inverter_ump_is_invertible_2cell β
                                 (property_from_invertible_2cell β)).
  End Projections.

  (**
   3. The universal property gives an equivalence of categories
   *)
  Definition universal_inverter_cat
             (x : B)
    : category.
  Proof.
    refine (full_sub_category
              (hom x b₁)
              (λ h,
               make_hProp
                 (is_invertible_2cell (h ◃ α))
                 _)).
    apply isaprop_is_invertible_2cell.
  Defined.

  Definition inverter_cone_functor_data
             (cone : inverter_cone)
             (x : B)
    : functor_data
        (hom x cone)
        (universal_inverter_cat x).
  Proof.
    use make_functor_data.
    - refine (λ h, h · inverter_cone_pr1 cone ,, _).
      use eq_is_invertible_2cell.
      + exact (rassociator _ _ _ • (h ◃ (inverter_cone_pr1 cone ◃ α)) • lassociator _ _ _).
      + abstract
          (rewrite lwhisker_lwhisker_rassociator, vassocl, rassociator_lassociator;
           apply id2_right).
      + set (cell := inverter_cone_pr1 cone ◃ α).
        is_iso.
        apply inverter_cone_is_invertible_cell.
    - exact (λ h₁ h₂ ζ, ζ ▹ _ ,, tt).
  Defined.

  Definition inverter_cone_functor_is_functor
             (cone : inverter_cone)
             (x : B)
    : is_functor (inverter_cone_functor_data cone x).
  Proof.
    split.
    - intro h; cbn.
      use subtypePath.
      {
        intro.
        apply isapropunit.
      }
      apply id2_rwhisker.
    - intros h₁ h₂ h₃ ζ₁ ζ₂ ; cbn.
      use subtypePath.
      {
        intro.
        apply isapropunit.
      }
      refine (!_).
      apply rwhisker_vcomp.
  Qed.

  Definition inverter_cone_functor
             (cone : inverter_cone)
             (x : B)
    : hom x cone ⟶ universal_inverter_cat x.
  Proof.
    use make_functor.
    - exact (inverter_cone_functor_data cone x).
    - exact (inverter_cone_functor_is_functor cone x).
  Defined.

  Definition is_universal_inverter_cone
            (cone : inverter_cone)
    : UU
    := ∏ (x : B),
       adj_equivalence_of_cats (inverter_cone_functor cone x).

  Section MakeUniversalInverterCone.
    Context (cone : inverter_cone)
            (H : has_inverter_ump cone)
            (x : B).

    Definition make_is_universal_inverter_cone_right_adjoint_data
      : functor_data
          (universal_inverter_cat x)
          (hom x cone).
    Proof.
      use make_functor_data.
      - exact (λ c, inverter_ump_mor H (pr1 c) (pr2 c)).
      - intros c₁ c₂ β.
        apply (inverter_ump_cell H).
        exact (inverter_ump_mor_pr1 H (pr1 c₁) (pr2 c₁) • (pr1 β)
               • (inverter_ump_mor_pr1 H (pr1 c₂) (pr2 c₂))^-1).
    Defined.

    Definition make_is_universal_inverter_cone_right_adjoint_is_functor
      : is_functor make_is_universal_inverter_cone_right_adjoint_data.
    Proof.
      split.
      - intro c; cbn.
        apply (inverter_ump_eq_alt H).
        rewrite inverter_ump_cell_pr1.
        rewrite id2_rwhisker.
        rewrite id2_right.
        apply vcomp_rinv.
      - intros c₁ c₂ c₃ β₁ β₂ ; cbn.
        apply (inverter_ump_eq_alt H).
        refine (!_).
        rewrite <- rwhisker_vcomp.
        rewrite 3 ! inverter_ump_cell_pr1.
        rewrite vassocl, 2 ! vassoc4.
        rewrite vcomp_linv, id2_right.
        rewrite vassocr.
        reflexivity.
    Qed.

    Definition make_is_universal_inverter_cone_right_adjoint
      : functor
          (universal_inverter_cat x)
          (hom x cone).
    Proof.
      use make_functor.
      - exact make_is_universal_inverter_cone_right_adjoint_data.
      - exact make_is_universal_inverter_cone_right_adjoint_is_functor.
    Defined.

    Definition make_is_universal_inverter_cone_unit
      : functor_identity _ ⟹
        make_is_universal_inverter_cone_right_adjoint
        ∙ inverter_cone_functor cone x.
    Proof.
      use make_nat_trans.
      - exact (λ c, (inverter_ump_mor_pr1 H (pr1 c) (pr2 c))^-1 ,, tt).
      - intros c₁ c₂ β.
        use subtypePath.
        {
          intro.
          apply isapropunit.
        }
        cbn.
        refine (!_).
        rewrite inverter_ump_cell_pr1.
        rewrite vassocl, vassocr, vcomp_linv.
        apply id2_left.
    Defined.

    Definition make_is_universal_inverter_cone_counit
      : inverter_cone_functor cone x ∙ make_is_universal_inverter_cone_right_adjoint
        ⟹ functor_identity _.
    Proof.
      use make_nat_trans.
      - intro h.
        apply (inverter_ump_cell H).
        refine (inverter_ump_mor_pr1 H _ _).
      - abstract
          (intros h₁ h₂ ζ; cbn;
          apply (inverter_ump_eq_alt H);
          refine (!_);
          rewrite <- ! rwhisker_vcomp;
          rewrite 3 ! inverter_ump_cell_pr1;
          rewrite vassocl;
          rewrite vcomp_linv, id2_right;
          reflexivity).
    Defined.

    Definition make_is_universal_inverter_cone_adjunction
      : form_adjunction
          make_is_universal_inverter_cone_right_adjoint
          (inverter_cone_functor cone x)
          make_is_universal_inverter_cone_unit
          make_is_universal_inverter_cone_counit.
    Proof.
      use make_form_adjunction.
      - intro c.
        apply (inverter_ump_eq_alt H).
        cbn.
        rewrite <- rwhisker_vcomp.
        rewrite 2 ! inverter_ump_cell_pr1.
        rewrite vcomp_rinv, id2_left.
        rewrite id2_rwhisker.
        apply vcomp_linv.
      - intro h.
        use subtypePath.
        {
          intro.
          apply isapropunit.
        }
        cbn.
        rewrite inverter_ump_cell_pr1.
        apply vcomp_linv.
    Qed.

    Definition make_is_universal_inverter_cone_adjunitiso
      : (∏ c,
         is_z_isomorphism (make_is_universal_inverter_cone_unit c)).
    Proof.
      intro c.
      refine (iso_in_precat_is_iso_in_subcat _ _ _ _ (make_z_iso' _ _)).
      apply is_inv2cell_to_is_z_iso.
      exact (is_invertible_2cell_inv (inverter_ump_mor_pr1 H (pr1 c) (pr2 c))).
    Defined.

    Definition make_is_universal_inverter_cone_adjcounitiso
      : (∏ h,
         is_z_isomorphism (make_is_universal_inverter_cone_counit h)).
    Proof.
      intro h.
      apply is_inv2cell_to_is_z_iso.
      apply inverter_ump_is_invertible_2cell.
      apply property_from_invertible_2cell.
    Defined.
  End MakeUniversalInverterCone.

  Definition make_is_universal_inverter_cone
             (cone : inverter_cone)
             (H : has_inverter_ump cone)
    : is_universal_inverter_cone cone.
  Proof.
    intro x.
    use make_adj_equivalence_of_cats'.
    - exact (make_is_universal_inverter_cone_right_adjoint _ H x).
    - exact (make_is_universal_inverter_cone_unit _ H x).
    - exact (make_is_universal_inverter_cone_counit _ H x).
    - exact (make_is_universal_inverter_cone_adjunction _ H x).
    - exact (make_is_universal_inverter_cone_adjunitiso _ H x).
    - exact (make_is_universal_inverter_cone_adjcounitiso _ H x).
  Defined.

  Section UniversalConeHasUMP.
    Context (cone : inverter_cone)
            (H : is_universal_inverter_cone cone).

    Section UMP1.
      Context (q : inverter_cone).

      Let q' : universal_inverter_cat q
        := inverter_cone_pr1 q ,, inverter_cone_is_invertible_cell q.

      Definition universal_inverter_cone_has_ump_1_mor
        : q --> cone
        := right_adjoint (H q) q'.

      Definition universal_inverter_cone_has_ump_1_pr1
        : invertible_2cell
            (universal_inverter_cone_has_ump_1_mor · inverter_cone_pr1 cone)
            (inverter_cone_pr1 q).
      Proof.
        use z_iso_to_inv2cell.
        exact (iso_from_iso_in_sub
                _ _ _ _
                (nat_z_iso_pointwise_z_iso
                   (counit_nat_z_iso_from_adj_equivalence_of_cats (H q))
                   q')).
      Defined.
    End UMP1.

    Definition universal_inverter_cone_has_ump_1
      : has_inverter_ump_1 cone.
    Proof.
      intro q.
      use make_inverter_1cell.
      - exact (universal_inverter_cone_has_ump_1_mor q).
      - exact (universal_inverter_cone_has_ump_1_pr1 q).
    Defined.

    Section UMP2.
      Context {x : B}
              {u₁ u₂ : x --> cone}
              (ζ : u₁ · inverter_cone_pr1 cone
                   ==>
                   u₂ · inverter_cone_pr1 cone).

      Definition universal_inverter_cone_has_ump_2_cell
                 : u₁ ==> u₂.
      Proof.
        apply (invmap (make_weq _ (fully_faithful_from_equivalence _ _ _ (H x) u₁ u₂))).
        simple refine (_ ,, _).
        - exact ζ.
        - exact tt.
      Defined.

      Definition universal_inverter_cone_has_ump_2_pr1
        : universal_inverter_cone_has_ump_2_cell ▹ inverter_cone_pr1 cone
          =
          ζ.
      Proof.
        exact (maponpaths
                 pr1
                 (homotweqinvweq
                    (make_weq _ (fully_faithful_from_equivalence _ _ _ (H x) u₁ u₂))
                    _)).
      Qed.
    End UMP2.

    Definition universal_inverter_cone_has_ump_2
      : has_inverter_ump_2 cone.
    Proof.
      intros x u₁ u₂ ζ.
      simple refine (_ ,, _).
      - exact (universal_inverter_cone_has_ump_2_cell ζ).
      - exact (universal_inverter_cone_has_ump_2_pr1 ζ).
    Defined.

    Definition universal_inverter_cone_has_ump_eq
      : has_inverter_ump_eq cone.
    Proof.
      intros x u₁ u₂ ζ φ₁ φ₂ p q.
      use (invmaponpathsweq
             (make_weq
                _
                (fully_faithful_from_equivalence _ _ _ (H x) u₁ u₂))) ; cbn.
      use subtypePath.
      {
        intro.
        apply isapropunit.
      }
      cbn.
      exact (p @ !q).
    Qed.

    Definition universal_inverter_cone_has_ump
      : has_inverter_ump cone
      := (universal_inverter_cone_has_ump_1 ,, universal_inverter_cone_has_ump_2 ,, universal_inverter_cone_has_ump_eq).
  End UniversalConeHasUMP.
End Inverters.

(**
 4. Bicategories with inverters
 *)
Definition has_inverters
           (B : bicat)
  : UU
  := ∏ (b₁ b₂ : B)
       (f g : b₁ --> b₂)
       (α : f ==> g),
     ∑ (i : B)
       (m : i --> b₁)
       (inv_mα : is_invertible_2cell (m ◃ α)),
     has_inverter_ump (make_inverter_cone i m inv_mα).

(**
 5. Inverters are fully faithful
 *)
Definition inverter_faithful
           {B : bicat}
           {b₁ b₂ : B}
           {f g : b₁ --> b₂}
           {α : f ==> g}
           {i : B}
           (m : i --> b₁)
           (inv_mα : is_invertible_2cell (m ◃ α))
           (H : has_inverter_ump (make_inverter_cone i m inv_mα))
  : faithful_1cell m.
Proof.
  intros x g₁ g₂ β₁ β₂ p.
  use (inverter_ump_eq_alt H).
  exact p.
Defined.

Definition inverter_fully_faithful
           {B : bicat}
           {b₁ b₂ : B}
           {f g : b₁ --> b₂}
           {α : f ==> g}
           {i : B}
           (m : i --> b₁)
           (inv_mα : is_invertible_2cell (m ◃ α))
           (H : has_inverter_ump (make_inverter_cone i m inv_mα))
  : fully_faithful_1cell m.
Proof.
  use make_fully_faithful.
  - exact (inverter_faithful m inv_mα H).
  - intros z g₁ g₂ βf.
    simple refine (_ ,, _).
    + exact (inverter_ump_cell H βf).
    + exact (inverter_ump_cell_pr1 H βf).
Defined.

Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.

(**
 6. Pseudofunctors preserving inverters
*)
Section Preserves.
  Context {B₁ B₂ : bicat}
          (F : psfunctor B₁ B₂).

  Definition psfunctor_inverter_cone
             {x y : B₁}
             {f g : x --> y}
             {α : f ==> g}
             (c : @inverter_cone _ _ _ f g α)
    : @inverter_cone _ _ _ _ _ (psfunctor_on_cells F α).
  Proof.
    use make_inverter_cone.
    - exact (F c).
    - exact (#F (inverter_cone_pr1 c)).
    - use eq_is_invertible_2cell.
      + exact (psfunctor_comp F (inverter_cone_pr1 c) f
          • (psfunctor_on_cells F ((inverter_cone_pr1 c) ◃ α))
          • (psfunctor_comp F (inverter_cone_pr1 c) g)^-1).
      + symmetry; apply vcomp_move_L_Vp.
        symmetry; apply psfunctor_lwhisker.
      + apply is_invertible_2cell_vcomp.
        { apply is_invertible_2cell_vcomp.
          { apply property_from_invertible_2cell. }
          exact (psfunctor_is_iso F (make_invertible_2cell (inverter_cone_is_invertible_cell c))).
        }
        is_iso.
  Defined.

  Definition preserves_inverters
    : UU
    := ∏ (x y : B₁)
         (f g : x --> y)
         (α : f ==> g)
         (p : @inverter_cone _ _ _ f g α),
       has_inverter_ump p
       →
       has_inverter_ump (psfunctor_inverter_cone p).
End Preserves.
