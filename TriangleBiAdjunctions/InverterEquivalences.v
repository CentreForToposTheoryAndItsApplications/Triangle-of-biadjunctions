(************************************************************************

Equivalences for inverters

************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Subcategory.FullEquivalences.
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

Local Open Scope cat.

(**

  Suppose, we have a diagram as follows


                        ---- f₁ ---->
     p₁ ---- i₁ ----> x₁     V        y₁
                        ---- g₁ ---->
                      |               |
                      |               |
                      l₁     ≃        l₂
                      |               |
                      |               |
                      V               V
                        ---- f₂ ---->
     p₂ ---- i₂ ----> x₂     V        y₂
                        ---- g₂ ---->


  where both rows are inverters cones.
  If the bottom row is an inverter, then there exists a morphism from p₁ to p₂
  and an invertible cell filling the so-formed square.

*)
Section InverterMorphism.
  Context {B : bicat}
          {x₁ y₁ x₂ y₂ : B}
          {f₁ g₁ : x₁ --> y₁}
          {α₁ : f₁ ==> g₁}
          {f₂ g₂ : x₂ --> y₂}
          {α₂ : f₂ ==> g₂}
          (lx : x₁ --> x₂)
          (ly : y₁ --> y₂)
          (γ₂ : invertible_2cell (lx · f₂) (f₁ · ly))
          (γ₃ : invertible_2cell (lx · g₂) (g₁ · ly))
          (pα : (lx ◃ α₂) • γ₃ = γ₂ • (α₁ ▹ ly)).

  Let eq_hlxα₂ {q : B} (h : hom q x₁)
    : rassociator _ _ _ • (((h ◃ γ₂) • (lassociator _ _ _ • (h ◃ α₁ ▹ ly)) • rassociator _ _ _ • (h ◃ γ₃^-1)) • lassociator _ _ _)
      = h · lx ◃ α₂.
  Proof.
    rewrite <- rwhisker_lwhisker.
    rewrite <- vassoc4.
    rewrite lassociator_rassociator, id2_right.
    rewrite 2 ! lwhisker_vcomp.
    rewrite <- pα.
    rewrite vassocl.
    rewrite vcomp_rinv, id2_right.
    rewrite lwhisker_lwhisker.
    rewrite vassocr.
    rewrite rassociator_lassociator.
    apply id2_left.
  Qed.

  Definition inverter_cone_is_invertible_cell_morphism
             (cone : @inverter_cone B _ _ _ _ α₁)
    : is_invertible_2cell (inverter_cone_pr1 cone · lx ◃ α₂).
  Proof.
    apply (eq_is_invertible_2cell (eq_hlxα₂ _)).
    set (cell := _ ◃ α₁).
    is_iso.
    { apply property_from_invertible_2cell. }
    apply inverter_cone_is_invertible_cell.
  Defined.

  Definition inverter_cone_morphism
             (cone : @inverter_cone B _ _ _ _ α₁)
    : @inverter_cone B _ _ _ _ α₂.
  Proof.
    use make_inverter_cone.
    - exact cone.
    - exact (inverter_cone_pr1 cone · lx).
    - apply inverter_cone_is_invertible_cell_morphism.
  Defined.

  Definition universal_inverter_cat_morphism (q : B)
    : functor
        (@universal_inverter_cat B _ _ _ _ α₁ q)
        (@universal_inverter_cat B _ _ _ _ α₂ q).
  Proof.
    use full_sub_category_functor.
    - exact (post_comp _ lx).
    - intro h; cbn; intro inv_hα₁.
      exact (inverter_cone_is_invertible_cell
              (inverter_cone_morphism (make_inverter_cone q h inv_hα₁))).
  Defined.

  Section MorphismToInverter.
    Context {cone : @inverter_cone B _ _ _ _ α₂}
            (H : has_inverter_ump cone).

    Definition inverter_ump_mor_morphism
               {i : B}
               (m : i --> x₁)
               (inv_mα : is_invertible_2cell (m ◃ α₁))
      : i --> cone
      := pr1 H (inverter_cone_morphism (make_inverter_cone i m inv_mα)).

    Definition inverter_ump_mor_pr1_morphism
               {i : B}
               (m : i --> x₁)
               (inv_mα : is_invertible_2cell (m ◃ α₁))
      : invertible_2cell
          (inverter_ump_mor_morphism m inv_mα · inverter_cone_pr1 cone)
          (m · lx)
      := inverter_1cell_pr1 (pr1 H (inverter_cone_morphism (make_inverter_cone i m inv_mα))).
  End MorphismToInverter.
End InverterMorphism.

(**

  Suppose, we have a diagram as follows


                        ---- f₁ ---->
     p₁ ---- i₁ ----> x₁     V        y₁
                        ---- g₁ ---->
     |                |               |
     |                |               |
     l₃      ≃        l₁     ≃        l₂
     |                |               |
     |                |               |
     V                V               V
                        ---- f₂ ---->
     p₂ ---- i₂ ----> x₂     V        y₂
                        ---- g₂ ---->


  where the columns are equivalences and both rows are inverters cones.
  If the top row is an inverter, then so is the bottom row.

*)
Section InverterEquivalence.
  Context {B : bicat}
          {p₁ x₁ y₁ p₂ x₂ y₂ : B}
          {i₁ : p₁ --> x₁}
          {f₁ g₁ : x₁ --> y₁}
          {α₁ : f₁ ==> g₁}
          {inv_i₁α₁ : is_invertible_2cell (i₁ ◃ α₁)}
          (cone₁ :=  make_inverter_cone p₁ i₁ inv_i₁α₁)
          {i₂ : p₂ --> x₂}
          {f₂ g₂ : x₂ --> y₂}
          {α₂ : f₂ ==> g₂}
          (lx : x₁ --> x₂)
          (ly : y₁ --> y₂)
          (lp : p₁ --> p₂)
          (Hlx : left_adjoint_equivalence lx)
          (Hly : left_adjoint_equivalence ly)
          (Hlp : left_adjoint_equivalence lp)
          (γ₁ : invertible_2cell (lp · i₂) (i₁ · lx))
          (γ₂ : invertible_2cell (lx · f₂) (f₁ · ly))
          (γ₃ : invertible_2cell (lx · g₂) (g₁ · ly))
          (H : has_inverter_ump cone₁)
          (pα : (lx ◃ α₂) • γ₃ = γ₂ • (α₁ ▹ ly)).

  Let rx : x₂ --> x₁
    := left_adjoint_right_adjoint Hlx.
  Let ηx : invertible_2cell (id₁ _) (lx · rx)
    := left_equivalence_unit_iso Hlx.
  Let εx : invertible_2cell (rx · lx) (id₁ _)
    := left_equivalence_counit_iso Hlx.

  Let ry : y₂ --> y₁
    := left_adjoint_right_adjoint Hly.
  Let ηy : invertible_2cell (id₁ _) (ly · ry)
    := left_equivalence_unit_iso Hly.
  Let εy : invertible_2cell (ry · ly) (id₁ _)
    := left_equivalence_counit_iso Hly.

  Let rp : p₂ --> p₁
    := left_adjoint_right_adjoint Hlp.
  Let ηp : invertible_2cell (id₁ _) (lp · rp)
    := left_equivalence_unit_iso Hlp.
  Let εp : invertible_2cell (rp · lp) (id₁ _)
    := left_equivalence_counit_iso Hlp.

  (*Let γ₁' : invertible_2cell (rp · i₁) (i₂ · rx)
    := comp_of_invertible_2cell
         (rinvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (lwhisker_of_invertible_2cell
               _
               ηx)
            (comp_of_invertible_2cell
               (lassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell
                     _
                     (rassociator_invertible_2cell _ _ _))
                  (comp_of_invertible_2cell
                     (rwhisker_of_invertible_2cell
                        _
                        (lwhisker_of_invertible_2cell
                           _
                           (inv_of_invertible_2cell γ₁)))
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           (lassociator_invertible_2cell _ _ _))
                        (comp_of_invertible_2cell
                           (rwhisker_of_invertible_2cell
                              _
                              (rwhisker_of_invertible_2cell
                                 _
                                 εp))
                           (rwhisker_of_invertible_2cell
                              _
                              (lunitor_invertible_2cell _)))))))).*)

  Let γ₂' : invertible_2cell (rx · f₁) (f₂ · ry)
    := comp_of_invertible_2cell
         (rinvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (lwhisker_of_invertible_2cell
               _
               ηy)
            (comp_of_invertible_2cell
               (lassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell
                     _
                     (rassociator_invertible_2cell _ _ _))
                  (comp_of_invertible_2cell
                     (rwhisker_of_invertible_2cell
                        _
                        (lwhisker_of_invertible_2cell
                           _
                           (inv_of_invertible_2cell γ₂)))
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           (lassociator_invertible_2cell _ _ _))
                        (comp_of_invertible_2cell
                           (rwhisker_of_invertible_2cell
                              _
                              (rwhisker_of_invertible_2cell
                                 _
                                 εx))
                           (rwhisker_of_invertible_2cell
                              _
                              (lunitor_invertible_2cell _)))))))).

  Let γ₃' : invertible_2cell (rx · g₁) (g₂ · ry)
    := comp_of_invertible_2cell
         (rinvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (lwhisker_of_invertible_2cell
               _
               ηy)
            (comp_of_invertible_2cell
               (lassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell
                     _
                     (rassociator_invertible_2cell _ _ _))
                  (comp_of_invertible_2cell
                     (rwhisker_of_invertible_2cell
                        _
                        (lwhisker_of_invertible_2cell
                           _
                           (inv_of_invertible_2cell γ₃)))
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           (lassociator_invertible_2cell _ _ _))
                        (comp_of_invertible_2cell
                           (rwhisker_of_invertible_2cell
                              _
                              (rwhisker_of_invertible_2cell
                                 _
                                 εx))
                           (rwhisker_of_invertible_2cell
                              _
                              (lunitor_invertible_2cell _)))))))).

  Let pα_inv : (α₁ ▹ ly) • γ₃^-1 = γ₂^-1 • (lx ◃ α₂) .
  Proof.
    use vcomp_move_L_pV.
    rewrite vassocr.
    refine (!_).
    use vcomp_move_L_Vp.
    exact pα.
  Qed.

  Let pα' : (rx ◃ α₁) • γ₃' = γ₂' • (α₂ ▹ ry).
  Proof.
    cbn.
    rewrite vassoc4.
    rewrite whisker_r_natural.
    rewrite <- vassoc4.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite vassocr.
      rewrite <- rwhisker_rwhisker.
      rewrite vassocl.
      apply maponpaths.
      rewrite ! rwhisker_vcomp.
      apply maponpaths.
      rewrite vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite vassocl.
      apply maponpaths.
      rewrite vassocr, lwhisker_vcomp.
      rewrite pα_inv.
      rewrite <- lwhisker_vcomp, vassocl.
      apply maponpaths.
      rewrite vassocr.
      rewrite lwhisker_lwhisker.
      rewrite vassocl.
      apply maponpaths.
      rewrite vassocr.
      rewrite <- vcomp_whisker.
      rewrite vassocl.
      apply maponpaths.
      apply vcomp_lunitor.
    }
    rewrite ! vassocl.
    rewrite ! rwhisker_vcomp.
    reflexivity.
  Qed.

  (*Let eq_α₁
    : α₁ =
      (rinvunitor f₁ • (f₁ ◃ ηy) • lassociator _ _ _)
      • (((γ₂^-1 • (lx ◃ α₂ • γ₃)) ▹ ry)
         • (rassociator _ _ _ • (g₁ ◃ ηy^-1) • runitor g₁)).
  Proof.
    use vcomp_move_L_pM; is_iso.
    { apply property_from_invertible_2cell. }
    rewrite pα.
    rewrite ! vassocr.
    rewrite vcomp_linv, id2_left.
    rewrite rwhisker_rwhisker_alt.
    rewrite 2 ! vassocl, vassoc4.
    rewrite vcomp_whisker.
    rewrite <- vassoc4.
    rewrite vcomp_runitor.
    rewrite vassoc4.
    reflexivity.
  Qed.*)

  Definition universal_inverter_cat_left_equivalence
             (q : B)
    : adj_equiv
        (@universal_inverter_cat B _ _ _ _ α₁ q)
        (@universal_inverter_cat B _ _ _ _ α₂ q).
  Proof.
    use tpair.
    - exact (universal_inverter_cat_morphism lx ly γ₂ γ₃ pα q).
    - use full_sub_category_adj_equivalence.
      + apply left_adjequiv_to_left_adjequiv_repr.
        exact Hlx.
      + intro h; cbn; intro inv_hα₂.
        exact (inverter_cone_is_invertible_cell
                (inverter_cone_morphism rx ry γ₂' γ₃' pα'
                  (make_inverter_cone q h inv_hα₂))).
  Defined.

  Let eq_i₂α₂
    : (linvunitor i₂ • (εp^-1 ▹ i₂) • rassociator _ _ _ • (rp ◃ γ₁) ▹ f₂)
      • rassociator _ _ _
      • ((rp ◃ (i₁ · lx ◃ α₂)) • lassociator _ _ _)
      • ((rp ◃ γ₁^-1) • (lassociator _ _ _ • ((εp ▹ i₂) • lunitor i₂)) ▹ g₂)
      = i₂ ◃ α₂.
  Proof.
    rewrite lwhisker_lwhisker.
    rewrite <- vassoc4.
    rewrite <- vcomp_whisker.
    rewrite vassocl, vassoc4.
    rewrite rassociator_lassociator, id2_right.
    rewrite vassocr.
    rewrite rwhisker_vcomp.
    rewrite vassocl, vassoc4.
    rewrite lwhisker_vcomp.
    rewrite vcomp_rinv, lwhisker_id2, id2_right.
    rewrite vassocl, vassoc4.
    rewrite rassociator_lassociator, id2_right.
    rewrite vassocl, vassoc4.
    rewrite rwhisker_vcomp.
    rewrite vcomp_linv, id2_rwhisker, id2_right.
    rewrite linvunitor_lunitor, id2_rwhisker.
    apply id2_left.
  Qed.

  Definition inverter_cone_is_invertible_cell_left_adjoint_equivalence
    : is_invertible_2cell (i₂ ◃ α₂).
  Proof.
    apply (eq_is_invertible_2cell eq_i₂α₂).
    set (i₁lxα₂ := i₁ · lx ◃ α₂).
    is_iso; try (apply property_from_invertible_2cell).
    exact (inverter_cone_is_invertible_cell_morphism lx ly γ₂ γ₃ pα cone₁).
  Defined.

  Definition inverter_cone_left_adjoint_equivalence
    := make_inverter_cone p₂ i₂
         inverter_cone_is_invertible_cell_left_adjoint_equivalence.

  Let inverter_cone_functor_comm
      (q : B)
    : nat_trans
        (post_comp q rp ∙ inverter_cone_functor cone₁ q ∙ universal_inverter_cat_left_equivalence q)
        (inverter_cone_functor inverter_cone_left_adjoint_equivalence q).
  Proof.
    use make_nat_trans.
    - intro h.
      refine (rassociator _ _ _ • rassociator _ _ _ • (h ◃ _) ,, tt).
      exact ((rp ◃ γ₁^-1) • lassociator _ _ _ • (εp ▹ i₂) • lunitor _).
    - intros h₁ h₂ ζ.
      use subtypePath.
      {
        intro.
        apply isapropunit.
      }
      abstract(
        cbn;
        rewrite 2! vassocl;
        rewrite vassocr;
        rewrite rwhisker_rwhisker_alt;
        rewrite vassocl, vassoc4;
        rewrite rwhisker_rwhisker_alt;
        rewrite <- vassoc4;
        rewrite vcomp_whisker;
        rewrite 2 ! vassocr;
        reflexivity).
  Defined.

  Let inverter_cone_functor_comm_iso
      (q : B)
    : is_nat_z_iso (inverter_cone_functor_comm q).
  Proof.
    intro h; cbn.
    refine (iso_in_precat_is_iso_in_subcat _ _ _ _ (make_z_iso' _ _)).
    apply is_inv2cell_to_is_z_iso.
    apply is_invertible_2cell_vcomp; is_iso.
    exact (left_equivalence_counit_iso Hlp).
  Defined.

  Definition is_universal_inverter_cone_left_adjoint_equivalence
    : is_universal_inverter_cone inverter_cone_left_adjoint_equivalence.
  Proof.
    intro q.
    apply (nat_iso_adj_equivalence_of_cats (inverter_cone_functor_comm q) (inverter_cone_functor_comm_iso q)).
    apply comp_adj_equivalence_of_cats.
    - apply comp_adj_equivalence_of_cats.
      + apply left_adjequiv_to_left_adjequiv_repr.
        exact (inv_left_adjoint_equivalence Hlp).
      + apply (make_is_universal_inverter_cone _ H).
    - apply adj_equiv_of_cats_from_adj.
  Defined.

  Definition has_inverter_ump_left_adjoint_equivalence
    : has_inverter_ump inverter_cone_left_adjoint_equivalence
    := universal_inverter_cone_has_ump _
         is_universal_inverter_cone_left_adjoint_equivalence.
End InverterEquivalence.

(**
 Same as above but when the bottom row is an inverter.
*)
Section InverterInverseEquivalence.
  Context {B : bicat}
          {p₁ x₁ y₁ p₂ x₂ y₂ : B}
          {i₁ : p₁ --> x₁}
          {f₁ g₁ : x₁ --> y₁}
          {α₁ : f₁ ==> g₁}
          {i₂ : p₂ --> x₂}
          {f₂ g₂ : x₂ --> y₂}
          {α₂ : f₂ ==> g₂}
          {inv_i₂α₂ : is_invertible_2cell (i₂ ◃ α₂)}
          (cone₂ :=  make_inverter_cone p₂ i₂ inv_i₂α₂)
          (lx : x₁ --> x₂)
          (ly : y₁ --> y₂)
          (lp : p₁ --> p₂)
          (Hlx : left_adjoint_equivalence lx)
          (Hly : left_adjoint_equivalence ly)
          (Hlp : left_adjoint_equivalence lp)
          (γ₁ : invertible_2cell (lp · i₂) (i₁ · lx))
          (γ₂ : invertible_2cell (lx · f₂) (f₁ · ly))
          (γ₃ : invertible_2cell (lx · g₂) (g₁ · ly))
          (H : has_inverter_ump cone₂)
          (pα : (lx ◃ α₂) • γ₃ = γ₂ • (α₁ ▹ ly)).

  Let rx : x₂ --> x₁
    := left_adjoint_right_adjoint Hlx.
  Let ηx : invertible_2cell (id₁ _) (lx · rx)
    := left_equivalence_unit_iso Hlx.
  Let εx : invertible_2cell (rx · lx) (id₁ _)
    := left_equivalence_counit_iso Hlx.

  Let ry : y₂ --> y₁
    := left_adjoint_right_adjoint Hly.
  Let ηy : invertible_2cell (id₁ _) (ly · ry)
    := left_equivalence_unit_iso Hly.
  Let εy : invertible_2cell (ry · ly) (id₁ _)
    := left_equivalence_counit_iso Hly.

  Let rp : p₂ --> p₁
    := left_adjoint_right_adjoint Hlp.
  Let ηp : invertible_2cell (id₁ _) (lp · rp)
    := left_equivalence_unit_iso Hlp.
  Let εp : invertible_2cell (rp · lp) (id₁ _)
    := left_equivalence_counit_iso Hlp.

  Let γ₁' : invertible_2cell (rp · i₁) (i₂ · rx)
    := comp_of_invertible_2cell
         (rinvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (lwhisker_of_invertible_2cell
               _
               ηx)
            (comp_of_invertible_2cell
               (lassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell
                     _
                     (rassociator_invertible_2cell _ _ _))
                  (comp_of_invertible_2cell
                     (rwhisker_of_invertible_2cell
                        _
                        (lwhisker_of_invertible_2cell
                           _
                           (inv_of_invertible_2cell γ₁)))
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           (lassociator_invertible_2cell _ _ _))
                        (comp_of_invertible_2cell
                           (rwhisker_of_invertible_2cell
                              _
                              (rwhisker_of_invertible_2cell
                                 _
                                 εp))
                           (rwhisker_of_invertible_2cell
                              _
                              (lunitor_invertible_2cell _)))))))).

  Let γ₂' : invertible_2cell (rx · f₁) (f₂ · ry)
    := comp_of_invertible_2cell
         (rinvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (lwhisker_of_invertible_2cell
               _
               ηy)
            (comp_of_invertible_2cell
               (lassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell
                     _
                     (rassociator_invertible_2cell _ _ _))
                  (comp_of_invertible_2cell
                     (rwhisker_of_invertible_2cell
                        _
                        (lwhisker_of_invertible_2cell
                           _
                           (inv_of_invertible_2cell γ₂)))
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           (lassociator_invertible_2cell _ _ _))
                        (comp_of_invertible_2cell
                           (rwhisker_of_invertible_2cell
                              _
                              (rwhisker_of_invertible_2cell
                                 _
                                 εx))
                           (rwhisker_of_invertible_2cell
                              _
                              (lunitor_invertible_2cell _)))))))).

  Let γ₃' : invertible_2cell (rx · g₁) (g₂ · ry)
    := comp_of_invertible_2cell
         (rinvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (lwhisker_of_invertible_2cell
               _
               ηy)
            (comp_of_invertible_2cell
               (lassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell
                     _
                     (rassociator_invertible_2cell _ _ _))
                  (comp_of_invertible_2cell
                     (rwhisker_of_invertible_2cell
                        _
                        (lwhisker_of_invertible_2cell
                           _
                           (inv_of_invertible_2cell γ₃)))
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           (lassociator_invertible_2cell _ _ _))
                        (comp_of_invertible_2cell
                           (rwhisker_of_invertible_2cell
                              _
                              (rwhisker_of_invertible_2cell
                                 _
                                 εx))
                           (rwhisker_of_invertible_2cell
                              _
                              (lunitor_invertible_2cell _)))))))).

  Let pα_inv : (α₁ ▹ ly) • γ₃^-1 = γ₂^-1 • (lx ◃ α₂) .
  Proof.
    use vcomp_move_L_pV.
    rewrite vassocr.
    refine (!_).
    use vcomp_move_L_Vp.
    exact pα.
  Qed.

  Let pα' : (rx ◃ α₁) • γ₃' = γ₂' • (α₂ ▹ ry).
  Proof.
    cbn.
    rewrite vassoc4.
    rewrite whisker_r_natural.
    rewrite <- vassoc4.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite vassocr.
      rewrite <- rwhisker_rwhisker.
      rewrite vassocl.
      apply maponpaths.
      rewrite ! rwhisker_vcomp.
      apply maponpaths.
      rewrite vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite vassocl.
      apply maponpaths.
      rewrite vassocr, lwhisker_vcomp.
      rewrite pα_inv.
      rewrite <- lwhisker_vcomp, vassocl.
      apply maponpaths.
      rewrite vassocr.
      rewrite lwhisker_lwhisker.
      rewrite vassocl.
      apply maponpaths.
      rewrite vassocr.
      rewrite <- vcomp_whisker.
      rewrite vassocl.
      apply maponpaths.
      apply vcomp_lunitor.
    }
    rewrite ! vassocl.
    rewrite ! rwhisker_vcomp.
    reflexivity.
  Qed.

  Definition inverter_cone_is_invertible_cell_inv_left_adjoint_equivalence
    : is_invertible_2cell (i₁ ◃ α₁)
    := @inverter_cone_is_invertible_cell_left_adjoint_equivalence B p₂ x₂ y₂ p₁
         x₁ y₁ i₂ f₂ g₂ α₂ inv_i₂α₂ i₁ f₁ g₁ α₁ _ _ _
         (inv_left_adjoint_equivalence Hlp) γ₁' γ₂' γ₃' pα'.

  Definition inverter_cone_inv_left_adjoint_equivalence
    := (@inverter_cone_left_adjoint_equivalence B p₂ x₂ y₂ p₁ x₁ y₁ i₂ f₂ g₂ α₂
          inv_i₂α₂ i₁ f₁ g₁ α₁ _ _ _ (inv_left_adjoint_equivalence Hlp) γ₁' γ₂'
          γ₃' pα').

  Definition has_inverter_ump_inv_left_adjoint_equivalence
    := (@has_inverter_ump_left_adjoint_equivalence B p₂ x₂ y₂ p₁ x₁ y₁ i₂ f₂ g₂
          α₂ inv_i₂α₂ i₁ f₁ g₁ α₁ _ _ _ (inv_left_adjoint_equivalence Hlx)
          (inv_left_adjoint_equivalence Hly) (inv_left_adjoint_equivalence Hlp)
          γ₁' γ₂' γ₃' H pα').
End InverterInverseEquivalence.

Section InverterWeqEquivalence.
  Context {B : bicat}
          {p₁ x₁ y₁ p₂ x₂ y₂ : B}
          {i₁ : p₁ --> x₁}
          {f₁ g₁ : x₁ --> y₁}
          {α₁ : f₁ ==> g₁}
          {i₂ : p₂ --> x₂}
          {f₂ g₂ : x₂ --> y₂}
          {α₂ : f₂ ==> g₂}
          (lx : x₁ --> x₂)
          (ly : y₁ --> y₂)
          (lp : p₁ --> p₂)
          (Hlx : left_adjoint_equivalence lx)
          (Hly : left_adjoint_equivalence ly)
          (Hlp : left_adjoint_equivalence lp)
          (γ₁ : invertible_2cell (lp · i₂) (i₁ · lx))
          (γ₂ : invertible_2cell (lx · f₂) (f₁ · ly))
          (γ₃ : invertible_2cell (lx · g₂) (g₁ · ly))
          (pα : (lx ◃ α₂) • γ₃ = γ₂ • (α₁ ▹ ly)).

  Definition weq_inverter_cone_is_invertible_cell_left_adjoint_equivalence
    : is_invertible_2cell (i₁ ◃ α₁) ≃ is_invertible_2cell (i₂ ◃ α₂).
  Proof.
    use weqimplimpl.
    - intro inv_i₁α₁.
      use (inverter_cone_is_invertible_cell_left_adjoint_equivalence lx ly lp Hlp γ₁ γ₂ γ₃ pα).
      exact inv_i₁α₁.
    - intro inv_i₂α₂.
      use (inverter_cone_is_invertible_cell_inv_left_adjoint_equivalence lx ly lp Hlx Hly Hlp γ₁ γ₂ γ₃ pα).
      exact inv_i₂α₂.
    - apply isaprop_is_invertible_2cell.
    - apply isaprop_is_invertible_2cell.
  Defined.
End InverterWeqEquivalence.

(**
 If both rows are inverters, then l₃ is an equivalence.
*)
Section EquivalenceInverters.
  Context {B : bicat}
          {p₁ x₁ y₁ p₂ x₂ y₂ : B}
          {i₁ : p₁ --> x₁}
          {f₁ g₁ : x₁ --> y₁}
          {α₁ : f₁ ==> g₁}
          {inv_i₁α₁ : is_invertible_2cell (i₁ ◃ α₁)}
          (cone₁ :=  make_inverter_cone p₁ i₁ inv_i₁α₁)
          {i₂ : p₂ --> x₂}
          {f₂ g₂ : x₂ --> y₂}
          {α₂ : f₂ ==> g₂}
          {inv_i₂α₂ : is_invertible_2cell (i₂ ◃ α₂)}
          (cone₂ :=  make_inverter_cone p₂ i₂ inv_i₂α₂)
          (lx : x₁ --> x₂)
          (ly : y₁ --> y₂)
          (Hlx : left_adjoint_equivalence lx)
          (Hly : left_adjoint_equivalence ly)
          (γ₂ : invertible_2cell (lx · f₂) (f₁ · ly))
          (γ₃ : invertible_2cell (lx · g₂) (g₁ · ly))
          (H₁ : has_inverter_ump cone₁)
          (H₂ : has_inverter_ump cone₂)
          (pα : (lx ◃ α₂) • γ₃ = γ₂ • (α₁ ▹ ly)).

  Let rx : x₂ --> x₁
    := left_adjoint_right_adjoint Hlx.
  Let ηx : invertible_2cell (id₁ _) (lx · rx)
    := left_equivalence_unit_iso Hlx.
  Let εx : invertible_2cell (rx · lx) (id₁ _)
    := left_equivalence_counit_iso Hlx.

  Let ry : y₂ --> y₁
    := left_adjoint_right_adjoint Hly.
  Let ηy : invertible_2cell (id₁ _) (ly · ry)
    := left_equivalence_unit_iso Hly.
  Let εy : invertible_2cell (ry · ly) (id₁ _)
    := left_equivalence_counit_iso Hly.

  Let γ₂' : invertible_2cell (rx · f₁) (f₂ · ry)
    := comp_of_invertible_2cell
         (rinvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (lwhisker_of_invertible_2cell
               _
               ηy)
            (comp_of_invertible_2cell
               (lassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell
                     _
                     (rassociator_invertible_2cell _ _ _))
                  (comp_of_invertible_2cell
                     (rwhisker_of_invertible_2cell
                        _
                        (lwhisker_of_invertible_2cell
                           _
                           (inv_of_invertible_2cell γ₂)))
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           (lassociator_invertible_2cell _ _ _))
                        (comp_of_invertible_2cell
                           (rwhisker_of_invertible_2cell
                              _
                              (rwhisker_of_invertible_2cell
                                 _
                                 εx))
                           (rwhisker_of_invertible_2cell
                              _
                              (lunitor_invertible_2cell _)))))))).

  Let γ₃' : invertible_2cell (rx · g₁) (g₂ · ry)
    := comp_of_invertible_2cell
         (rinvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (lwhisker_of_invertible_2cell
               _
               ηy)
            (comp_of_invertible_2cell
               (lassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell
                     _
                     (rassociator_invertible_2cell _ _ _))
                  (comp_of_invertible_2cell
                     (rwhisker_of_invertible_2cell
                        _
                        (lwhisker_of_invertible_2cell
                           _
                           (inv_of_invertible_2cell γ₃)))
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           (lassociator_invertible_2cell _ _ _))
                        (comp_of_invertible_2cell
                           (rwhisker_of_invertible_2cell
                              _
                              (rwhisker_of_invertible_2cell
                                 _
                                 εx))
                           (rwhisker_of_invertible_2cell
                              _
                              (lunitor_invertible_2cell _)))))))).

  Let pα_inv : (α₁ ▹ ly) • γ₃^-1 = γ₂^-1 • (lx ◃ α₂) .
  Proof.
    use vcomp_move_L_pV.
    rewrite vassocr.
    refine (!_).
    use vcomp_move_L_Vp.
    exact pα.
  Qed.

  Let pα' : (rx ◃ α₁) • γ₃' = γ₂' • (α₂ ▹ ry).
  Proof.
    cbn.
    rewrite vassoc4.
    rewrite whisker_r_natural.
    rewrite <- vassoc4.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite vassocr.
      rewrite <- rwhisker_rwhisker.
      rewrite vassocl.
      apply maponpaths.
      rewrite ! rwhisker_vcomp.
      apply maponpaths.
      rewrite vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite vassocl.
      apply maponpaths.
      rewrite vassocr, lwhisker_vcomp.
      rewrite pα_inv.
      rewrite <- lwhisker_vcomp, vassocl.
      apply maponpaths.
      rewrite vassocr.
      rewrite lwhisker_lwhisker.
      rewrite vassocl.
      apply maponpaths.
      rewrite vassocr.
      rewrite <- vcomp_whisker.
      rewrite vassocl.
      apply maponpaths.
      apply vcomp_lunitor.
    }
    rewrite ! vassocl.
    rewrite ! rwhisker_vcomp.
    reflexivity.
  Qed.

  Let lp : p₁ --> p₂
    := inverter_ump_mor H₂ (i₁ · lx) (inverter_cone_is_invertible_cell_morphism _ _ _ _ pα cone₁).

  Let rp : p₂ --> p₁
    := inverter_ump_mor H₁ (i₂ · rx) (inverter_cone_is_invertible_cell_morphism _ _ _ _ pα' cone₂).

  Let ηp : invertible_2cell (id₁ _) (lp · rp).
  Proof.
    apply (inverter_ump_invertible_2cell H₁).
    exact (comp_of_invertible_2cell
             (comp_of_invertible_2cell
                (comp_of_invertible_2cell
                   (comp_of_invertible_2cell
                      (comp_of_invertible_2cell
                         (comp_of_invertible_2cell
                            (comp_of_invertible_2cell
                               (lunitor_invertible_2cell _)
                               (rinvunitor_invertible_2cell _))
                            (lwhisker_of_invertible_2cell i₁ ηx))
                        (lassociator_invertible_2cell _ _ _))
                     (rwhisker_of_invertible_2cell rx (inv_of_invertible_2cell (inverter_ump_mor_pr1 H₂ _ _))))
                  (rassociator_invertible_2cell _ _ _))
                (lwhisker_of_invertible_2cell lp (inv_of_invertible_2cell (inverter_ump_mor_pr1 H₁ _ _))))
             (lassociator_invertible_2cell _ _ _)).
  Defined.

  Let εp : invertible_2cell (rp · lp) (id₁ _).
  Proof.
    apply (inverter_ump_invertible_2cell H₂).
    exact (comp_of_invertible_2cell
             (comp_of_invertible_2cell
                (comp_of_invertible_2cell
                   (comp_of_invertible_2cell
                      (comp_of_invertible_2cell
                         (comp_of_invertible_2cell
                            (comp_of_invertible_2cell
                               (rassociator_invertible_2cell _ _ _)
                               (lwhisker_of_invertible_2cell rp (inverter_ump_mor_pr1 H₂ _ _)))
                            (lassociator_invertible_2cell _ _ _))
                         (rwhisker_of_invertible_2cell lx (inverter_ump_mor_pr1 H₁ _ _)))
                      (rassociator_invertible_2cell _ _ _))
                   (lwhisker_of_invertible_2cell i₂ εx))
                (runitor_invertible_2cell _))
             (linvunitor_invertible_2cell _)).
  Defined.

  Definition left_equivalence_data_inverters
    : left_adjoint_data lp
    := (rp ,, (cell_from_invertible_2cell ηp ,, cell_from_invertible_2cell εp)).

  Definition left_equivalence_axioms_inverters
    : left_equivalence_axioms left_equivalence_data_inverters.
  Proof.
    split; apply property_from_invertible_2cell.
  Defined.

  Definition left_equivalence_inverters
    : left_equivalence lp
    := (left_equivalence_data_inverters ,, left_equivalence_axioms_inverters).
End EquivalenceInverters.
