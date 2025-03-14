Require Import UniMath.Foundations.Preamble.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.

Local Open Scope cat.

Section Preserves.
  Context {B₁ B₂ : bicat}
          (F : psfunctor B₁ B₂)
          {a b : B₁}
          {f : a --> b}.

  Definition psfunctor_left_adjoint_data
             (αd : left_adjoint_data f)
    : left_adjoint_data (# F f)
    := (# F (pr1 αd) ,,
        (psfunctor_id F a • ## F (pr12 αd) • (psfunctor_comp F f (pr1 αd))^-1 ,,
         psfunctor_comp F (pr1 αd) f • ## F (pr22 αd) • (psfunctor_id F b)^-1)).

  Definition psfunctor_left_equivalence_axioms
             {αd : left_adjoint_data f}
             (H : left_equivalence_axioms αd)
    : left_equivalence_axioms (psfunctor_left_adjoint_data αd).
  Proof.
    split; cbn - [cell_from_invertible_2cell]; is_iso;
    try (apply property_from_invertible_2cell).
    - exact (psfunctor_is_iso F (_ ,, pr1 H)).
    - exact (psfunctor_is_iso F (left_adjoint_counit αd ,, pr2 H)).
  Defined.

  Definition psfunctor_left_equivalence
             (αe : left_equivalence f)
    : left_equivalence (# F f)
    := (psfunctor_left_adjoint_data (pr1 αe) ,,
        psfunctor_left_equivalence_axioms (pr2 αe)).
End Preserves.
