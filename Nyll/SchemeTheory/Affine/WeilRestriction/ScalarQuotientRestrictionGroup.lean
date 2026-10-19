/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientRestrictionScheme

/-! # Group classification of the concrete scalar quotient restriction -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite Module

attribute [local instance] MvPolynomial.gradedAlgebra

namespace SchemeTheory.Affine.ScalarQuotientSchemePresheaf

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  {n m : ℕ} (bA : Basis (Fin (n + 1)) R A) (bB : Basis (Fin (m + 1)) R B)
  (f : A →ₐ[R] B)

/-- The actual group-valued restriction after fppf sheafification. -/
def algebraRestrictionGroupSheaf : scalarQuotientGroupSheaf R A ⟶
    scalarQuotientGroupSheaf R B :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}).map
      (Functor.whiskerRight (algebraRestrictionPresheaf f) CommGrpCat.uliftFunctor.{u + 1, u})

/-- Forgetting group structure identifies the canonical group restriction with the
concrete projective norm-open restriction. This uses naturality of sheafification. -/
theorem scalarQuotientRepresentingIso_restriction :
    Functor.whiskerRight (algebraRestrictionGroupSheaf f).hom
        (forget CommGrpCat.{u + 1}) ≫ (scalarQuotientRepresentingIso bB).hom =
      (scalarQuotientRepresentingIso bA).hom ≫
        uliftYoneda.map (quotientRestrictionOver bA bB f) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  let U := forget CommGrpCat.{u + 1}
  let a : liftedGroupPresheaf R A ⟶ liftedGroupPresheaf R B :=
    Functor.whiskerRight (algebraRestrictionPresheaf f) CommGrpCat.uliftFunctor.{u + 1, u}
  let e := sheafComposeNatIso J U (sheafificationAdjunction J CommGrpCat.{u + 1})
    (sheafificationAdjunction J (Type (u + 1)))
  have hn : Functor.whiskerRight (algebraRestrictionGroupSheaf f).hom U ≫
        (sheafifyComposeIso J U (liftedGroupPresheaf R B)).inv =
      (sheafifyComposeIso J U (liftedGroupPresheaf R A)).inv ≫
        sheafifyMap J (Functor.whiskerRight a U) :=
    congrArg (fun k => (sheafToPresheaf J (Type (u + 1))).map k) (e.inv.naturality a)
  change Functor.whiskerRight (algebraRestrictionGroupSheaf f).hom U ≫
      ((sheafifyComposeIso J U (liftedGroupPresheaf R B)).inv ≫
        (sheafifiedComparisonIso bB).hom) =
    ((sheafifyComposeIso J U (liftedGroupPresheaf R A)).inv ≫
      (sheafifiedComparisonIso bA).hom) ≫ uliftYoneda.map (quotientRestrictionOver bA bB f)
  rw [uliftYoneda_map_quotientRestrictionOver]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (sheafifiedComparisonIso bB).hom) hn).trans
      (Category.assoc _ _ _))

/-- On every parameter scheme, the concrete norm quotient map is the original group
sheaf restriction under the proved representing equivalences. -/
theorem quotientRestrictionOver_homEquiv {T : Over (Spec (CommRingCat.of R))}
    (g : T ⟶ representingObject bA) :
    (scalarQuotientRepresentable bB).homEquiv (g ≫ quotientRestrictionOver bA bB f) =
      ((algebraRestrictionGroupSheaf f).hom.app (op T)).hom
        ((scalarQuotientRepresentable bA).homEquiv g) := by
  have hn : uliftYoneda.map (quotientRestrictionOver bA bB f) ≫
        (scalarQuotientRepresentingIso bB).inv =
      (scalarQuotientRepresentingIso bA).inv ≫
        Functor.whiskerRight (algebraRestrictionGroupSheaf f).hom
          (forget CommGrpCat.{u + 1}) := by
    symm
    apply (scalarQuotientRepresentingIso bA).inv_comp_eq.mpr
    symm
    rw [← Category.assoc]
    apply (scalarQuotientRepresentingIso bB).comp_inv_eq.mpr
    exact (scalarQuotientRepresentingIso_restriction bA bB f).symm
  exact congrArg (fun k => TypeCat.homEquiv (k.app (op T)) (ULift.up g)) hn

end SchemeTheory.Affine.ScalarQuotientSchemePresheaf
