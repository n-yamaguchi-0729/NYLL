/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUnitRestrictionAffine

/-! # Changing-modulus compatibility of the actual fppf group comparison -/

noncomputable section

universe u

open CategoryTheory Opposite
open SchemeTheory.Affine SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {K : Type u} [Field K] {Y Y' : Scheme.{u}}
  {q : Y ⟶ Spec (CommRingCat.of K)} {q' : Y' ⟶ Spec (CommRingCat.of K)}
  (j : Y' ⟶ Y) (w : j ≫ q = q') [IsFinite q] [IsFinite q']

/-- Restriction on the algebraic scalar quotient, retaining its lifted group structure. -/
def liftedAlgebraUnitRestrictionPresheaf :
    ScalarQuotientSchemePresheaf.liftedGroupPresheaf K (coordinateAlgebra q) ⟶
      ScalarQuotientSchemePresheaf.liftedGroupPresheaf K (coordinateAlgebra q') :=
  Functor.whiskerRight
    (ScalarQuotientSchemePresheaf.algebraRestrictionPresheaf (coordinateRestriction q q' j w))
    CommGrpCat.uliftFunctor.{u + 1, u}

/-- The affine square remains multiplicative in the big-site value universe. -/
theorem scalarQuotientLiftedAffineGroupIso_restriction_square :
    Functor.whiskerLeft (specOverFunctor (CommRingCat.of K)).op
        (liftedAlgebraUnitRestrictionPresheaf j w) ≫
      (scalarQuotientLiftedAffineGroupIso q').hom =
    (scalarQuotientLiftedAffineGroupIso q).hom ≫
      Functor.whiskerLeft (specOverFunctor (CommRingCat.of K)).op
        (liftedModulusUnitRestrictionPresheaf j w) := by
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  intro x
  apply ULift.ext
  exact scalarQuotientAffineIso_restriction j w S.unop.unop x.down

/-- This is the actual affine comparison used inside the existing group sheaf isomorphism. -/
private def restrictedGroupComparison
    {Z : Scheme.{u}} (r : Z ⟶ Spec (CommRingCat.of K)) [IsFinite r] :
    (affineForget (CommRingCat.of K)).op ⋙
        ScalarQuotientSchemePresheaf.liftedGroupPresheaf K (coordinateAlgebra r) ≅
      (affineForget (CommRingCat.of K)).op ⋙ liftedModulusUnitQuotientGroupPresheaf r := by
  let R := CommRingCat.of K
  let F := ScalarQuotientSchemePresheaf.liftedGroupPresheaf K (coordinateAlgebra r)
  let G := liftedModulusUnitQuotientGroupPresheaf r
  exact Functor.isoWhiskerRight (NatIso.op (affineToSpecGammaIso R).symm) F ≪≫
    Functor.associator (affineAlgebraEquiv R).functor.rightOp.op (specOverFunctor R).op F ≪≫
      Functor.isoWhiskerLeft (affineAlgebraEquiv R).functor.rightOp.op
        (scalarQuotientLiftedAffineGroupIso r) ≪≫
        (Functor.associator (affineAlgebraEquiv R).functor.rightOp.op
          (specOverFunctor R).op G).symm ≪≫
          (Functor.isoWhiskerRight (NatIso.op (affineToSpecGammaIso R).symm) G).symm

private theorem restrictedGroupComparison_restriction_square :
    Functor.whiskerLeft (affineForget (CommRingCat.of K)).op
        (liftedAlgebraUnitRestrictionPresheaf j w) ≫ (restrictedGroupComparison q').hom =
      (restrictedGroupComparison q).hom ≫
        Functor.whiskerLeft (affineForget (CommRingCat.of K)).op
          (liftedModulusUnitRestrictionPresheaf j w) := by
  let R := CommRingCat.of K
  let F := ScalarQuotientSchemePresheaf.liftedGroupPresheaf K (coordinateAlgebra q)
  let F' := ScalarQuotientSchemePresheaf.liftedGroupPresheaf K (coordinateAlgebra q')
  let G := liftedModulusUnitQuotientGroupPresheaf q
  let G' := liftedModulusUnitQuotientGroupPresheaf q'
  let a := liftedAlgebraUnitRestrictionPresheaf j w
  let b := liftedModulusUnitRestrictionPresheaf j w
  apply NatTrans.ext
  funext T
  let S := (affineAlgebraEquiv R).functor.rightOp.op.obj T
  let σ : (affineForget R).op.obj T ⟶ (specOverFunctor R).op.obj S :=
    ((affineToSpecGammaIso R).inv.app T.unop).op
  let τ : (specOverFunctor R).op.obj S ⟶ (affineForget R).op.obj T :=
    ((affineToSpecGammaIso R).hom.app T.unop).op
  have ha := a.naturality σ
  have hb := b.naturality τ
  have he := NatTrans.congr_app
    (scalarQuotientLiftedAffineGroupIso_restriction_square j w) S
  change a.app _ ≫ (F'.map σ ≫ (scalarQuotientLiftedAffineGroupIso q').hom.app S ≫ G'.map τ) =
    (F.map σ ≫ (scalarQuotientLiftedAffineGroupIso q).hom.app S ≫ G.map τ) ≫ b.app _
  change a.app _ ≫ (scalarQuotientLiftedAffineGroupIso q').hom.app S =
    (scalarQuotientLiftedAffineGroupIso q).hom.app S ≫ b.app _ at he
  simp only [Category.assoc]
  rw [← reassoc_of% ha, reassoc_of% he, ← hb]

/-- The algebraic scalar quotient restriction after genuine group-valued sheafification. -/
def algebraUnitRestrictionSheaf :
    ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (coordinateAlgebra q) ⟶
      ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (coordinateAlgebra q') :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    CommGrpCat.{u + 1}).map (liftedAlgebraUnitRestrictionPresheaf j w)

private theorem restricted_modulusUnitGroupSheafComparisonIso
    {Z : Scheme.{u}} (r : Z ⟶ Spec (CommRingCat.of K)) [IsFinite r] :
    let R := CommRingCat.of K
    let J := Scheme.fppfTopology.over (Spec R)
    let I := (affineForget R).restrictedTopology J
    let E := Functor.IsDenseSubsite.sheafEquiv I J (affineForget R) CommGrpCat.{u + 1}
    let e := Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility
      I J (affineForget R) CommGrpCat.{u + 1}
    E.inverse.map (modulusUnitGroupSheafComparisonIso r).hom =
      (e.app (ScalarQuotientSchemePresheaf.liftedGroupPresheaf K (coordinateAlgebra r))).inv ≫
        (presheafToSheaf I CommGrpCat.{u + 1}).map (restrictedGroupComparison r).hom ≫
          (e.app (liftedModulusUnitQuotientGroupPresheaf r)).hom := by
  dsimp only
  exact (Functor.IsDenseSubsite.sheafEquiv
    ((affineForget (CommRingCat.of K)).restrictedTopology
      (Scheme.fppfTopology.over (Spec (CommRingCat.of K))))
    (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    (affineForget (CommRingCat.of K)) CommGrpCat.{u + 1}).symm.fullyFaithfulFunctor.map_preimage _

/-- The existing algebraic-to-intrinsic group sheaf comparison is natural for actual
modulus restriction. Its affine compatibility is proved on tensor factors above. -/
theorem modulusUnitGroupSheafComparisonIso_restriction :
    algebraUnitRestrictionSheaf j w ≫ (modulusUnitGroupSheafComparisonIso q').hom =
      (modulusUnitGroupSheafComparisonIso q).hom ≫ modulusUnitRestrictionSheaf j w := by
  let R := CommRingCat.of K
  let J := Scheme.fppfTopology.over (Spec R)
  let I := (affineForget R).restrictedTopology J
  let E := Functor.IsDenseSubsite.sheafEquiv I J (affineForget R) CommGrpCat.{u + 1}
  let e := Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility
    I J (affineForget R) CommGrpCat.{u + 1}
  let H := presheafToSheaf I CommGrpCat.{u + 1}
  let Hbig := presheafToSheaf J CommGrpCat.{u + 1}
  let F := ScalarQuotientSchemePresheaf.liftedGroupPresheaf K (coordinateAlgebra q)
  let F' := ScalarQuotientSchemePresheaf.liftedGroupPresheaf K (coordinateAlgebra q')
  let G := liftedModulusUnitQuotientGroupPresheaf q
  let G' := liftedModulusUnitQuotientGroupPresheaf q'
  let a : F ⟶ F' := liftedAlgebraUnitRestrictionPresheaf j w
  let b : G ⟶ G' := liftedModulusUnitRestrictionPresheaf j w
  apply E.inverse.map_injective
  rw [Functor.map_comp, Functor.map_comp,
    restricted_modulusUnitGroupSheafComparisonIso,
    restricted_modulusUnitGroupSheafComparisonIso]
  change E.inverse.map (Hbig.map a) ≫
      ((e.app F').inv ≫ H.map (restrictedGroupComparison q').hom ≫ (e.app G').hom) =
    ((e.app F).inv ≫ H.map (restrictedGroupComparison q).hom ≫ (e.app G).hom) ≫
      E.inverse.map (Hbig.map b)
  apply (cancel_epi (e.app F).hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have ha := e.hom.naturality a
  have hb := e.hom.naturality b
  change H.map (Functor.whiskerLeft (affineForget R).op a) ≫ (e.app F').hom =
    (e.app F).hom ≫ E.inverse.map (Hbig.map a) at ha
  change H.map (Functor.whiskerLeft (affineForget R).op b) ≫ (e.app G').hom =
    (e.app G).hom ≫ E.inverse.map (Hbig.map b) at hb
  rw [← reassoc_of% ha, Iso.hom_inv_id_assoc, ← hb]
  exact (by
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun k => H.map k ≫ (e.app G').hom)
        (restrictedGroupComparison_restriction_square j w))

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
