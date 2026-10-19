/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUnitRepresentation
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIso

/-! # The intrinsic modulus-unit quotient as an actual represented group sheaf -/

noncomputable section

universe u

open CategoryTheory Module
open SchemeTheory.Affine SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y S : Scheme.{u}} (q : Y ⟶ S)

/-- The intrinsic quotient, retaining its multiplicative law in the big-site universe. -/
def liftedModulusUnitQuotientGroupPresheaf : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} :=
  modulusUnitQuotientPresheaf q ⋙ CommGrpCat.uliftFunctor.{u + 1, u}

/-- Sheafification of actual modulus units modulo parameter scalars in commutative groups. -/
def modulusUnitQuotientGroupSheaf : Sheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).obj
    (liftedModulusUnitQuotientGroupPresheaf q)

/-- Its underlying sheaf is the previously constructed intrinsic modulus-unit sheaf. -/
def modulusUnitQuotientGroupSheafForgetIso :
    (modulusUnitQuotientGroupSheaf q).obj ⋙ forget CommGrpCat.{u + 1} ≅
      (modulusUnitQuotientSheaf q).obj :=
  (sheafifyComposeIso (Scheme.fppfTopology.over S) (forget CommGrpCat.{u + 1})
    (liftedModulusUnitQuotientGroupPresheaf q)).symm

variable {K : Type u} [Field K] {Y : Scheme.{u}}
  (q : Y ⟶ Spec (CommRingCat.of K)) [IsFinite q]

/-- The existing affine comparison preserves the actual group structures after lifting. -/
def scalarQuotientLiftedAffineGroupIso :
    (specOverFunctor (CommRingCat.of K)).op ⋙
        ScalarQuotientSchemePresheaf.liftedGroupPresheaf K (coordinateAlgebra q) ≅
      (specOverFunctor (CommRingCat.of K)).op ⋙
        liftedModulusUnitQuotientGroupPresheaf q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (scalarQuotientAffineIso q) CommGrpCat.uliftFunctor ≪≫
      Functor.associator _ _ _

/-- The actual dense affine comparison extends in commutative groups, so no
multiplicativity property of a merely set-valued comparison is assumed. -/
def modulusUnitGroupSheafComparisonIso :
    ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (coordinateAlgebra q) ≅
      modulusUnitQuotientGroupSheaf q := by
  let R := CommRingCat.of K
  let F := ScalarQuotientSchemePresheaf.liftedGroupPresheaf K (coordinateAlgebra q)
  let G := liftedModulusUnitQuotientGroupPresheaf q
  let a : (affineForget R).op ⋙ F ≅ (affineForget R).op ⋙ G :=
    Functor.isoWhiskerRight (NatIso.op (affineToSpecGammaIso R).symm) F ≪≫
      Functor.associator (affineAlgebraEquiv R).functor.rightOp.op (specOverFunctor R).op F ≪≫
        Functor.isoWhiskerLeft (affineAlgebraEquiv R).functor.rightOp.op
          (scalarQuotientLiftedAffineGroupIso q) ≪≫
          (Functor.associator (affineAlgebraEquiv R).functor.rightOp.op
            (specOverFunctor R).op G).symm ≪≫
            (Functor.isoWhiskerRight (NatIso.op (affineToSpecGammaIso R).symm) G).symm
  let J := Scheme.fppfTopology.over (Spec R)
  let I := (affineForget R).restrictedTopology J
  let E := Functor.IsDenseSubsite.sheafEquiv I J (affineForget R) CommGrpCat.{u + 1}
  let e := Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility
    I J (affineForget R) CommGrpCat.{u + 1}
  exact E.symm.fullyFaithfulFunctor.preimageIso
    ((e.app F).symm ≪≫ (presheafToSheaf I CommGrpCat.{u + 1}).mapIso a ≪≫ e.app G)

variable {n : ℕ} (b : Basis (Fin (n + 1)) K (coordinateAlgebra q))

/-- The intrinsic multiplicative sheaf is represented on the same concrete norm open. -/
def modulusUnitGroupSheafRepresentable :
    ((modulusUnitQuotientGroupSheaf q).obj ⋙ forget CommGrpCat.{u + 1}).RepresentableBy
      (ScalarQuotientSchemePresheaf.representingObject b) :=
  (ScalarQuotientSchemePresheaf.scalarQuotientRepresentable b).ofIso
    (Functor.isoWhiskerRight
      ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        CommGrpCat.{u + 1}).mapIso (modulusUnitGroupSheafComparisonIso q))
      (forget CommGrpCat.{u + 1}))

/-- The intrinsic modulus-unit group scheme, with its proved group representation. -/
def modulusUnitCommGroupScheme : CommGrp (Over (Spec (CommRingCat.of K))) :=
  SchemeTheory.RepresentedGroups.groupObject
    (modulusUnitQuotientGroupSheaf q).obj (modulusUnitGroupSheafRepresentable q b)

/-- The intrinsic and algebraic norm-open group schemes are isomorphic as groups. -/
def modulusUnitCommGroupSchemeIso : modulusUnitCommGroupScheme q b ≅
    ScalarQuotientSchemePresheaf.scalarQuotientCommGroupScheme b :=
  SchemeTheory.RepresentedGroups.iso _ _ (modulusUnitGroupSheafRepresentable q b)
    (ScalarQuotientSchemePresheaf.scalarQuotientRepresentable b)
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      CommGrpCat.{u + 1}).mapIso (modulusUnitGroupSheafComparisonIso q).symm)

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
