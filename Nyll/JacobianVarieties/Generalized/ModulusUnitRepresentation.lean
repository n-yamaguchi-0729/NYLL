/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUnitAffineComparison
import Nyll.SchemeTheory.Affine.AffineFppfComparison
import Nyll.SchemeTheory.Affine.RelativeSectionsOnSpectra
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientGroupScheme

/-!
# Representation of the intrinsic modulus-unit sheaf

The affine-test comparison extends through the actual big fppf site. Thus
the intrinsic quotient of units on scheme fibre products is represented by
the same projective norm open as the algebraic scalar quotient. A chosen
actual frame also gives a representation of the scalar-frame sheaf.

The Poincaré family over the ordinary Jacobian need not have a global
frame; its local represented charts still have to be glued.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory Module
open SchemeTheory.Affine SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {K : Type u} [Field K] {Y : Scheme.{u}}
  (q : Y ⟶ Spec (CommRingCat.of K)) [IsFinite q]

/-- The algebraic global-sections model and the intrinsic model agree on affine tests. -/
def scalarQuotientAffineIso :
    (specOverFunctor (CommRingCat.of K)).op ⋙
        ScalarQuotientSchemePresheaf.groupPresheaf K (coordinateAlgebra q) ≅
      (specOverFunctor (CommRingCat.of K)).op ⋙ modulusUnitQuotientPresheaf q :=
  relativeSectionsSpectrumRestrictionIso (CommRingCat.of K)
    (ScalarQuotientPresheaf.quotientFunctor K (coordinateAlgebra q)) ≪≫
      algebraicModulusUnitAffineIso q

/-- The affine comparison in the actual value universe of big-site sheafification. -/
def scalarQuotientLiftedAffineIso :
    (specOverFunctor (CommRingCat.of K)).op ⋙
        (ScalarQuotientSchemePresheaf.liftedGroupPresheaf K (coordinateAlgebra q) ⋙
          forget CommGrpCat.{u + 1}) ≅
      (specOverFunctor (CommRingCat.of K)).op ⋙ liftedModulusUnitQuotientPresheaf q :=
  NatIso.ofComponents (fun A =>
    (Equiv.ulift.trans
      ((scalarQuotientAffineIso q).app A).commGroupIsoToMulEquiv.toEquiv |>.trans
        Equiv.ulift.symm).toIso)
    (fun g => by
      apply TypeCat.homEquiv.injective
      funext x
      apply ULift.ext
      exact ConcreteCategory.congr_hom ((scalarQuotientAffineIso q).hom.naturality g) x.down)

/-- The proved affine comparison identifies the actual fppf sheafifications. -/
def modulusUnitSheafComparisonIso :
    (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (Type (u + 1))).obj
        (ScalarQuotientSchemePresheaf.liftedGroupPresheaf K (coordinateAlgebra q) ⋙
          forget CommGrpCat.{u + 1}) ≅ modulusUnitQuotientSheaf q :=
  fppfSheafificationIsoOfSpecRestriction (CommRingCat.of K) (scalarQuotientLiftedAffineIso q)

variable {n : ℕ} (b : Basis (Fin (n + 1)) K (coordinateAlgebra q))

/-- The intrinsic modulus-unit sheaf is the represented projective norm open. -/
def modulusUnitRepresentingIso :
    (modulusUnitQuotientSheaf q).obj ≅
      uliftYoneda.{u + 1}.obj (ScalarQuotientSchemePresheaf.representingObject b) :=
  (sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    (Type (u + 1))).mapIso (modulusUnitSheafComparisonIso q).symm ≪≫
      ScalarQuotientSchemePresheaf.sheafifiedComparisonIso b

/-- Representation of the actual geometric scalar-unit quotient on all test schemes. -/
def modulusUnitSheafRepresentable :
    (modulusUnitQuotientSheaf q).obj.RepresentableBy
      (ScalarQuotientSchemePresheaf.representingObject b) :=
  (Functor.RepresentableBy.equivUliftYonedaIso _ _).symm (modulusUnitRepresentingIso q b).symm

/-- A genuine reference frame gives the local scalar-frame representation by the same scheme. -/
def scalarFrameSheafRepresentable {M : Y.Modules} (e : M ≅ 𝟙_ Y.Modules) :
    (scalarFrameSheaf q M).obj.RepresentableBy
      (ScalarQuotientSchemePresheaf.representingObject b) :=
  (modulusUnitSheafRepresentable q b).ofIso
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (Type (u + 1))).mapIso (scalarFrameSheafCoordinatesIso q e).symm)

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
