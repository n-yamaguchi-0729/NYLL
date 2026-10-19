/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.SplitScalarQuotient
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientGroupScheme
import Nyll.SchemeTheory.GroupSchemes.SplitTorusSchemePoints
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupTargetIso

/-! # The actual scalar-unit quotient of a split algebra is a split torus -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite Module
open scoped CategoryTheory.MonObj

namespace SchemeTheory.Affine.ScalarQuotientSchemePresheaf

open ScalarQuotientPresheaf AlgebraicGeometry.GroupSchemes

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The group of points of the original Hopf split torus on every test scheme. -/
def torusPointGroupPresheaf : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of (ULift.{u + 1} (T.unop ⟶ (splitTorus R n).X))
  map f := CommGrpCat.ofHom
    { toFun := fun x => ULift.up (f.unop ≫ x.down)
      map_one' := congrArg ULift.up (MonObj.comp_one f.unop)
      map_mul' := fun x y => congrArg ULift.up (MonObj.comp_mul f.unop x.down y.down) }
  map_id T := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact congrArg ULift.up (Category.id_comp x.down)
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact congrArg ULift.up (Category.assoc g.unop f.unop x.down)

/-- Forgetting the point groups gives exactly the usual universe-lifted Yoneda presheaf. -/
def torusPointGroupForgetIso :
    torusPointGroupPresheaf R n ⋙ forget CommGrpCat.{u + 1} ≅
      uliftYoneda.{u + 1}.obj (splitTorus R n).X := Iso.refl _

/-- Actual split-torus points satisfy fppf descent. -/
theorem torusPointGroup_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (torusPointGroupPresheaf R n) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget CommGrpCat.{u + 1})
  exact ((GrothendieckTopology.uliftYoneda.{u + 1}
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).obj (splitTorus R n).X).property

variable {R n} {A : Type u} [CommRing A] [Algebra R A]
  (e : A ≃ₐ[R] (Fin (n + 1) → R))

/-- Actual scalar classes correspond multiplicatively to actual split-torus points. -/
def splitScalarPointEquiv (T : Over (Spec (CommRingCat.of R))) :
    ScalarQuotient (R := R) (A := A) (S := sectionsAlgebra R T) ≃*
      (T ⟶ (splitTorus R n).X) :=
  (splitScalarQuotientEquiv e).trans (splitTorusPointEquiv R n T).symm

/-- Coordinate ratios commute with every map of parameter schemes. -/
theorem splitScalarPointEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (x : ScalarQuotient (R := R) (A := A) (S := sectionsAlgebra R T)) :
    splitScalarPointEquiv e T' (quotientMap (sectionsMap f) x) =
      f ≫ splitScalarPointEquiv e T x := by
  apply (splitTorusPointEquiv R n T').injective
  funext i
  change splitTorusPointEquiv R n T'
      ((splitTorusPointEquiv R n T').symm
        (splitScalarQuotientEquiv e (quotientMap (sectionsMap f) x))) i = _
  rw [MulEquiv.apply_symm_apply, splitTorusPointEquiv_naturality]
  change splitScalarQuotientEquiv e (quotientMap (sectionsMap f) x) i =
    Units.map (sectionsMap f).toRingHom.toMonoidHom
      (splitTorusPointEquiv R n T
        ((splitTorusPointEquiv R n T).symm (splitScalarQuotientEquiv e x)) i)
  rw [MulEquiv.apply_symm_apply]
  exact splitScalarQuotientEquiv_naturality e (sectionsMap f) x i

/-- This is an isomorphism of actual group presheaves on the entire big scheme site. -/
def splitScalarPointPresheafIso :
    liftedGroupPresheaf R A ≅ torusPointGroupPresheaf R n :=
  NatIso.ofComponents (fun T => MulEquiv.toCommGrpIso
    ((MulEquiv.ulift.trans (splitScalarPointEquiv e T.unop)).trans MulEquiv.ulift.symm))
    (fun f => by
      apply CommGrpCat.hom_ext
      apply MonoidHom.ext
      intro x
      exact congrArg ULift.up (splitScalarPointEquiv_naturality e f.unop x.down))

/-- Sheafifying the actual point isomorphism retains the original split-torus group law. -/
def splitScalarPointSheafIso :
    (scalarQuotientGroupSheaf R A).obj ≅ torusPointGroupPresheaf R n :=
  (sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}).mapIso
      ((presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        CommGrpCat.{u + 1}).mapIso (splitScalarPointPresheafIso e)) ≪≫
    (isoSheafify _ (torusPointGroup_isSheaf R n)).symm

/-- A multiplicative representing dictionary on the actual split-torus carrier. -/
def splitScalarTorusRepresentable :
    ((scalarQuotientGroupSheaf R A).obj ⋙ forget CommGrpCat.{u + 1}).RepresentableBy
      (splitTorus R n).X where
  homEquiv := Equiv.ulift.symm.trans
    ((splitScalarPointSheafIso e).symm.app _).commGroupIsoToMulEquiv.toEquiv
  homEquiv_comp f g := by
    exact ConcreteCategory.congr_hom ((splitScalarPointSheafIso e).inv.naturality f.op)
      (ULift.up g)

/-- The concrete norm-open group is isomorphic to the original Hopf split torus. -/
def splitScalarQuotientTorusIso (b : Basis (Fin (n + 1)) R A) :
    scalarQuotientCommGroupScheme b ≅ splitTorus R n :=
  RepresentedGroups.isoToGroup (scalarQuotientGroupSheaf R A).obj
    (scalarQuotientRepresentable b) (splitTorus R n) (splitScalarTorusRepresentable e)
    (fun T f g => ((splitScalarPointSheafIso e).inv.app (op T)).hom.map_mul
      (ULift.up f) (ULift.up g))

end SchemeTheory.Affine.ScalarQuotientSchemePresheaf
