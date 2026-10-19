/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.FiniteSchemeScalarNaturality

/-!
# The actual scalar-unit quotient as a functor on affine tests

Both its values and its maps come from the actual base-changed finite
scheme. The natural tensor comparison identifies it as a group-valued
functor with the algebraic scalar quotient used in the norm-open construction.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace SchemeTheory.Affine.FiniteScheme

variable {K A B C : Type u} [Field K] [CommRing A] [CommRing B] [CommRing C]
  [Algebra K A] [Algebra K B] [Algebra K C]
  {Z : Scheme.{u}} (q : Z ⟶ Spec (CommRingCat.of K)) [IsFinite q]

theorem baseChangedScalarQuotientMap_id (x : BaseChangedScalarQuotient (A := A) q) :
    baseChangedScalarQuotientMap q (AlgHom.id K A) x = x := by
  obtain ⟨a, rfl⟩ := (baseChangedScalarQuotientEquiv (A := A) q).surjective x
  have ha : ScalarQuotientPresheaf.quotientMap (AlgHom.id K A) a = a :=
    ConcreteCategory.congr_hom
      ((ScalarQuotientPresheaf.quotientFunctor K (coordinateAlgebra q)).map_id
        (CommAlgCat.of K A)) a
  exact (baseChangedScalarQuotientEquiv_naturality q (AlgHom.id K A) a).symm.trans
    (congrArg (baseChangedScalarQuotientEquiv (A := A) q) ha)

theorem baseChangedScalarQuotientMap_comp (f : A →ₐ[K] B) (g : B →ₐ[K] C)
    (x : BaseChangedScalarQuotient (A := A) q) :
    baseChangedScalarQuotientMap q (g.comp f) x =
      baseChangedScalarQuotientMap q g (baseChangedScalarQuotientMap q f x) := by
  obtain ⟨a, rfl⟩ := (baseChangedScalarQuotientEquiv (A := A) q).surjective x
  have ha : ScalarQuotientPresheaf.quotientMap (g.comp f) a =
      ScalarQuotientPresheaf.quotientMap g (ScalarQuotientPresheaf.quotientMap f a) :=
    ConcreteCategory.congr_hom
      ((ScalarQuotientPresheaf.quotientFunctor K (coordinateAlgebra q)).map_comp
        (CommAlgCat.ofHom f) (CommAlgCat.ofHom g)) a
  exact (baseChangedScalarQuotientEquiv_naturality q (g.comp f) a).symm.trans
    ((congrArg (baseChangedScalarQuotientEquiv (A := C) q) ha).trans
      ((baseChangedScalarQuotientEquiv_naturality q g
        (ScalarQuotientPresheaf.quotientMap f a)).trans
          (congrArg (baseChangedScalarQuotientMap q g)
            (baseChangedScalarQuotientEquiv_naturality q f a))))

/-- The group functor defined by actual geometric pullbacks and scalar classes. -/
def baseChangedScalarQuotientFunctor : CommAlgCat.{u} K ⥤ CommGrpCat.{u} where
  obj A := CommGrpCat.of (BaseChangedScalarQuotient (A := A) q)
  map f := CommGrpCat.ofHom (baseChangedScalarQuotientMap q f.hom)
  map_id A := by
    apply ConcreteCategory.hom_ext
    exact baseChangedScalarQuotientMap_id q
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    exact baseChangedScalarQuotientMap_comp q f.hom g.hom

/-- The geometric and algebraic scalar quotients agree as group-valued functors. -/
def baseChangedScalarQuotientFunctorIso :
    ScalarQuotientPresheaf.quotientFunctor K (coordinateAlgebra q) ≅
      baseChangedScalarQuotientFunctor q :=
  NatIso.ofComponents (fun A => (baseChangedScalarQuotientEquiv (A := A) q).toCommGrpIso)
    (fun f => by
      apply ConcreteCategory.hom_ext
      exact baseChangedScalarQuotientEquiv_naturality q f.hom)

end SchemeTheory.Affine.FiniteScheme
