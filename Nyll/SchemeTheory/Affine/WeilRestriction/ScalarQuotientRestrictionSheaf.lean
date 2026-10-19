/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientRestriction
import Nyll.SchemeTheory.Affine.WeilRestriction.UnitsOnSchemes
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Over

/-! # The Cartesian restriction square after actual fppf sheafification -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Module
open scoped TensorProduct

namespace SchemeTheory.Affine.ScalarQuotientPresheaf

variable {R A B S T : Type u} [CommRing R] [CommRing A] [CommRing B]
  [CommRing S] [CommRing T] [Algebra R A] [Algebra R B] [Algebra R S] [Algebra R T]
  (f : A →ₐ[R] B)

/-- Restriction of the algebra factor commutes with extension of test coefficients. -/
theorem algebraUnitRestriction_naturality (g : S →ₐ[R] T) (a : (S ⊗[R] A)ˣ) :
    algebraUnitRestriction f (unitMap g a) = unitMap g (algebraUnitRestriction f a) := by
  apply Units.ext
  change Algebra.TensorProduct.map (AlgHom.id R T) f
      (Algebra.TensorProduct.map g (AlgHom.id R A) (a : S ⊗[R] A)) =
    Algebra.TensorProduct.map g (AlgHom.id R B)
      (Algebra.TensorProduct.map (AlgHom.id R S) f (a : S ⊗[R] A))
  have hm : (Algebra.TensorProduct.map (AlgHom.id R T) f).comp
      (Algebra.TensorProduct.map g (AlgHom.id R A)) =
    (Algebra.TensorProduct.map g (AlgHom.id R B)).comp
      (Algebra.TensorProduct.map (AlgHom.id R S) f) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
      AlgHom.id_comp, AlgHom.comp_id, AlgHom.comp_id, AlgHom.id_comp]
  exact AlgHom.congr_fun hm _

end SchemeTheory.Affine.ScalarQuotientPresheaf

namespace SchemeTheory.Affine.ScalarQuotientSchemePresheaf

open ScalarQuotientPresheaf WeilRestrictionUnits

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)

/-- Actual tensor-unit restriction on every scheme-valued test. -/
def tensorUnitRestrictionPresheaf : schemeTensorUnitsPresheaf R A ⟶
    schemeTensorUnitsPresheaf R B where
  app T := TypeCat.ofHom (algebraUnitRestriction (S := sectionsAlgebra R T.unop) f)
  naturality {T T'} g := by
    apply TypeCat.homEquiv.injective
    funext a
    exact algebraUnitRestriction_naturality f (sectionsMap g.unop) a

/-- Actual scalar-quotient restriction on every scheme-valued test. -/
def algebraRestrictionPresheaf : groupPresheaf R A ⟶ groupPresheaf R B where
  app T := CommGrpCat.ofHom
    (algebraQuotientRestriction (S := sectionsAlgebra R T.unop) f)
  naturality {T T'} g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    refine QuotientGroup.induction_on x fun a => ?_
    change QuotientGroup.mk (algebraUnitRestriction f (unitMap (sectionsMap g.unop) a)) =
      QuotientGroup.mk (unitMap (sectionsMap g.unop) (algebraUnitRestriction f a))
    rw [algebraUnitRestriction_naturality]

/-- Passing from actual tensor units to their literal parameter-scalar classes. -/
def tensorUnitsToScalarQuotient (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    schemeTensorUnitsPresheaf R A ⟶ groupPresheaf R A ⋙ forget CommGrpCat.{u} where
  app T := TypeCat.ofHom (fun a : (sectionsAlgebra R T.unop ⊗[R] A)ˣ =>
    (QuotientGroup.mk a : ScalarQuotient (R := R) (A := A)
      (S := sectionsAlgebra R T.unop)))
  naturality {_ _} _ := rfl

/-- Before sheafification the restriction square is a pullback on all scheme tests. -/
theorem restriction_isPullback {κ : Type} [Nonempty κ] (bB : Basis κ R B) :
    IsPullback (tensorUnitsToScalarQuotient R A) (tensorUnitRestrictionPresheaf f)
      (Functor.whiskerRight (algebraRestrictionPresheaf f) (forget CommGrpCat.{u}))
      (tensorUnitsToScalarQuotient R B) := by
  apply IsPullback.of_forall_isPullback_app
  intro T
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro a b h
    exact toRestrictionUnitFiber_injective (S := sectionsAlgebra R T.unop) f bB
      (Subtype.ext (Prod.ext h.1 h.2))
  · intro x b h
    obtain ⟨a, ha⟩ := toRestrictionUnitFiber_surjective
      (S := sectionsAlgebra R T.unop) f ⟨(x, b), h⟩
    exact ⟨a,
      congrArg (fun p : RestrictionUnitFiber (S := sectionsAlgebra R T.unop) f => p.val.1) ha,
      congrArg (fun p : RestrictionUnitFiber (S := sectionsAlgebra R T.unop) f => p.val.2) ha⟩

/-- The actual Cartesian square survives the universe lift needed on the big site. -/
theorem lifted_restriction_isPullback {κ : Type} [Nonempty κ] (bB : Basis κ R B) :
    IsPullback
      (Functor.whiskerRight (tensorUnitsToScalarQuotient R A) uliftFunctor.{u + 1, u})
      (Functor.whiskerRight (tensorUnitRestrictionPresheaf f) uliftFunctor.{u + 1, u})
      (Functor.whiskerRight
        (Functor.whiskerRight (algebraRestrictionPresheaf f) (forget CommGrpCat.{u}))
        uliftFunctor.{u + 1, u})
      (Functor.whiskerRight (tensorUnitsToScalarQuotient R B) uliftFunctor.{u + 1, u}) :=
  (restriction_isPullback f bB).map
    ((Functor.whiskeringRight (Over (Spec (CommRingCat.of R)))ᵒᵖ
      (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1, u})

/-- Fppf sheafification of the actual restriction square remains Cartesian.
The hypothesis is a nonempty target basis, not an assumed compatibility of representers. -/
theorem sheafified_restriction_isPullback {κ : Type} [Nonempty κ] (bB : Basis κ R B) :
    let H := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))
    IsPullback
      (H.map (Functor.whiskerRight (tensorUnitsToScalarQuotient R A) uliftFunctor.{u + 1, u}))
      (H.map (Functor.whiskerRight (tensorUnitRestrictionPresheaf f) uliftFunctor.{u + 1, u}))
      (H.map (Functor.whiskerRight
        (Functor.whiskerRight (algebraRestrictionPresheaf f) (forget CommGrpCat.{u}))
        uliftFunctor.{u + 1, u}))
      (H.map (Functor.whiskerRight (tensorUnitsToScalarQuotient R B) uliftFunctor.{u + 1, u})) :=
  (lifted_restriction_isPullback f bB).map
    (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1)))

end SchemeTheory.Affine.ScalarQuotientSchemePresheaf
