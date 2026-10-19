/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardForgetful
import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.UnrigidifiedAlgEquivZero
import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Geometric-fibre algebraic triviality for the modulus Picard functor

The zero condition is imposed on the actual underlying line bundle on every
algebraically closed field-valued fibre. Its invariance under relative base twists
and pullback is supplied by the existing unrigidified Picard construction.
The resulting subpresheaf is sheafified in the fppf topology. No representing
scheme or identification with a scheme's identity component is assumed.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {X D : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of R)) (i : D ⟶ X)

/-- The subfunctor whose actual underlying line bundle is algebraically trivial
on every geometric fibre. -/
def modulusPicardZeroSubfunctor : Subfunctor (modulusPicardPresheaf c i) where
  obj T := {x | RelPicard.Unrigidified.classesZero T.unop.hom
    (forgetModulusClasses c i T.unop.hom x)}
  map s := by
    intro x hx
    induction x using Quotient.ind with
    | _ M =>
      exact RelPicard.Unrigidified.fibrewiseZero_pullback
        (⟨s.unop.left, Over.w s.unop⟩ : NeronModelInfra.SchemeHomOver _ _) hx

/-- Membership for an actual bundle is exactly the geometric-fibre condition;
the chosen trivialization is retained and does not replace this condition. -/
theorem classOf_mem_modulusPicardZero {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle (modulusBaseChange c i t)) :
    RigidifiedLineBundle.classOf M ∈ (modulusPicardZeroSubfunctor c i).obj (op (Over.mk t)) ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        RelPicard.IsAlgEquivZero (RelPicard.fibreAt c t s)
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj M.L) := Iff.rfl

/-- Naive chosen-rigidified classes with geometric-fibre algebraic triviality. -/
def modulusPicardZeroPresheaf : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1) :=
  (modulusPicardZeroSubfunctor c i).toFunctor

/-- Forgetting the modulus preserves the actual geometric-fibre zero condition. -/
def forgetModulusZeroPresheaf :
    modulusPicardZeroPresheaf c i ⟶ RelPicard.Unrigidified.zeroPresheaf c where
  app T := TypeCat.ofHom (fun x => ⟨forgetModulusClasses c i T.unop.hom x.1, x.2⟩)
  naturality {T T'} s := by
    apply TypeCat.homEquiv.injective
    funext x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((forgetModulusPresheaf c i).naturality s) x.1

/-- The actual fppf sheaf of modulus-rigidified classes with fibrewise algebraic triviality. -/
def modulusPicardZeroSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))).obj
    (modulusPicardZeroPresheaf c i)

/-- The ordinary relative Picard-zero sheaf is obtained separately by quotienting
base twists and fppf sheafification, without a modulus trivialization. -/
def ordinaryRelativePicardZeroSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))).obj
    (RelPicard.Unrigidified.zeroPresheaf c)

/-- The induced morphism of actual fppf sheaves after forgetting the modulus. -/
def forgetModulusZeroSheaf :
    modulusPicardZeroSheaf c i ⟶ ordinaryRelativePicardZeroSheaf c :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))).map
    (forgetModulusZeroPresheaf c i)

end AlgebraicGeometry.GeneralizedJacobian
