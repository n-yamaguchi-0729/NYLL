/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FrameCoordinates
import Nyll.SchemeTheory.WeilRestriction.BaseChange
import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Base change of the intrinsic modulus-unit sheaf

Actual pullback pasting identifies the base-changed modulus and its units
on every parameter scheme. It preserves the exact scalar subgroup, giving
an isomorphism of group presheaves. Restriction to a slice commutes with
fppf sheafification, so this comparison descends to the intrinsic sheaves.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open SchemeTheory.WeilRestriction

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y S S' : Scheme.{u}} (q : Y ⟶ S)

@[reassoc] theorem modulusPullbackMap_fst {T T' : Over S} (g : T' ⟶ T) :
    ((Over.pullback q).map g).left ≫ modulusProjection q T =
      modulusProjection q T' ≫ g.left := pullback.lift_fst _ _ _

@[reassoc] theorem modulusPullbackMap_snd {T T' : Over S} (g : T' ⟶ T) :
    ((Over.pullback q).map g).left ≫ ((Over.pullback q).obj T).hom =
      ((Over.pullback q).obj T').hom := ((Over.pullback q).map g).w

variable (f : S' ⟶ S)

/-- The actual pullback-pasting comparison on a parameter scheme. -/
def baseChangeUnitSchemeIso (T : Over S') :
    ((Over.pullback (pullback.snd q f)).obj T).left ≅
      ((Over.pullback q).obj ((Over.map f).obj T)).left :=
  tensorBaseChangeLeftIso f (Over.mk q) T

@[reassoc] theorem baseChangeUnitSchemeIso_fst (T : Over S') :
    (baseChangeUnitSchemeIso q f T).hom ≫ modulusProjection q ((Over.map f).obj T) =
      modulusProjection (pullback.snd q f) T := tensorBaseChangeLeftIso_hom_fst f (Over.mk q) T

@[reassoc] theorem baseChangeUnitSchemeIso_snd (T : Over S') :
    (baseChangeUnitSchemeIso q f T).hom ≫ ((Over.pullback q).obj ((Over.map f).obj T)).hom =
      ((Over.pullback (pullback.snd q f)).obj T).hom ≫ pullback.fst q f :=
  tensorBaseChangeLeftIso_hom_snd f (Over.mk q) T

theorem baseChangeUnitSchemeIso_naturality {T T' : Over S'} (g : T' ⟶ T) :
    ((Over.pullback (pullback.snd q f)).map g).left ≫ (baseChangeUnitSchemeIso q f T).hom =
      (baseChangeUnitSchemeIso q f T').hom ≫ ((Over.pullback q).map ((Over.map f).map g)).left := by
  apply pullback.hom_ext
  · change _ ≫ modulusProjection q ((Over.map f).obj T) =
      _ ≫ modulusProjection q ((Over.map f).obj T)
    simp only [Category.assoc, baseChangeUnitSchemeIso_fst, modulusPullbackMap_fst]
    rw [← Category.assoc, baseChangeUnitSchemeIso_fst]
    rfl
  · change _ ≫ ((Over.pullback q).obj ((Over.map f).obj T)).hom =
      _ ≫ ((Over.pullback q).obj ((Over.map f).obj T)).hom
    simp only [Category.assoc, baseChangeUnitSchemeIso_snd,
      modulusPullbackMap_snd, modulusPullbackMap_snd_assoc]

/-- Pullback pasting gives the actual equivalence of modulus units. -/
def baseChangeModulusUnitsEquiv (T : Over S') :
    ModulusUnits q ((Over.map f).obj T) ≃* ModulusUnits (pullback.snd q f) T :=
  Units.mapEquiv (Scheme.Γ.mapIso
    (baseChangeUnitSchemeIso q f T).op).commRingCatIsoToRingEquiv.toMulEquiv

theorem baseChangeModulusUnitsEquiv_scalar (T : Over S') (a : Γ(T.left, ⊤)ˣ) :
    baseChangeModulusUnitsEquiv q f T
        (Units.map (modulusProjection q ((Over.map f).obj T)).appTop.hom.toMonoidHom a) =
      Units.map (modulusProjection (pullback.snd q f) T).appTop.hom.toMonoidHom a := by
  apply Units.ext
  exact congrArg (fun g : Γ(T.left, ⊤) ⟶
    Γ(((Over.pullback (pullback.snd q f)).obj T).left, ⊤) => g (a : Γ(T.left, ⊤)))
      (congrArg Scheme.Hom.appTop (baseChangeUnitSchemeIso_fst q f T))

theorem baseChangeModulusUnitsEquiv_naturality {T T' : Over S'} (g : T' ⟶ T)
    (a : ModulusUnits q ((Over.map f).obj T)) :
    baseChangeModulusUnitsEquiv q f T'
        (modulusUnitMap q ((Over.map f).map g) a) =
      modulusUnitMap (pullback.snd q f) g (baseChangeModulusUnitsEquiv q f T a) := by
  apply Units.ext
  exact (congrArg (fun h : Γ(((Over.pullback q).obj ((Over.map f).obj T)).left, ⊤) ⟶
    Γ(((Over.pullback (pullback.snd q f)).obj T').left, ⊤) =>
      h (a : Γ(((Over.pullback q).obj ((Over.map f).obj T)).left, ⊤)))
        (congrArg Scheme.Hom.appTop (baseChangeUnitSchemeIso_naturality q f g))).symm

/-- The actual scalar relation is preserved by pullback pasting. -/
def baseChangeModulusUnitQuotientEquiv (T : Over S') :
    (modulusUnitQuotientPresheaf q).obj (op ((Over.map f).obj T)) ≃*
      (modulusUnitQuotientPresheaf (pullback.snd q f)).obj (op T) :=
  QuotientGroup.congr _ _ (baseChangeModulusUnitsEquiv q f T) (by
    ext a
    constructor
    · rintro ⟨x, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (baseChangeModulusUnitsEquiv_scalar q f T s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨Units.map
        (modulusProjection q ((Over.map f).obj T)).appTop.hom.toMonoidHom s,
        ⟨s, rfl⟩, baseChangeModulusUnitsEquiv_scalar q f T s⟩)

theorem baseChangeModulusUnitQuotientEquiv_naturality {T T' : Over S'} (g : T' ⟶ T)
    (x : (modulusUnitQuotientPresheaf q).obj (op ((Over.map f).obj T))) :
    baseChangeModulusUnitQuotientEquiv q f T'
        (modulusUnitQuotientMap q ((Over.map f).map g) x) =
      modulusUnitQuotientMap (pullback.snd q f) g (baseChangeModulusUnitQuotientEquiv q f T x) := by
  refine QuotientGroup.induction_on x fun a => ?_
  exact congrArg (fun a : ModulusUnits (pullback.snd q f) T' =>
    (QuotientGroup.mk a : ModulusUnits (pullback.snd q f) T' ⧸
      modulusScalars (pullback.snd q f) T')) (baseChangeModulusUnitsEquiv_naturality q f g a)

/-- Base change of the intrinsic group presheaf, on arbitrary test schemes. -/
def modulusUnitPresheafBaseChangeIso :
    (Over.map f).op ⋙ modulusUnitQuotientPresheaf q ≅
      modulusUnitQuotientPresheaf (pullback.snd q f) :=
  NatIso.ofComponents (fun T => (baseChangeModulusUnitQuotientEquiv q f T.unop).toCommGrpIso)
    (fun g => by
      apply ConcreteCategory.hom_ext
      exact baseChangeModulusUnitQuotientEquiv_naturality q f g.unop)

/-- The same comparison in the value universe of the big fppf site. -/
def liftedModulusUnitPresheafBaseChangeIso :
    (Over.map f).op ⋙ liftedModulusUnitQuotientPresheaf q ≅
      liftedModulusUnitQuotientPresheaf (pullback.snd q f) :=
  NatIso.ofComponents (fun T =>
    (Equiv.ulift.trans (baseChangeModulusUnitQuotientEquiv q f T.unop).toEquiv |>.trans
      Equiv.ulift.symm).toIso)
    (fun g => by
      apply TypeCat.homEquiv.injective
      funext x
      apply ULift.ext
      exact baseChangeModulusUnitQuotientEquiv_naturality q f g.unop x.down)

/-- The intrinsic fppf modulus-unit sheaf commutes with arbitrary base change. -/
def modulusUnitSheafBaseChangeIso :
    (Scheme.fppfTopology.overMapPullback (Type (u + 1)) f).obj (modulusUnitQuotientSheaf q) ≅
      modulusUnitQuotientSheaf (pullback.snd q f) :=
  ((Functor.pushforwardContinuousSheafificationCompatibility
    (G := Over.map f) (A := Type (u + 1))
    (J := Scheme.fppfTopology.over S') (K := Scheme.fppfTopology.over S)).app
      (liftedModulusUnitQuotientPresheaf q)).symm ≪≫
        (presheafToSheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
          (liftedModulusUnitPresheafBaseChangeIso q f)

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
