/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FrameFunctorPullback
import Nyll.JacobianVarieties.Generalized.ModulusUnitBaseChange

/-!
# Base change of the intrinsic scalar-frame sheaf

The module pullback comparison and actual pullback pasting identify the
frames of a base-changed family. Their ratios change by the actual map
on units, so the scalar relation is preserved in both directions. This
gives the comparison of scalar-frame presheaves and their fppf sheaves.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y S S' : Scheme.{u}} (q : Y ⟶ S) (f : S' ⟶ S) (M : Y.Modules)

/-- Pullback pasting as an isomorphism of functors into the original modulus slice. -/
def modulusOverBaseChangeIso :
    Over.pullback (pullback.snd q f) ⋙ Over.map (pullback.fst q f) ≅
      Over.map f ⋙ Over.pullback q :=
  NatIso.ofComponents
    (fun T => Over.isoMk (baseChangeUnitSchemeIso q f T) (baseChangeUnitSchemeIso_snd q f T))
    (fun g => by
      apply Over.OverMorphism.ext
      exact baseChangeUnitSchemeIso_naturality q f g)

/-- The actual frame presheaf of a pulled family is its restriction to the new base. -/
def relativeFramePresheafBaseChangeIso :
    (Over.map f).op ⋙ relativeFramePresheaf q M ≅
      relativeFramePresheaf (pullback.snd q f)
        ((Scheme.Modules.pullback (pullback.fst q f)).obj M) :=
  frameTransportNatIso (pullback.fst q f) M
    (Over.pullback (pullback.snd q f)) (Over.map f ⋙ Over.pullback q)
    (modulusOverBaseChangeIso q f)

/-- The resulting actual equivalence of frames on each parameter scheme. -/
def relativeFrameBaseChangeEquiv (T : Over S') :
    (relativeFramePresheaf q M).obj (op ((Over.map f).obj T)) ≃
      (relativeFramePresheaf (pullback.snd q f)
        ((Scheme.Modules.pullback (pullback.fst q f)).obj M)).obj (op T) :=
  frameTransportEquiv (pullback.fst q f) M ((modulusOverBaseChangeIso q f).app T)

theorem relativeFrameBaseChangeEquiv_naturality {T T' : Over S'} (g : T' ⟶ T)
    (e : (relativeFramePresheaf q M).obj (op ((Over.map f).obj T))) :
    relativeFrameBaseChangeEquiv q f M T'
        ((relativeFramePresheaf q M).map ((Over.map f).map g).op e) =
      (relativeFramePresheaf (pullback.snd q f)
        ((Scheme.Modules.pullback (pullback.fst q f)).obj M)).map g.op
          (relativeFrameBaseChangeEquiv q f M T e) := by
  have h := frameTransportEquiv_naturality (pullback.fst q f) M
    (T := (Over.pullback q).obj ((Over.map f).obj T))
    (T' := (Over.pullback q).obj ((Over.map f).obj T'))
    (U := (Over.pullback (pullback.snd q f)).obj T)
    (U' := (Over.pullback (pullback.snd q f)).obj T')
    ((modulusOverBaseChangeIso q f).app T) ((modulusOverBaseChangeIso q f).app T')
    ((Over.pullback q).map ((Over.map f).map g))
    ((Over.pullback (pullback.snd q f)).map g)
    ((modulusOverBaseChangeIso q f).hom.naturality g) e
  exact (congrArg (relativeFrameBaseChangeEquiv q f M T')
    (relativeFramePresheaf_map_apply q M ((Over.map f).map g) e)).trans
      (h.trans (relativeFramePresheaf_map_apply (pullback.snd q f)
        ((Scheme.Modules.pullback (pullback.fst q f)).obj M) g
        (relativeFrameBaseChangeEquiv q f M T e)).symm)

/-- The change of a frame ratio is the actual pullback of its modulus unit. -/
theorem frameRatio_relativeFrameBaseChangeEquiv (T : Over S')
    (e e' : (relativeFramePresheaf q M).obj (op ((Over.map f).obj T))) :
    frameRatio (Y := ((Over.pullback (pullback.snd q f)).obj T).left)
        (M := (Scheme.Modules.pullback ((Over.pullback (pullback.snd q f)).obj T).hom).obj
          ((Scheme.Modules.pullback (pullback.fst q f)).obj M))
        (relativeFrameBaseChangeEquiv q f M T e)
        (relativeFrameBaseChangeEquiv q f M T e') =
      baseChangeModulusUnitsEquiv q f T
        (frameRatio (Y := ((Over.pullback q).obj ((Over.map f).obj T)).left)
          (M := (Scheme.Modules.pullback ((Over.pullback q).obj ((Over.map f).obj T)).hom).obj M)
          e e') := by
  exact frameRatio_frameTransportEquiv (pullback.fst q f) M
    ((modulusOverBaseChangeIso q f).app T) e e'

/-- The frame base-change equivalence preserves exactly the scalar relation. -/
theorem relativeFrameBaseChangeEquiv_scalarRel (T : Over S')
    (e e' : (relativeFramePresheaf q M).obj (op ((Over.map f).obj T))) :
    (relativeScalarFrameSetoid q M ((Over.map f).obj T)).r e e' ↔
      (relativeScalarFrameSetoid (pullback.snd q f)
        ((Scheme.Modules.pullback (pullback.fst q f)).obj M) T).r
          (relativeFrameBaseChangeEquiv q f M T e) (relativeFrameBaseChangeEquiv q f M T e') := by
  have hr := frameRatio_relativeFrameBaseChangeEquiv q f M T e e'
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (baseChangeModulusUnitsEquiv_scalar q f T a).symm.trans
      ((congrArg (baseChangeModulusUnitsEquiv q f T) ha).trans hr.symm)⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (baseChangeModulusUnitsEquiv q f T).injective
      ((baseChangeModulusUnitsEquiv_scalar q f T a).trans (ha.trans hr))⟩

/-- Actual scalar-frame classes before and after base change. -/
def scalarFrameBaseChangeEquiv (T : Over S') :
    (scalarFramePresheaf q M).obj (op ((Over.map f).obj T)) ≃
      (scalarFramePresheaf (pullback.snd q f)
        ((Scheme.Modules.pullback (pullback.fst q f)).obj M)).obj (op T) :=
  Quotient.congr (relativeFrameBaseChangeEquiv q f M T)
    (relativeFrameBaseChangeEquiv_scalarRel q f M T)

theorem scalarFrameBaseChangeEquiv_naturality {T T' : Over S'} (g : T' ⟶ T)
    (x : (scalarFramePresheaf q M).obj (op ((Over.map f).obj T))) :
    scalarFrameBaseChangeEquiv q f M T'
        ((scalarFramePresheaf q M).map ((Over.map f).map g).op x) =
      (scalarFramePresheaf (pullback.snd q f)
        ((Scheme.Modules.pullback (pullback.fst q f)).obj M)).map g.op
          (scalarFrameBaseChangeEquiv q f M T x) := by
  induction x using Quotient.ind with
  | _ e =>
    exact congrArg (fun e : (relativeFramePresheaf (pullback.snd q f)
      ((Scheme.Modules.pullback (pullback.fst q f)).obj M)).obj (op T') =>
        Quotient.mk (relativeScalarFrameSetoid (pullback.snd q f)
          ((Scheme.Modules.pullback (pullback.fst q f)).obj M) T') e)
      (relativeFrameBaseChangeEquiv_naturality q f M g e)

/-- The scalar-frame quotient comparison is natural on arbitrary parameter schemes. -/
def scalarFramePresheafBaseChangeIso :
    (Over.map f).op ⋙ scalarFramePresheaf q M ≅
      scalarFramePresheaf (pullback.snd q f)
        ((Scheme.Modules.pullback (pullback.fst q f)).obj M) :=
  NatIso.ofComponents (fun T => (scalarFrameBaseChangeEquiv q f M T.unop).toIso)
    (fun g => TypeCat.homEquiv.injective
      (funext fun x => scalarFrameBaseChangeEquiv_naturality q f M g.unop x))

/-- The scalar-frame comparison in the value universe used for fppf sheafification. -/
def liftedScalarFramePresheafBaseChangeIso :
    (Over.map f).op ⋙ liftedScalarFramePresheaf q M ≅
      liftedScalarFramePresheaf (pullback.snd q f)
        ((Scheme.Modules.pullback (pullback.fst q f)).obj M) :=
  (Functor.associator (Over.map f).op (scalarFramePresheaf q M)
    CategoryTheory.uliftFunctor.{u + 1, u}).symm ≪≫
      Functor.isoWhiskerRight (scalarFramePresheafBaseChangeIso q f M)
        CategoryTheory.uliftFunctor.{u + 1, u}

/-- The intrinsic scalar-frame sheaf agrees with the frame sheaf of the actual pulled family. -/
def scalarFrameSheafBaseChangeIso :
    (Scheme.fppfTopology.overMapPullback (Type (u + 1)) f).obj (scalarFrameSheaf q M) ≅
      scalarFrameSheaf (pullback.snd q f) ((Scheme.Modules.pullback (pullback.fst q f)).obj M) :=
  ((Functor.pushforwardContinuousSheafificationCompatibility
    (G := Over.map f) (A := Type (u + 1))
    (J := Scheme.fppfTopology.over S') (K := Scheme.fppfTopology.over S)).app
      (liftedScalarFramePresheaf q M)).symm ≪≫
        (presheafToSheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
          (liftedScalarFramePresheafBaseChangeIso q f M)

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
