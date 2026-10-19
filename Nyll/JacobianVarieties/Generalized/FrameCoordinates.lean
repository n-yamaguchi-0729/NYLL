/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUnitFunctor

/-!
# Natural scalar-unit coordinates supplied by an actual frame

A chosen frame of the fixed module gives coordinates on every base change.
These coordinates commute with restriction on arbitrary test schemes, hence
identify the actual fppf scalar-frame sheaf with the scalar-unit sheaf on
this trivialized family. Changes of reference frame remain translations.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y : Scheme.{u}} {M : Y.Modules}

/-- A reference frame pulled coherently to every scheme over its source. -/
def referenceFrame (e : M ≅ 𝟙_ Y.Modules) (T : Over Y) :
    (Scheme.Modules.pullback T.hom).obj M ≅ 𝟙_ T.left.Modules :=
  frameMap M (Over.mkIdTerminal.from T) (pullbackFrame (𝟙 Y) e)

theorem referenceFrame_naturality (e : M ≅ 𝟙_ Y.Modules)
    {T T' : Over Y} (f : T' ⟶ T) :
    frameMap M f (referenceFrame e T) = referenceFrame e T' := by
  change frameMap M f (frameMap M (Over.mkIdTerminal.from T) _) = _
  rw [frameMap_comp]
  exact congrArg (fun g : T' ⟶ Over.mk (𝟙 Y) =>
    frameMap M g (pullbackFrame (𝟙 Y) e)) (Over.mkIdTerminal.hom_ext _ _)

/-- The actual ratio of restricted frames is restriction of their ratio. -/
theorem frameRatio_frameMap {T T' : Over Y} (f : T' ⟶ T)
    (e e' : (Scheme.Modules.pullback T.hom).obj M ≅ 𝟙_ T.left.Modules) :
    frameRatio (frameMap M f e) (frameMap M f e') =
      Units.map f.left.appTop.hom.toMonoidHom (frameRatio e e') := by
  change frameRatio ((frameComparison M f).symm ≪≫ pullbackFrame f.left e)
    ((frameComparison M f).symm ≪≫ pullbackFrame f.left e') = _
  rw [frameRatio_precomp]
  exact frameRatio_pullbackFrame f.left e e'

variable {S : Scheme.{u}} (q : Y ⟶ S) (e₀ : M ≅ 𝟙_ Y.Modules)

/-- Coordinates of the actual frame quotient on an arbitrary parameter scheme. -/
def scalarFrameCoordinates (T : Over S) :
    (scalarFramePresheaf q M).obj (op T) ≃
      ModulusUnits q T ⧸ modulusScalars q T :=
  scalarFrameClassesEquiv (modulusProjection q T)
    (referenceFrame e₀ ((Over.pullback q).obj T))

theorem scalarFrameCoordinates_naturality {T T' : Over S} (f : T' ⟶ T)
    (x : (scalarFramePresheaf q M).obj (op T)) :
    scalarFrameCoordinates q e₀ T' ((scalarFramePresheaf q M).map f.op x) =
      modulusUnitQuotientMap q f (scalarFrameCoordinates q e₀ T x) := by
  induction x using Quotient.ind with
  | _ e =>
    change QuotientGroup.mk
        (frameRatio (referenceFrame e₀ ((Over.pullback q).obj T'))
          (frameMap M ((Over.pullback q).map f) e)) =
      QuotientGroup.mk (modulusUnitMap q f
        (frameRatio (referenceFrame e₀ ((Over.pullback q).obj T)) e))
    rw [← referenceFrame_naturality e₀ ((Over.pullback q).map f)]
    exact congrArg (fun a : ModulusUnits q T' =>
      (QuotientGroup.mk a : ModulusUnits q T' ⧸ modulusScalars q T'))
        (frameRatio_frameMap ((Over.pullback q).map f)
          (referenceFrame e₀ ((Over.pullback q).obj T)) e)

/-- The coordinates form a natural isomorphism, not merely pointwise bijections. -/
def scalarFrameCoordinatesIso : scalarFramePresheaf q M ≅
    modulusUnitQuotientPresheaf q ⋙ forget CommGrpCat.{u} :=
  NatIso.ofComponents (fun T => (scalarFrameCoordinates q e₀ T.unop).toIso)
    (fun f => TypeCat.homEquiv.injective
      (funext fun x => scalarFrameCoordinates_naturality q e₀ f.unop x))

/-- The lifted presheaf of actual scalar-unit classes on the modulus. -/
def liftedModulusUnitQuotientPresheaf : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  (modulusUnitQuotientPresheaf q ⋙ forget CommGrpCat.{u}) ⋙
    CategoryTheory.uliftFunctor.{u + 1, u}

/-- The actual fppf sheaf of modulus units modulo parameter scalars. -/
def modulusUnitQuotientSheaf : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
    (liftedModulusUnitQuotientPresheaf q)

/-- An actual reference frame identifies the two fppf sheaves. -/
def scalarFrameSheafCoordinatesIso :
    scalarFrameSheaf q M ≅ modulusUnitQuotientSheaf q :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).mapIso
    (Functor.isoWhiskerRight (scalarFrameCoordinatesIso q e₀)
      CategoryTheory.uliftFunctor.{u + 1, u})

/-- The transition between two local coordinate systems is the actual frame ratio. -/
theorem scalarFrameCoordinates_change (e₁ : M ≅ 𝟙_ Y.Modules)
    (T : Over S) (x : (scalarFramePresheaf q M).obj (op T)) :
    scalarFrameCoordinates q e₁ T x =
      QuotientGroup.mk (frameRatio (referenceFrame e₁ ((Over.pullback q).obj T))
        (referenceFrame e₀ ((Over.pullback q).obj T))) *
          scalarFrameCoordinates q e₀ T x :=
  scalarFrameClassesEquiv_change _ _ _ x

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
