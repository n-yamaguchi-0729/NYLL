/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FrameFunctor
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The intrinsic scalar-frame functor of a family over a finite modulus

For a fixed module on `Y` over `S`, pull back to every parameter scheme and
take its actual frames modulo units of that parameter scheme. Pullback
preserves precisely this scalar relation and obeys the functor laws. The
fppf sheafification retains the resulting local gluing data.

This definition applies in particular to a Poincaré bundle restricted to
the modulus. It does not assume a representing scheme or global frame.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y S : Scheme.{u}} (q : Y ⟶ S) (M : Y.Modules)

/-- The actual frame presheaf after changing parameters over the base. -/
def relativeFramePresheaf : (Over S)ᵒᵖ ⥤ Type u :=
  (Over.pullback q).op ⋙ framePresheaf M

theorem relativeFramePresheaf_map_apply {T T' : Over S} (f : T' ⟶ T)
    (e : (Scheme.Modules.pullback ((Over.pullback q).obj T).hom).obj M ≅
      𝟙_ ((Over.pullback q).obj T).left.Modules) :
    (relativeFramePresheaf q M).map f.op e =
      frameMap M ((Over.pullback q).map f) e := rfl

/-- The projection of the actual base-changed modulus to its parameter scheme. -/
abbrev modulusProjection (T : Over S) : ((Over.pullback q).obj T).left ⟶ T.left :=
  pullback.fst T.hom q

/-- The scalar relation on each test scheme uses its own global units. -/
def relativeScalarFrameSetoid (T : Over S) :
    Setoid ((relativeFramePresheaf q M).obj (op T)) :=
  scalarFrameSetoid (modulusProjection q T)
    ((Scheme.Modules.pullback ((Over.pullback q).obj T).hom).obj M)

/-- The parameter restriction maps preserve the actual base-scalar relation. -/
theorem relativeFrameMap_scalarRel {T T' : Over S} (f : T' ⟶ T)
    {e e' : (relativeFramePresheaf q M).obj (op T)}
    (h : (relativeScalarFrameSetoid q M T).r e e') :
    (relativeScalarFrameSetoid q M T').r
      ((relativeFramePresheaf q M).map f.op e)
      ((relativeFramePresheaf q M).map f.op e') := by
  have hw : ((Over.pullback q).map f).left ≫ modulusProjection q T =
      modulusProjection q T' ≫ f.left := by
    simp only [Over.pullback_map_left, modulusProjection, pullback.lift_fst]
  have hp := frameMap_scalarRel M
    (T := (Over.pullback q).obj T) (T' := (Over.pullback q).obj T')
    ((Over.pullback q).map f) (q := modulusProjection q T)
    (q' := modulusProjection q T') f.left hw (e := e) (e' := e') h
  exact (congrArg₂ (relativeScalarFrameSetoid q M T').r
    (relativeFramePresheaf_map_apply q M f e)
    (relativeFramePresheaf_map_apply q M f e')).mpr hp

/-- Frames of the fixed family modulo scalar units on the parameter scheme. -/
def scalarFramePresheaf : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Quotient (relativeScalarFrameSetoid q M T.unop)
  map {T T'} f := TypeCat.ofHom (Quotient.map
    ((relativeFramePresheaf q M).map f)
    (fun _ _ h => relativeFrameMap_scalarRel q M f.unop h))
  map_id T := TypeCat.homEquiv.injective (funext fun x => by
    induction x using Quotient.ind with
    | _ e =>
      change Quotient.mk _ ((relativeFramePresheaf q M).map (𝟙 T) e) = Quotient.mk _ e
      rw [CategoryTheory.Functor.map_id]
      rfl)
  map_comp {T T' T''} f g := TypeCat.homEquiv.injective (funext fun x => by
    induction x using Quotient.ind with
    | _ e =>
      change Quotient.mk _ ((relativeFramePresheaf q M).map (f ≫ g) e) =
        Quotient.mk _ ((relativeFramePresheaf q M).map g
          ((relativeFramePresheaf q M).map f e))
      rw [CategoryTheory.Functor.map_comp]
      rfl)

/-- The same concrete quotient presheaf in the value universe of the big site. -/
def liftedScalarFramePresheaf : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  scalarFramePresheaf q M ⋙ CategoryTheory.uliftFunctor.{u + 1, u}

/-- The actual fppf scalar-frame sheaf of the fixed module family. -/
def scalarFrameSheaf : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
    (liftedScalarFramePresheaf q M)

/-- Actual scalar-frame classes map canonically into the fppf frame sheaf. -/
def toScalarFrameSheaf : liftedScalarFramePresheaf q M ⟶ (scalarFrameSheaf q M).obj :=
  toSheafify (Scheme.fppfTopology.over S) (liftedScalarFramePresheaf q M)

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
