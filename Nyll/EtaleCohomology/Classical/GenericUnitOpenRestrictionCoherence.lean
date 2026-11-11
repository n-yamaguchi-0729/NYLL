/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.GenericUnitOpenRestriction
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Composition of the actual generic-unit chart comparisons

The generic-point maps of nested integral opens compose because their
composites with the original generic-point morphism agree. The existing
cartesian quotient pasting formula therefore applies to the original
generic-unit quotients, on every section of every étale object.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleCohomology

variable {X U V : Scheme.{u}} [IsIntegral X] [IsIntegral U] [IsIntegral V]
  (i : U ⟶ X) [IsOpenImmersion i] (j : V ⟶ U) [IsOpenImmersion j]

private theorem genericPointOpenIso_hom_comp :
    (genericPointOpenIso j).hom ≫ (genericPointOpenIso i).hom =
      (genericPointOpenIso (j ≫ i)).hom := by
  apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
  calc
    ((genericPointOpenIso j).hom ≫ (genericPointOpenIso i).hom) ≫
        X.fromSpecStalk (genericPoint X) =
      (genericPointOpenIso j).hom ≫
        (U.fromSpecStalk (genericPoint U) ≫ i) := by
      rw [Category.assoc, ← (genericPointOpenIsPullback i).w]
    _ = (V.fromSpecStalk (genericPoint V) ≫ j) ≫ i := by
      rw [← Category.assoc, ← (genericPointOpenIsPullback j).w]
    _ = V.fromSpecStalk (genericPoint V) ≫ (j ≫ i) := Category.assoc _ _ _
    _ = (genericPointOpenIso (j ≫ i)).hom ≫
        X.fromSpecStalk (genericPoint X) := (genericPointOpenIsPullback (j ≫ i)).w

/-- The original generic-unit quotient comparisons compose along nested
integral open charts. This is a sheaf-morphism identity, so it applies to
arbitrary sections on the smaller chart. -/
theorem etaleRestrictionGenericUnitQuotientIso_comp :
    (etaleRestriction j AddCommGrpCat.{u}).map
        (etaleRestrictionGenericUnitQuotientIso i).hom ≫
      (etaleRestrictionGenericUnitQuotientIso j).hom =
    (etaleRestrictionCompIso j i AddCommGrpCat.{u}).hom.app
        (etaleGenericUnitQuotient X) ≫
      (etaleRestrictionGenericUnitQuotientIso (j ≫ i)).hom := by
  have h := etaleRestrictionUnitQuotient_paste i j
    (X.fromSpecStalk (genericPoint X))
    (U.fromSpecStalk (genericPoint U)) (genericPointOpenIso i).hom
    (V.fromSpecStalk (genericPoint V)) (genericPointOpenIso j).hom
    (genericPointOpenIsPullback i) (genericPointOpenIsPullback j)
  simpa only [genericPointOpenIso_hom_comp i j,
    etaleRestrictionGenericUnitQuotientIso, etaleGenericUnitQuotient] using h

end EtaleCohomology
