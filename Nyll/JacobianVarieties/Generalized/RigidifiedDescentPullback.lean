/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedDescent
import Nyll.SchemeTheory.Modules.Functoriality.CanonicalPullbackLegRelation

/-!
# Effective descent expressed as an actual rigidified pullback

The canonical comparison in module descent is identified with the square comparison
used by rigidified pullback. Thus effectivity preserves the supplied local line bundle
and its chosen trivialization through an actual compatible isomorphism.
-/

universe u

open CategoryTheory MonoidalCategory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

/-- Evaluation of a one-member module descent datum on its actual covering scheme. -/
def descentComponentFunctor {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) :
    ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData
      (fun _ : Unit => q) ⥤ Y'.Modules where
  obj d := d.obj ()
  map e := e.hom ()
  map_id _ := rfl
  map_comp _ _ := rfl

variable {X D X' : Scheme.{u}} (i : D ⟶ X) (q : X' ⟶ X)

/-- The comparison used by descent is the actual square comparison used by
chosen-rigidification pullback, including its orientation. -/
theorem restrictCanonicalDescentDataIso_component (L : X.Modules) :
    (descentComponentFunctor (pullback.snd q i)).mapIso
        ((restrictCanonicalDescentDataIso i q).app L) =
      (restrictionComparison q (pullback.snd q i) pullback.condition).app L := by
  apply CategoryTheory.Iso.ext
  exact congrArg CategoryTheory.Iso.hom
    (AlgebraicCurves.Geometry.Sheaves.DescentComparison.square_component_eq
      (pullback.fst q i) q (pullback.snd q i) i pullback.condition L)

namespace DescentData

variable {i q}

/-- The local rigidified bundle supplied by a descent datum. The local
trivialization is the specified datum, followed by the canonical unit comparison. -/
def bundle (d : DescentData i q) : RigidifiedLineBundle (pullback.fst q i) where
  L := d.modules.obj ()
  isInvertible := d.isInvertible ()
  trivialization :=
    (descentComponentFunctor (pullback.snd q i)).mapIso d.trivialization ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso (pullback.snd q i)

/-- Effectivity gives a compatible isomorphism between the pullback of a global
rigidified bundle and the actual local rigidified bundle in the supplied datum. -/
theorem exists_pullback_iso [IsAffineHom q] [Flat q] [Surjective q]
    (d : DescentData i q) :
    ∃ M : RigidifiedLineBundle i,
      Nonempty (Iso (M.pullback q (pullback.snd q i) pullback.condition) d.bundle) := by
  obtain ⟨M, e, he⟩ := d.effective
  refine ⟨M, ⟨{
    toIso := (descentComponentFunctor q).mapIso e
    compatible := ?_
  }⟩⟩
  have h := congrArg
    (fun t => ((descentComponentFunctor (pullback.snd q i)).mapIso t).hom ≫
      (Scheme.Modules.pullbackTensorUnitObjIso (pullback.snd q i)).hom) he
  have hκ := congrArg CategoryTheory.Iso.hom
    (restrictCanonicalDescentDataIso_component i q M.L)
  change (Scheme.Modules.pullback (pullback.fst q i)).map (e.hom.hom ()) ≫
      d.trivialization.hom.hom () ≫
        (Scheme.Modules.pullbackTensorUnitObjIso (pullback.snd q i)).hom =
    (restrictionComparison q (pullback.snd q i) pullback.condition).hom.app M.L ≫
      (Scheme.Modules.pullback (pullback.snd q i)).map M.trivialization.hom ≫
        (Scheme.Modules.pullbackTensorUnitObjIso (pullback.snd q i)).hom
  change ((Scheme.Modules.pullback (pullback.fst q i)).map (e.hom.hom ()) ≫
      d.trivialization.hom.hom ()) ≫
        (Scheme.Modules.pullbackTensorUnitObjIso (pullback.snd q i)).hom =
    (((restrictCanonicalDescentDataIso i q).hom.app M.L).hom () ≫
      (Scheme.Modules.pullback (pullback.snd q i)).map M.trivialization.hom) ≫
        (Scheme.Modules.pullbackTensorUnitObjIso (pullback.snd q i)).hom at h
  change ((restrictCanonicalDescentDataIso i q).hom.app M.L).hom () =
    (restrictionComparison q (pullback.snd q i) pullback.condition).hom.app M.L at hκ
  rw [hκ] at h
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

end DescentData

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
