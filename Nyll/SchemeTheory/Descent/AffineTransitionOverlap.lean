/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineTransitionCover
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Native overlaps of descended covering schemes

A Cartesian square of covering maps induces a Cartesian square of their
self-overlaps. Applying this to a coefficient transition identifies the
actual overlap of the recovered cover with the coefficient pullback of the
stage overlap. Both original cover projections and the whole image of the
overlap map are retained. The quasi-compactness needed for open-range descent
follows from an affine covering source and a quasi-separated original model.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineTransitionHom

/-- Self-overlaps of an actual Cartesian covering square remain Cartesian. -/
theorem selfOverlap_isPullback {V O X' X : Scheme.{u}}
    (d : V ⟶ O) (b : V ⟶ X') (a : O ⟶ X) (x : X' ⟶ X)
    (H : IsPullback d b a x) :
    IsPullback (pullback.map b b a a d d x H.w.symm H.w.symm)
      (pullback.snd b b ≫ b) (pullback.snd a a ≫ a) x := by
  let m : pullback b b ⟶ pullback a a :=
    pullback.map b b a a d d x H.w.symm H.w.symm
  have hm₁ : m ≫ pullback.fst a a = pullback.fst b b ≫ d :=
    pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd a a = pullback.snd b b ≫ d :=
    pullback.lift_snd _ _ _
  have ho : IsPullback (m ≫ pullback.fst a a) (pullback.snd b b) a (d ≫ a) := by
    rw [hm₁, H.w]
    exact (IsPullback.of_hasPullback b b).paste_horiz H
  exact (ho.of_right hm₂ (IsPullback.of_hasPullback a a)).paste_vert H

variable {S X : Scheme.{u}} {B C : Over S}

/-- The actual map of coefficient pullbacks is Cartesian over the coefficient map. -/
theorem modelTransition_isPullback (t : B ⟶ C) (f : X ⟶ S) :
    IsPullback ((Over.pullback f).map t).left (pullback.fst B.hom f)
      (pullback.fst C.hom f) t.left := by
  let x : pullback B.hom f ⟶ pullback C.hom f := ((Over.pullback f).map t).left
  have hxs : x ≫ pullback.snd C.hom f = pullback.snd B.hom f :=
    Over.w ((Over.pullback f).map t)
  have hxf : x ≫ pullback.fst C.hom f = pullback.fst B.hom f ≫ t.left :=
    pullback.lift_fst _ _ _
  have ho : IsPullback (x ≫ pullback.snd C.hom f)
      (pullback.fst B.hom f) f (t.left ≫ C.hom) := by
    rw [hxs, Over.w t]
    exact (IsPullback.of_hasPullback B.hom f).flip
  exact ho.of_right hxf (IsPullback.of_hasPullback C.hom f).flip

variable (t : B ⟶ C) (f : X ⟶ S) {V O : Scheme.{u}}
  (b : V ⟶ pullback B.hom f) (a : O ⟶ pullback C.hom f) (d : V ⟶ O)
  (H : IsPullback d b a ((Over.pullback f).map t).left)

/-- The overlap of a recovered cover is the native coefficient pullback of
its stage overlap. The Cartesian covering square may use the original
covering scheme, without replacing it by an isomorphic site object. -/
def selfOverlapCoefficientIso : pullback b b ≅
    pullback t.left (pullback.snd a a ≫ a ≫ pullback.fst C.hom f) := by
  have h := (selfOverlap_isPullback d b a _ H).paste_vert
    (modelTransition_isPullback t f)
  rw [Category.assoc, Category.assoc] at h
  exact h.flip.isoPullback

/-- The overlap isomorphism retains the actual coefficient projection. -/
theorem selfOverlapCoefficientIso_hom_fst :
    (selfOverlapCoefficientIso t f b a d H).hom ≫
        pullback.fst t.left (pullback.snd a a ≫ a ≫ pullback.fst C.hom f) =
      pullback.snd b b ≫ b ≫ pullback.fst B.hom f := by
  exact IsPullback.isoPullback_hom_fst _

/-- The overlap isomorphism retains the literal map of the two coverings. -/
theorem selfOverlapCoefficientIso_hom_snd :
    (selfOverlapCoefficientIso t f b a d H).hom ≫
        pullback.snd t.left (pullback.snd a a ≫ a ≫ pullback.fst C.hom f) =
      pullback.map b b a a d d ((Over.pullback f).map t).left H.w.symm H.w.symm := by
  exact IsPullback.isoPullback_hom_snd _

/-- The first overlap projection is the first original covering map. -/
theorem selfOverlapCoefficientIso_inv_fst :
    (selfOverlapCoefficientIso t f b a d H).inv ≫ pullback.fst b b ≫ d =
      pullback.snd t.left (pullback.snd a a ≫ a ≫ pullback.fst C.hom f) ≫
        pullback.fst a a := by
  let e := selfOverlapCoefficientIso t f b a d H
  let m := pullback.map b b a a d d ((Over.pullback f).map t).left H.w.symm H.w.symm
  have hm : e.inv ≫ m =
      pullback.snd t.left (pullback.snd a a ≫ a ≫ pullback.fst C.hom f) := by
    exact (Iso.inv_comp_eq e).mpr
      (selfOverlapCoefficientIso_hom_snd t f b a d H).symm
  have hmf : m ≫ pullback.fst a a = pullback.fst b b ≫ d :=
    pullback.lift_fst _ _ _
  calc
    e.inv ≫ pullback.fst b b ≫ d = e.inv ≫ m ≫ pullback.fst a a :=
      congrArg (fun k => e.inv ≫ k) hmf.symm
    _ = _ := (Category.assoc e.inv m (pullback.fst a a)).symm.trans
      (congrArg (fun k => k ≫ pullback.fst a a) hm)

/-- The second overlap projection is the second original covering map. -/
theorem selfOverlapCoefficientIso_inv_snd :
    (selfOverlapCoefficientIso t f b a d H).inv ≫ pullback.snd b b ≫ d =
      pullback.snd t.left (pullback.snd a a ≫ a ≫ pullback.fst C.hom f) ≫
        pullback.snd a a := by
  let e := selfOverlapCoefficientIso t f b a d H
  let m := pullback.map b b a a d d ((Over.pullback f).map t).left H.w.symm H.w.symm
  have hm : e.inv ≫ m =
      pullback.snd t.left (pullback.snd a a ≫ a ≫ pullback.fst C.hom f) := by
    exact (Iso.inv_comp_eq e).mpr
      (selfOverlapCoefficientIso_hom_snd t f b a d H).symm
  have hms : m ≫ pullback.snd a a = pullback.snd b b ≫ d :=
    pullback.lift_snd _ _ _
  calc
    e.inv ≫ pullback.snd b b ≫ d = e.inv ≫ m ≫ pullback.snd a a :=
      congrArg (fun k => e.inv ≫ k) hms.symm
    _ = _ := (Category.assoc e.inv m (pullback.snd a a)).symm.trans
      (congrArg (fun k => k ≫ pullback.snd a a) hm)

/-- The coefficient overlap projection has exactly the image of the
original overlap map; consequently open range containment transfers unchanged. -/
theorem selfOverlapCoefficient_range :
    Set.range (pullback.snd t.left (pullback.snd a a ≫ a ≫ pullback.fst C.hom f)) =
      Set.range (pullback.map b b a a d d ((Over.pullback f).map t).left
        H.w.symm H.w.symm) := by
  exact (range_eq_range_of_surjective _ _ (selfOverlapCoefficientIso t f b a d H).hom
    (selfOverlapCoefficientIso_hom_snd t f b a d H)).symm

/-- Restricting a coefficient transition to an open cover supplies the
Cartesian covering square used by the native overlap isomorphism. -/
theorem openCover_transition_isPullback {U : Scheme.{u}} (g : U ⟶ X)
    (W : (pullback C.hom (g ≫ f)).Opens) :
    IsPullback (((Over.pullback (g ≫ f)).map t).left ∣_ W)
      ((((Over.pullback (g ≫ f)).map t).left ⁻¹ᵁ W).ι ≫ modelMap B.hom f g)
      (W.ι ≫ modelMap C.hom f g) ((Over.pullback f).map t).left :=
  (isPullback_morphismRestrict ((Over.pullback (g ≫ f)).map t).left W).paste_vert
    (modelMap_transition_isPullback t f g)

/-- An affine covering model over a quasi-separated source has a
quasi-compact native overlap over its coefficient scheme. -/
theorem selfOverlapCoefficient_quasiCompact [QuasiSeparated f]
    [QuasiSeparatedSpace C.left] [CompactSpace O] :
    QuasiCompact (pullback.snd a a ≫ a ≫ pullback.fst C.hom f) := by
  have : QuasiSeparated (pullback.fst C.hom f) :=
    MorphismProperty.pullback_fst
      (P := show MorphismProperty Scheme.{u} from @QuasiSeparated) C.hom f inferInstance
  have : QuasiSeparatedSpace (pullback C.hom f : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst C.hom f)
  have : QuasiCompact a := inferInstance
  have : CompactSpace (pullback a a : Scheme.{u}) := inferInstance
  infer_instance

end AlgebraicGeometry.AffineTransitionHom
