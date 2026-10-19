/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFunctoriality
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationSchemeComposition
import Nyll.SchemeTheory.LocalGeometry.PointedStalkMap
import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Naturality of the actual strict local models

A scheme morphism and a specified square of field-valued points induce a
local homomorphism between the actual geometric stalks of their ordinary
local rings. Both the given coefficient-field map and the original scheme
morphism are preserved.

Composing a previously chosen generic lift with this homomorphism gives
the generic lift on the target scheme. The equality on the ordinary local
ring and the full scheme triangle are proved for this exact composite.
No new generic lift is chosen.

This constructs the local-model diagram in Stacks Project, Lemma 58.16.1,
https://stacks.math.columbia.edu/tag/0BUP. The resulting fundamental-group
square also requires the proper closed-fiber comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {X Y : Scheme.{u}} {Ωx Ωy : Type u} [Field Ωx] [Field Ωy]
  (f : X ⟶ Y) (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ Y)
  (ι : Ωy →+* Ωx)
  (h : x ≫ f = Spec.map (CommRingCat.ofHom ι) ≫ y)

private theorem localGeometricStalkMap_square :
    Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo x).hom) ≫
        Spec.map (CommRingCat.ofHom (Scheme.pointedStalkMap f x y ι h).hom) =
      Spec.map (CommRingCat.ofHom ι) ≫
        Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo y).hom) := by
  let Rx : CommRingCat.{u} := X.presheaf.stalk (x (closedPoint Ωx))
  let Ry : CommRingCat.{u} := Y.presheaf.stalk (y (closedPoint Ωy))
  let a : Ry ⟶ Rx := Scheme.pointedStalkMap f x y ι h
  let sx : Rx ⟶ CommRingCat.of Ωx := Scheme.stalkClosedPointTo x
  let sy : Ry ⟶ CommRingCat.of Ωy := Scheme.stalkClosedPointTo y
  have he : a ≫ sx = sy ≫ CommRingCat.ofHom ι :=
    Scheme.pointedStalkMap_evaluation f x y ι h
  have hSpec := congrArg
    (fun b : Y.presheaf.stalk (y (closedPoint Ωy)) ⟶ CommRingCat.of Ωx => Spec.map b) he
  simpa only [CommRingCat.ofHom_hom] using
    (Spec.map_comp a sx).symm.trans (hSpec.trans (Spec.map_comp sy (CommRingCat.ofHom ι)))

/-- The local homomorphism of actual strict local models induced by the
scheme morphism and the specified coefficient-field square. -/
def localGeometricStalkMap :
    geometricStalk (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo y).hom)) ⟶
      geometricStalk (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo x).hom)) :=
  geometricStalkMap
    (Spec.map (CommRingCat.ofHom (Scheme.pointedStalkMap f x y ι h).hom))
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo x).hom))
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo y).hom))
    ι (localGeometricStalkMap_square f x y ι h)

instance localGeometricStalkMap_isLocalHom :
    IsLocalHom (localGeometricStalkMap f x y ι h).hom := by
  unfold localGeometricStalkMap
  infer_instance

/-- Evaluation at the two special geometric points preserves the
original coefficient-field homomorphism. -/
theorem localGeometricStalkMap_evaluation :
    localGeometricStalkMap f x y ι h ≫
        geometricStalkEvaluation
          (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo x).hom)) =
      geometricStalkEvaluation
          (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo y).hom)) ≫
        CommRingCat.ofHom ι :=
  geometricStalkMap_evaluation
    (Spec.map (CommRingCat.ofHom (Scheme.pointedStalkMap f x y ι h).hom))
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo x).hom))
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo y).hom))
    ι (localGeometricStalkMap_square f x y ι h)

/-- The strict-local map extends the actual homomorphism on ordinary
stalks, including the identification obtained from the field square. -/
theorem localGeometricStalkMap_comp_structure :
    (localGeometricStalkMap f x y ι h).hom.comp
        (geometricStalkStructureMap (Scheme.stalkClosedPointTo y).hom) =
      (geometricStalkStructureMap (Scheme.stalkClosedPointTo x).hom).comp
        (Scheme.pointedStalkMap f x y ι h).hom :=
  geometricStalkMap_affine_comp_structure
    (Scheme.pointedStalkMap f x y ι h).hom
    (Scheme.stalkClosedPointTo x).hom (Scheme.stalkClosedPointTo y).hom
    ι (localGeometricStalkMap_square f x y ι h)

/-- The actual strict local models form a commuting square over the
original scheme morphism. -/
theorem localGeometricStalkMap_toScheme :
    Spec.map (localGeometricStalkMap f x y ι h) ≫ localGeometricStalkToScheme y =
      localGeometricStalkToScheme x ≫ f := by
  let Rx : CommRingCat.{u} := X.presheaf.stalk (x (closedPoint Ωx))
  let Ry : CommRingCat.{u} := Y.presheaf.stalk (y (closedPoint Ωy))
  let Hx : CommRingCat.{u} :=
    geometricStalk (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo x).hom))
  let Hy : CommRingCat.{u} :=
    geometricStalk (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo y).hom))
  let a : Ry ⟶ Rx := Scheme.pointedStalkMap f x y ι h
  let cx : Rx ⟶ Hx := CommRingCat.ofHom
    (geometricStalkStructureMap (Scheme.stalkClosedPointTo x).hom)
  let cy : Ry ⟶ Hy := CommRingCat.ofHom
    (geometricStalkStructureMap (Scheme.stalkClosedPointTo y).hom)
  let M : Hy ⟶ Hx := localGeometricStalkMap f x y ι h
  let qx : Spec Rx ⟶ X := X.fromSpecStalk (x (closedPoint Ωx))
  let qy : Spec Ry ⟶ Y := Y.fromSpecStalk (y (closedPoint Ωy))
  have hcat : cy ≫ M = a ≫ cx :=
    congrArg CommRingCat.ofHom (localGeometricStalkMap_comp_structure f x y ι h)
  have hFrom : Spec.map a ≫ qy = qx ≫ f := Scheme.pointedStalkMap_fromSpecStalk f x y ι h
  change Spec.map M ≫ (Spec.map cy ≫ qy) = (Spec.map cx ≫ qx) ≫ f
  calc
    Spec.map M ≫ (Spec.map cy ≫ qy) = Spec.map (cy ≫ M) ≫ qy := by
      rw [Spec.map_comp, Category.assoc]
    _ = Spec.map (a ≫ cx) ≫ qy :=
      congrArg (fun b : Ry ⟶ Hx => Spec.map b ≫ qy) hcat
    _ = Spec.map cx ≫ (qx ≫ f) := by
      rw [Spec.map_comp, Category.assoc, hFrom]
    _ = (Spec.map cx ≫ qx) ≫ f := (Category.assoc _ _ _).symm

/-- A chosen geometric specialization is sent to the literal composite
with the strict-local map. This composite has the required ordinary-stalk
values and preserves the original generic geometric point over the target
scheme. -/
theorem localGeometricStalkMap_specializationLift {Ξ : Type u} [Field Ξ]
    (t : Spec (.of Ξ) ⟶ X) (ht : t (closedPoint Ξ) ⤳ x (closedPoint Ωx))
    (ψ : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo x).hom)) →+* Ξ)
    (hψ : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo x).hom) =
      (Scheme.stalkSpecializationToField (x (closedPoint Ωx)) t ht).hom) :
    (ψ.comp (localGeometricStalkMap f x y ι h).hom).comp
        (geometricStalkStructureMap (Scheme.stalkClosedPointTo y).hom) =
      (Scheme.stalkSpecializationToField (y (closedPoint Ωy)) (t ≫ f)
        (Scheme.specializes_of_fieldPointSquare f x y ι h t ht)).hom ∧
    Spec.map (CommRingCat.ofHom (ψ.comp (localGeometricStalkMap f x y ι h).hom)) ≫
        localGeometricStalkToScheme y = t ≫ f := by
  have hRing : (ψ.comp (localGeometricStalkMap f x y ι h).hom).comp
        (geometricStalkStructureMap (Scheme.stalkClosedPointTo y).hom) =
      (Scheme.stalkSpecializationToField (y (closedPoint Ωy)) (t ≫ f)
        (Scheme.specializes_of_fieldPointSquare f x y ι h t ht)).hom := by
    rw [RingHom.comp_assoc, localGeometricStalkMap_comp_structure,
      ← RingHom.comp_assoc, hψ]
    exact congrArg CommRingCat.Hom.hom
      (Scheme.pointedStalkMap_specializationToField f x y ι h t ht)
  refine ⟨hRing, ?_⟩
  let R : CommRingCat.{u} := Y.presheaf.stalk (y (closedPoint Ωy))
  let H : CommRingCat.{u} :=
    geometricStalk (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo y).hom))
  let c : R ⟶ H := CommRingCat.ofHom
    (geometricStalkStructureMap (Scheme.stalkClosedPointTo y).hom)
  let φ : H ⟶ CommRingCat.of Ξ :=
    CommRingCat.ofHom (ψ.comp (localGeometricStalkMap f x y ι h).hom)
  let p : R ⟶ CommRingCat.of Ξ :=
    Scheme.stalkSpecializationToField (y (closedPoint Ωy)) (t ≫ f)
      (Scheme.specializes_of_fieldPointSquare f x y ι h t ht)
  let q : Spec R ⟶ Y := Y.fromSpecStalk (y (closedPoint Ωy))
  have hcat : c ≫ φ = p := congrArg CommRingCat.ofHom hRing
  change Spec.map φ ≫ (Spec.map c ≫ q) = t ≫ f
  rw [← Category.assoc, ← Spec.map_comp, hcat]
  exact Scheme.Spec_stalkSpecializationToField_fromSpecStalk _ _ _

end EtaleFundamentalGroups.StrictHenselian
