/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
import Mathlib.Algebra.Category.Ring.Instances
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.Topology.Sheaves.Stalks

/-!
# Ordinary stalk maps for a specified square of field-valued points

A scheme morphism together with a specified coefficient-field map and
commuting square induces a local homomorphism on the two ordinary stalks.
The point identification is obtained from the square and is incorporated
using the canonical stalk isomorphism. Evaluation and the maps from stalk
spectra commute with the original scheme morphism.

The construction also commutes with the actual ordinary-stalk map of a
specialization. This supplies the local-ring part of the naturality
diagram in Stacks Project, Lemma 58.16.1.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme

universe u

variable {X Y : Scheme.{u}} {Ωx Ωy : Type u} [Field Ωx] [Field Ωy]
  (f : X ⟶ Y) (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ Y)
  (ι : Ωy →+* Ωx)
  (h : x ≫ f = Spec.map (CommRingCat.ofHom ι) ≫ y)

include ι h

/-- The specified field square identifies the image of the underlying
source point with the underlying target point. -/
theorem fieldPointSquare_closedPoint :
    f (x (closedPoint Ωx)) = y (closedPoint Ωy) := by
  have hp := congrArg (fun a : Spec (.of Ωx) ⟶ Y => a (closedPoint Ωx)) h
  change f (x (closedPoint Ωx)) = y (Spec.map (CommRingCat.ofHom ι) (closedPoint Ωx)) at hp
  rw [Spec_closedPoint] at hp
  exact hp

/-- The actual local-ring map at a square of geometric points. Its source
stalk is identified by the equality proved from the specified square. -/
def pointedStalkMap :
    Y.presheaf.stalk (y (closedPoint Ωy)) ⟶ X.presheaf.stalk (x (closedPoint Ωx)) :=
  (Y.presheaf.stalkCongr
    (Inseparable.of_eq (fieldPointSquare_closedPoint f x y ι h).symm)).hom ≫
      f.stalkMap (x (closedPoint Ωx))

instance pointedStalkMap_isLocalHom : IsLocalHom (pointedStalkMap f x y ι h).hom := by
  unfold pointedStalkMap
  infer_instance

/-- The map of ordinary stalk spectra lies over the original scheme
morphism. The point comparison is the canonical equality-induced stalk
isomorphism. -/
theorem pointedStalkMap_fromSpecStalk :
    Spec.map (pointedStalkMap f x y ι h) ≫ Y.fromSpecStalk (y (closedPoint Ωy)) =
      X.fromSpecStalk (x (closedPoint Ωx)) ≫ f := by
  let e : Y.presheaf.stalk (y (closedPoint Ωy)) ≅
      Y.presheaf.stalk (f (x (closedPoint Ωx))) :=
    Y.presheaf.stalkCongr
      (Inseparable.of_eq (fieldPointSquare_closedPoint f x y ι h).symm)
  have he : Spec.map e.hom ≫ Y.fromSpecStalk (y (closedPoint Ωy)) =
      Y.fromSpecStalk (f (x (closedPoint Ωx))) :=
    SpecMap_stalkSpecializes_fromSpecStalk
      (Inseparable.of_eq (fieldPointSquare_closedPoint f x y ι h).symm).ge
  change Spec.map (e.hom ≫ f.stalkMap (x (closedPoint Ωx))) ≫
      Y.fromSpecStalk (y (closedPoint Ωy)) = _
  rw [Spec.map_comp, Category.assoc, he]
  exact SpecMap_stalkMap_fromSpecStalk f

/-- Evaluation on the two ordinary stalks retains the given coefficient
homomorphism. The equality follows by the actual maps to the scheme and
the monomorphism from the target stalk spectrum. -/
theorem pointedStalkMap_evaluation :
    pointedStalkMap f x y ι h ≫ stalkClosedPointTo x =
      stalkClosedPointTo y ≫ CommRingCat.ofHom ι := by
  apply Spec.map_injective
  apply (cancel_mono (Y.fromSpecStalk (y (closedPoint Ωy)))).mp
  calc
    Spec.map (pointedStalkMap f x y ι h ≫ stalkClosedPointTo x) ≫
        Y.fromSpecStalk (y (closedPoint Ωy)) =
      Spec.map (stalkClosedPointTo x) ≫
        (X.fromSpecStalk (x (closedPoint Ωx)) ≫ f) := by
      rw [Spec.map_comp, Category.assoc, pointedStalkMap_fromSpecStalk]
    _ = x ≫ f := by
      rw [← Category.assoc, Spec_stalkClosedPointTo_fromSpecStalk]
    _ = Spec.map (CommRingCat.ofHom ι) ≫ y := h
    _ = Spec.map (stalkClosedPointTo y ≫ CommRingCat.ofHom ι) ≫
        Y.fromSpecStalk (y (closedPoint Ωy)) := by
      rw [Spec.map_comp, Category.assoc, Spec_stalkClosedPointTo_fromSpecStalk]

/-- A specialization is preserved by the scheme morphism and the
specified identification of the special geometric points. -/
theorem specializes_of_fieldPointSquare {Ξ : Type u} [Field Ξ]
    (t : Spec (.of Ξ) ⟶ X) (ht : t (closedPoint Ξ) ⤳ x (closedPoint Ωx)) :
    (t ≫ f) (closedPoint Ξ) ⤳ y (closedPoint Ωy) := by
  change f (t (closedPoint Ξ)) ⤳ y (closedPoint Ωy)
  exact (ht.map f.continuous).trans
    (specializes_of_eq (fieldPointSquare_closedPoint f x y ι h))

/-- The ordinary-stalk specialization homomorphism commutes with the
actual pointed stalk map. No compatibility on stalks is an extra input. -/
theorem pointedStalkMap_specializationToField {Ξ : Type u} [Field Ξ]
    (t : Spec (.of Ξ) ⟶ X) (ht : t (closedPoint Ξ) ⤳ x (closedPoint Ωx)) :
    pointedStalkMap f x y ι h ≫ stalkSpecializationToField (x (closedPoint Ωx)) t ht =
      stalkSpecializationToField (y (closedPoint Ωy)) (t ≫ f)
        (specializes_of_fieldPointSquare f x y ι h t ht) := by
  apply Spec.map_injective
  apply (cancel_mono (Y.fromSpecStalk (y (closedPoint Ωy)))).mp
  calc
    Spec.map (pointedStalkMap f x y ι h ≫
        stalkSpecializationToField (x (closedPoint Ωx)) t ht) ≫
        Y.fromSpecStalk (y (closedPoint Ωy)) =
      Spec.map (stalkSpecializationToField (x (closedPoint Ωx)) t ht) ≫
        (X.fromSpecStalk (x (closedPoint Ωx)) ≫ f) := by
      rw [Spec.map_comp, Category.assoc, pointedStalkMap_fromSpecStalk]
    _ = t ≫ f := by
      rw [← Category.assoc, Spec_stalkSpecializationToField_fromSpecStalk]
    _ = Spec.map (stalkSpecializationToField (y (closedPoint Ωy)) (t ≫ f)
        (specializes_of_fieldPointSquare f x y ι h t ht)) ≫
        Y.fromSpecStalk (y (closedPoint Ωy)) :=
      (Spec_stalkSpecializationToField_fromSpecStalk _ _ _).symm

end AlgebraicGeometry.Scheme
