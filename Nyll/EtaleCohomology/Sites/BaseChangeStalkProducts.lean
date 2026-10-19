/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.PullbackStalks
import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Base change of the products of geometric stalks

The universal property of the actual scheme pullback identifies geometric
lifts before and after base change. The inverse-image stalk isomorphisms
then identify the corresponding categorical products. This is the product
side of the finite direct-image base-change comparison.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
  {Ω : Type u} [Field Ω] (t : Spec (.of Ω) ⟶ Y')

/-- Geometric lifts into a scheme pullback are precisely the original lifts
of the composite geometric point. -/
def geometricLiftBaseChangeEquiv :
    {s : Spec (.of Ω) ⟶ pullback f g // s ≫ pullback.snd f g = t} ≃
      {s : Spec (.of Ω) ⟶ X // s ≫ f = t ≫ g} where
  toFun s := ⟨s.val ≫ pullback.fst f g, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, s.property]⟩
  invFun s := ⟨pullback.lift s.val t s.property, pullback.lift_snd _ _ _⟩
  left_inv s := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans s.property.symm
  right_inv s := Subtype.ext (pullback.lift_fst _ _ _)

variable [IsSepClosed Ω] (R : Type u) [CommRing R]

/-- The canonical stalk isomorphism oriented as the actual inverse-image
unit followed by restriction to the chosen geometric lift. -/
def pullbackUnitGeometricStalkIso {T S : Scheme.{u}} (q : T ⟶ S)
    (s : Spec (.of Ω) ⟶ T) (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} R)) :
    (Scheme.pointSmallEtale (s ≫ q)).sheafFiber.obj F ≅
      (Scheme.pointSmallEtale s).sheafFiber.obj ((etalePullback q R).obj F) := by
  let α := (Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map
      ((etalePullbackPushforwardAdjunction q R).unit.app F) ≫
    etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ ((etalePullback q R).obj F)
  have : IsIso α := etalePullbackUnit_stalkComponent_isIso q s R F
  exact asIso α

/-- The forward map is literally the inverse-image unit followed by
restriction to the specified geometric lift. -/
theorem pullbackUnitGeometricStalkIso_hom {T S : Scheme.{u}} (q : T ⟶ S)
    (s : Spec (.of Ω) ⟶ T) (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} R)) :
    (pullbackUnitGeometricStalkIso R q s F).hom =
      (Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map
        ((etalePullbackPushforwardAdjunction q R).unit.app F) ≫
      etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩
        ((etalePullback q R).obj F) := rfl

/-- The actual products of geometric stalks are identified by base change.
Finiteness is not needed for this product comparison. -/
def baseChangeStalkProductIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (∏ᶜ fun s : {s : Spec (.of Ω) ⟶ pullback f g // s ≫ pullback.snd f g = t} =>
      (Scheme.pointSmallEtale s.val).sheafFiber.obj
        ((etalePullback (pullback.fst f g) R).obj F)) ≅
      ∏ᶜ fun s : {s : Spec (.of Ω) ⟶ X // s ≫ f = t ≫ g} =>
        (Scheme.pointSmallEtale s.val).sheafFiber.obj F :=
  Pi.whiskerEquiv (geometricLiftBaseChangeEquiv f g t)
    (fun s => pullbackUnitGeometricStalkIso R (pullback.fst f g) s.val F)

end EtaleCohomology
