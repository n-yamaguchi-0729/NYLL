/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.ProperHenselianH0
import Nyll.EtaleCohomology.Sites.PullbackGlobalSectionsComposition
import Nyll.EtaleCohomology.Sites.SeparablyClosedFieldExtensionSections
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Proper sections over an arbitrary closed field point of a strictly local base

The local map to the field factors through the actual residue field. The
induced source base-change factors through the closed fibre, and its other
factor is Cartesian over that residue-field extension. Proper henselian
H⁰ and separably closed field-extension invariance give the two actual
section bijections. The canonical inverse-image composition isomorphism
then proves bijectivity of the original section map.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private theorem globalSectionsMap_bijective_comp
    {X Y Z : Scheme.{u}} (p : Z ⟶ Y) (q : Y ⟶ X)
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (hq : Function.Bijective (etalePullbackGlobalSectionsMap q Λ F))
    (hp : Function.Bijective
      (etalePullbackGlobalSectionsMap p Λ ((etalePullback q Λ).obj F))) :
    Function.Bijective (etalePullbackGlobalSectionsMap (p ≫ q) Λ F) := by
  let E := ((sheafSections Z.smallEtaleTopology (ModuleCat.{u} Λ)).obj
    (op (Scheme.Etale.mk (𝟙 Z)))).mapIso ((etalePullbackCompIso p q Λ).app F)
  have hcomp : etalePullbackGlobalSectionsMap (p ≫ q) Λ F ≫ E.hom =
      etalePullbackGlobalSectionsMap q Λ F ≫
        etalePullbackGlobalSectionsMap p Λ ((etalePullback q Λ).obj F) :=
    etalePullbackGlobalSectionsMap_comp p q Λ F
  apply Function.Bijective.of_comp_left (f := E.hom)
  · change Function.Bijective (etalePullbackGlobalSectionsMap (p ≫ q) Λ F ≫ E.hom)
    rw [hcomp]
    exact hp.comp hq
  · exact (ConcreteCategory.bijective_of_isIso E.hom).injective

/-- Proper henselian H⁰ remains invariant at every field-valued closed
point when the base residue field is separably closed. The conclusion is
the original map attached to any supplied actual Cartesian square. -/
theorem etaleClosedField_globalSections_bijective_of_isPullback
    (H : Type u) [CommRing H] [HenselianLocalRing H]
    [IsSepClosed (IsLocalRing.ResidueField H)]
    {Ω : Type u} [Field Ω] (ε : H →+* Ω) [IsLocalHom ε]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of H)) [IsProper f]
    (q : Z ⟶ X) (p : Z ⟶ Spec (CommRingCat.of Ω))
    (h : IsPullback q p f (Spec.map (CommRingCat.ofHom ε)))
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Function.Bijective (etalePullbackGlobalSectionsMap q Λ F) := by
  let κ := IsLocalRing.ResidueField H
  let r : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of H) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue H))
  let j : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of κ) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.lift ε))
  have hjr : j ≫ r = Spec.map (CommRingCat.ofHom ε) := by
    change Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.lift ε)) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue H)) = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact IsLocalRing.ResidueField.lift_comp_residue ε
  let Y : Scheme.{u} := pullback f r
  let i : Y ⟶ X := pullback.fst f r
  let g : Y ⟶ Spec (CommRingCat.of κ) := pullback.snd f r
  let l : Z ⟶ Y := pullback.lift q (p ≫ j) (by
    rw [Category.assoc, hjr]
    exact h.w)
  have hli : l ≫ i = q := pullback.lift_fst _ _ _
  have hlg : l ≫ g = p ≫ j := pullback.lift_snd _ _ _
  have houter : IsPullback (l ≫ i) p f (j ≫ r) := by
    rw [hli, hjr]
    exact h
  have hlpb : IsPullback l p g j :=
    houter.of_right hlg (IsPullback.of_hasPullback f r)
  have hi : Function.Bijective (etalePullbackGlobalSectionsMap i Λ F) :=
    etaleClosedFiber_globalSections_bijective H f Λ F
  have hl : Function.Bijective
      (etalePullbackGlobalSectionsMap l Λ ((etalePullback i Λ).obj F)) :=
    etalePullbackGlobalSectionsMap_bijective_of_isSepClosed_fieldPullback
      κ Ω j g l p hlpb Λ ((etalePullback i Λ).obj F)
  have hc := globalSectionsMap_bijective_comp l i Λ F hi hl
  rwa [hli] at hc

end EtaleCohomology
