/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperSeparablyClosedExtension
import Nyll.EtaleFundamentalGroups.GaloisCategories.EquivalenceFunctoriality
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Changing a geometric fiber over the original base scheme

A specified field embedding and its triangle over the original scheme induce
an actual map between the two fiber products. Its square over the two fields
is cartesian. For a proper morphism and separably closed fields, this map
induces an equivalence on finite étale covers and an isomorphism on the
automorphism groups of the specified fiber functors.

This retains the original geometric points, rather than replacing either
fiber product by an unspecified isomorphic scheme. It is used in the closed
fiber comparison for the strict local specialization diagram of Stacks 58.16.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

variable {X S : Scheme.{u}} {k K : Type u} [Field k] [Field K]
  (f : X ⟶ S) (s : Spec (CommRingCat.of k) ⟶ S)
  (t : Spec (CommRingCat.of K) ⟶ S) (ι : k →+* K)
  (h : t = Spec.map (CommRingCat.ofHom ι) ≫ s)

/-- The actual map of geometric fibers attached to the given point triangle. -/
def fieldBaseChangeMap : Limits.pullback f t ⟶ Limits.pullback f s :=
  Limits.pullback.lift (Limits.pullback.fst f t)
    (Limits.pullback.snd f t ≫ Spec.map (CommRingCat.ofHom ι))
    (by rw [Category.assoc, ← h]; exact Limits.pullback.condition)

/-- The change of field preserves the map to the original total space. -/
theorem fieldBaseChangeMap_fst :
    fieldBaseChangeMap f s t ι h ≫ Limits.pullback.fst f s =
      Limits.pullback.fst f t :=
  Limits.pullback.lift_fst _ _ _

/-- Its coefficient map is the specified embedding of fields. -/
theorem fieldBaseChangeMap_snd :
    fieldBaseChangeMap f s t ι h ≫ Limits.pullback.snd f s =
      Limits.pullback.snd f t ≫ Spec.map (CommRingCat.ofHom ι) :=
  Limits.pullback.lift_snd _ _ _

/-- The actual two fibers form a cartesian square over the specified fields. -/
theorem fieldBaseChangeMap_isPullback :
    IsPullback (fieldBaseChangeMap f s t ι h) (Limits.pullback.snd f t)
      (Limits.pullback.snd f s) (Spec.map (CommRingCat.ofHom ι)) := by
  apply IsPullback.of_right (p := fieldBaseChangeMap_snd f s t ι h)
    (t := IsPullback.of_hasPullback f s)
  rw [fieldBaseChangeMap_fst, ← h]
  exact IsPullback.of_hasPullback f t

section Proper

variable [IsProper f] [IsSepClosed k] [IsSepClosed K]

/-- Proper geometric fibers have the same finite étale covers under the
specified extension of separably closed fields. -/
theorem pullback_fieldBaseChangeMap_isEquivalence :
    (pullback (fieldBaseChangeMap f s t ι h)).IsEquivalence := by
  have hProper : IsProper (Limits.pullback.snd f s) := inferInstance
  exact pullback_isEquivalence_of_isProper_of_isSepClosed_field_square k K ι
    (Limits.pullback.snd f s) (fieldBaseChangeMap f s t ι h)
    (Limits.pullback.snd f t) (fieldBaseChangeMap_isPullback f s t ι h)

/-- The original geometric-fiber morphism induces an isomorphism of the
automorphism groups at the given field-valued point. For a geometric point,
these are the actual étale fundamental groups. No connectedness is assumed. -/
def fundamentalGroupEquivProperFieldBaseChange
    {Ω : Type u} [Field Ω]
    (xi : Spec (CommRingCat.of Ω) ⟶ Limits.pullback f t) :
    π₁ᵉᵗ(xi) ≃ₜ* π₁ᵉᵗ(xi ≫ fieldBaseChangeMap f s t ι h) := by
  have hEquivalence : (pullback (fieldBaseChangeMap f s t ι h)).IsEquivalence :=
    pullback_fieldBaseChangeMap_isEquivalence f s t ι h
  exact CategoryTheory.PreGaloisCategory.autEquivOfCompIsoOfEquivalence
    (pullback (fieldBaseChangeMap f s t ι h))
    (pullbackFiberIso (fieldBaseChangeMap f s t ι h) xi)

/-- The comparison retains the actual homomorphism induced by the fiber map. -/
theorem fundamentalGroupEquivProperFieldBaseChange_apply
    {Ω : Type u} [Field Ω]
    (xi : Spec (CommRingCat.of Ω) ⟶ Limits.pullback f t) (a : π₁ᵉᵗ(xi)) :
    fundamentalGroupEquivProperFieldBaseChange f s t ι h xi a =
      fundamentalGroupHom (fieldBaseChangeMap f s t ι h) xi a := rfl

end Proper

end AlgebraicGeometry.FiniteEtale
