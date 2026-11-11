/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FamilySpecializationNaturality
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperSeparablyClosedExtension
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Cartesian comparison of the actual fibers of a base-changed family

The previously defined geometric-fiber map is cartesian over the specified
field embedding when the original family square is cartesian. For proper
families and separably closed fields its actual finite étale pullback is an
equivalence, by the existing proper field-extension theorem.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.StrictHenselian

universe u

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

variable {X Y S T : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ T) (a : Y ⟶ X) (b : T ⟶ S)
  (hab : g ≫ b = a ≫ f)
  {Ωt Ωs : Type u} [Field Ωt] [Field Ωs]
  (t : Spec (.of Ωt) ⟶ T) (s : Spec (.of Ωs) ⟶ S)
  (ι : Ωs →+* Ωt) (hs : t ≫ b = Spec.map (CommRingCat.ofHom ι) ≫ s)

/-- The actual geometric-fiber map preserves the cartesian family square. -/
theorem familyGeometricFiberMap_isPullback (hcart : IsPullback a g f b) :
    IsPullback (familyGeometricFiberMap f g a b hab t s ι hs)
      (pullback.fst t g) (pullback.fst s f)
      (Spec.map (CommRingCat.ofHom ι)) := by
  apply IsPullback.of_right
    (p := familyGeometricFiberMap_fst f g a b hab t s ι hs)
    (t := (IsPullback.of_hasPullback s f).flip)
  rw [familyGeometricFiberMap_snd, ← hs]
  exact (IsPullback.of_hasPullback t g).flip.paste_horiz hcart

/-- The same actual fiber map induces the proper separably closed
field-extension equivalence. -/
theorem pullback_familyGeometricFiberMap_isEquivalence
    [IsProper f] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (hcart : IsPullback a g f b) :
    (FiniteEtale.pullback (familyGeometricFiberMap f g a b hab t s ι hs)).IsEquivalence := by
  have : IsProper (pullback.fst s f) := inferInstance
  exact FiniteEtale.pullback_isEquivalence_of_isProper_of_isSepClosed_field_square
    Ωs Ωt ι (pullback.fst s f)
    (familyGeometricFiberMap f g a b hab t s ι hs)
    (pullback.fst t g)
    (familyGeometricFiberMap_isPullback f g a b hab t s ι hs hcart)

end EtaleFundamentalGroups.StrictHenselian
