/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralAlgClosed
public import Nyll.EtaleCohomology.Classical.RootsOfUnityH0Pullback
public import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleConnected
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Roots-of-unity sections on a product with a proper integral variety

For a smooth proper integral scheme over an algebraically closed field,
every original Kummer-kernel section on its product with any parameter scheme
comes uniquely from that parameter scheme. No connectedness assumption is
made on the parameter, so the theorem applies to all Čech overlaps and
triangles of a finite étale cover.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Every actual μₙ section of the product descends uniquely to the
parameter, by the original global-section pullback map. -/
theorem existsUnique_rootsOfUnitySection_product
    {K : Type u} [Field K] [IsAlgClosed K]
    {C W : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) [Smooth c] [IsProper c]
    (w : W ⟶ Spec (.of K)) {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))
    (b : (etaleRootsOfUnitySheaf (pullback c w) n).obj.obj
      (op (Scheme.Etale.mk (𝟙 (pullback c w))))) :
    ∃! a : (etaleRootsOfUnitySheaf W n).obj.obj (op (Scheme.Etale.mk (𝟙 W))),
      etaleRootsOfUnityGlobalSectionsPullback (pullback.snd c w) n a = b := by
  have : GeometricallyIntegral c := geometricallyIntegral_of_isAlgClosed c
  have : GeometricallyConnected c := GeometricallyIrreducible.geometricallyConnected c
  have hb := etaleRootsOfUnityGlobalSectionsPullback_bijective
    (pullback.snd c w) w hn hnK
  obtain ⟨a, ha⟩ := hb.2 b
  exact ⟨a, ha, fun a' ha' => hb.1 (ha'.trans ha.symm)⟩

end EtaleCohomology
