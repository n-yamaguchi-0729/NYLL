/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.SmoothBaseChange
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.AdjoinRoot

/-!
# The actual root chart on a base-changed smooth scheme

An affine smooth chart of a scheme over a DVR gives an actual affine
open chart after the same uniformizer-root extension of the base. Its
coordinate ring is the polynomial root algebra on the original affine
chart, with its original coefficient and distinguished-root maps.

The map to the global base change is constructed by the pullback
universal property. Cancellation of cartesian squares identifies it
with the pullback of the original open chart, proving it is an open
immersion. This places the local root-normalization calculation on the
actual global base-changed scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace EtaleFundamentalGroups.Kummer

universe u

/-- A uniformizer root on an affine chart is the actual open chart on
the global root base change. Both original coefficient projections are
retained in the cartesian square and the map to the root base. -/
theorem exists_uniformizerRootSchemeChart
    (B A : Type u)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing A] [Algebra B A] [Algebra.Smooth B A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    (v : Spec (.of A) ⟶ X) [IsOpenImmersion v]
    (hv : v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B A)))
    (n : ℕ) (hn : 0 < n) (π : B) (hπ : Prime π) :
    let Bn := AdjoinRoot (Polynomial.X ^ n - C π)
    let D := AdjoinRoot (Polynomial.X ^ n - C (algebraMap B A π))
    let : Algebra Bn D := rootBaseChangeRootAlgebra B A n π
    let s := Spec.map (CommRingCat.ofHom (algebraMap B Bn))
    let u := Spec.map (CommRingCat.ofHom (algebraMap A D))
    ∃ v' : Spec (.of D) ⟶ pullback f s,
      IsOpenImmersion v' ∧ IsPullback u v' v (pullback.fst f s) ∧
        v' ≫ pullback.snd f s = Spec.map (CommRingCat.ofHom (algebraMap Bn D)) := by
  intro Bn D aBnD s u
  let w := Spec.map (CommRingCat.ofHom (algebraMap Bn D))
  have hRoot : IsPullback u w
      (Spec.map (CommRingCat.ofHom (algebraMap B A))) s :=
    (uniformizerRoot_smoothBaseChange_regular B A n hn π hπ).2.2
  have hcomm : (u ≫ v) ≫ f = w ≫ s := by
    rw [Category.assoc, hv]
    exact hRoot.w
  let v' : Spec (.of D) ⟶ pullback f s := pullback.lift (u ≫ v) w hcomm
  have hfst : v' ≫ pullback.fst f s = u ≫ v := pullback.lift_fst _ _ _
  have hsnd : v' ≫ pullback.snd f s = w := pullback.lift_snd _ _ _
  have hOuter : IsPullback u (v' ≫ pullback.snd f s) (v ≫ f) s := by
    rw [hsnd, hv]
    exact hRoot
  have hChart : IsPullback u v' v (pullback.fst f s) :=
    hOuter.of_bot hfst.symm (IsPullback.of_hasPullback f s)
  exact ⟨v', MorphismProperty.of_isPullback (P := @IsOpenImmersion) hChart inferInstance,
    hChart, hsnd⟩

end EtaleFundamentalGroups.Kummer
