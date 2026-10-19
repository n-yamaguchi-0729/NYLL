/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.GeometricallyConnectedSections
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleConnected
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleOverSeparablyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Spec

/-!
# Invariance of arbitrary étale sections under separably closed base extension

An arbitrary field extension of a separably closed field has geometrically
connected spectrum. Its projection after any scheme base change is flat
and quasi-compact with geometrically connected fibres. The original étale
global-section pullback map is therefore bijective, with no finite type or
constructibility restrictions (Stacks Project, Lemma 59.39.5).
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

/-- The actual projection from any Cartesian field-extension square has
bijective section pullback over a separably closed base field. -/
theorem etalePullbackGlobalSectionsMap_bijective_of_isSepClosed_fieldPullback
    (k K : Type u) [Field k] [IsSepClosed k] [Field K]
    (φ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {X Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (q : Z ⟶ X) (p : Z ⟶ Spec (CommRingCat.of K))
    (h : IsPullback q p f φ)
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Function.Bijective (etalePullbackGlobalSectionsMap q Λ F) := by
  have : GeometricallyIrreducible φ :=
    GeometricallyIrreducible.of_irreducibleSpace_of_isSepClosed φ
  have hφ : GeometricallyConnected φ := GeometricallyIrreducible.geometricallyConnected φ
  have : GeometricallyConnected q :=
    MorphismProperty.of_isPullback h.flip hφ
  have : Flat q := MorphismProperty.of_isPullback h.flip (inferInstance : Flat φ)
  have : QuasiCompact q :=
    MorphismProperty.of_isPullback h.flip (inferInstance : QuasiCompact φ)
  exact etalePullbackGlobalSectionsMap_bijective_of_geometricallyConnected q Λ F

/-- Arbitrary field extension of a separably closed base preserves the
actual global sections of every étale module sheaf, for every base scheme. -/
theorem etalePullbackGlobalSectionsMap_bijective_of_isSepClosed_fieldExtension
    (k K : Type u) [Field k] [IsSepClosed k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Function.Bijective (etalePullbackGlobalSectionsMap
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) Λ F) := by
  let φ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : GeometricallyIrreducible φ :=
    GeometricallyIrreducible.of_irreducibleSpace_of_isSepClosed φ
  have : GeometricallyConnected φ := GeometricallyIrreducible.geometricallyConnected φ
  have : Flat φ := inferInstance
  have : QuasiCompact φ := inferInstance
  exact etalePullbackGlobalSectionsMap_bijective_of_geometricallyConnected
    (pullback.snd φ f) Λ F

/-- The same field-extension invariance in the native first-projection
orientation, avoiding transport through pullback symmetry for consumers. -/
theorem etalePullbackGlobalSectionsMap_bijective_of_isSepClosed_fieldExtension_fst
    (k K : Type u) [Field k] [IsSepClosed k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Function.Bijective (etalePullbackGlobalSectionsMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) Λ F) := by
  let φ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : GeometricallyIrreducible φ :=
    GeometricallyIrreducible.of_irreducibleSpace_of_isSepClosed φ
  have : GeometricallyConnected φ := GeometricallyIrreducible.geometricallyConnected φ
  have : Flat φ := inferInstance
  have : QuasiCompact φ := inferInstance
  exact etalePullbackGlobalSectionsMap_bijective_of_geometricallyConnected
    (pullback.fst f φ) Λ F

end EtaleCohomology
