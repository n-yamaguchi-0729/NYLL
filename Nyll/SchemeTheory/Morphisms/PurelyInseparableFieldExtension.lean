/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Purely inseparable constant field extensions

A purely inseparable field extension induces an integral, universally
injective, surjective projection after base change by any scheme. Its
underlying continuous map is therefore a homeomorphism.

The two scheme-morphism lemmas retain their original namespace and signatures
from `EtaleFundamentalGroups/FiniteEtale/FiniteField/PurelyInseparablePullback`.
-/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace EtaleFundamentalGroups

/-- A purely inseparable field extension induces a universally injective map of spectra. -/
theorem purelyInseparable_specMap_universallyInjective
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsPurelyInseparable k L] :
    UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  apply ((tfae_universallyInjective _).out 1 2).mpr
  intro K _ a b hab
  apply (Spec.preimage_inj a b).mp
  apply CommRingCat.hom_ext
  apply IsPurelyInseparable.injective_comp_algebraMap k L K
  have h := congrArg Spec.preimage hab
  rw [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map] at h
  exact congrArg CommRingCat.Hom.hom h

/-- The coefficient projection of a purely inseparable extension is an
integral, universally injective, surjective scheme morphism. -/
theorem purelyInseparable_constantField_projection_properties
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsPurelyInseparable k L]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    let p := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
    IsIntegralHom p ∧ UniversallyInjective p ∧ Surjective p := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let : IsIntegralHom φ := (IsIntegralHom.SpecMap_iff).2
    (Algebra.IsIntegral.isIntegral (R := k))
  let : UniversallyInjective φ := purelyInseparable_specMap_universallyInjective k L
  let : Surjective φ := ⟨fun y ↦ ⟨Classical.choice (inferInstance : Nonempty (Spec (.of L))),
    Subsingleton.elim _ _⟩⟩
  exact ⟨inferInstance,
    MorphismProperty.pullback_snd
      (P := (show MorphismProperty Scheme.{u} from @UniversallyInjective)) φ f inferInstance,
    inferInstance⟩

end EtaleFundamentalGroups

namespace AlgebraicGeometry

/-- The actual base-change projection across a purely inseparable field extension
induces a homeomorphism, with no finiteness assumption on the scheme or extension. -/
def purelyInseparableConstantFieldHomeomorph
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsPurelyInseparable k L]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) ≃ₜ X := by
  let p := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
  have hp := EtaleFundamentalGroups.purelyInseparable_constantField_projection_properties
    k L X f
  have : IsIntegralHom p := hp.1
  have : UniversallyInjective p := hp.2.1
  have : Surjective p := hp.2.2
  exact IsHomeomorph.homeomorph p
    (isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
      ⟨p.continuous, p.isClosedMap, p.injective, p.surjective⟩)

end AlgebraicGeometry
