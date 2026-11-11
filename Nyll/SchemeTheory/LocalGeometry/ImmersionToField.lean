/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Nonempty immersions into a field spectrum

An immersion into a field spectrum has closed range. If its source is nonempty, it is
surjective, hence is an isomorphism by reducedness of the field spectrum. No algebraic or
separable closedness of the field is used.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

/-- A nonempty immersion into a field spectrum is an isomorphism. -/
theorem isIso_of_isImmersion_toSpecField
    {Ω : Type u} [Field Ω] {X : Scheme.{u}} [Nonempty X]
    (f : X ⟶ Spec (.of Ω)) [IsImmersion f] : IsIso f := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hf : Function.Surjective f := fun y => ⟨x, Subsingleton.elim _ y⟩
  have : Surjective f := ⟨hf⟩
  have : IsClosedImmersion f := IsClosedImmersion.of_isPreimmersion f (by
    rw [Set.range_eq_univ.mpr hf]
    exact isClosed_univ)
  exact isIso_of_isClosedImmersion_of_surjective f

end AlgebraicGeometry.Scheme
