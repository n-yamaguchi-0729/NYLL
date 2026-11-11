/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Spectral.Prespectral

/-!
# Compact open extensions along an actual closed immersion

The induced topology first extends an open subset to the ambient scheme.
The compact image of that subset then has a compact open neighbourhood
inside the chosen extension, using the existing prespectral-space theorem.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A quasicompact open in a closed subscheme is the exact inverse image
of a quasicompact open in the ambient scheme. -/
theorem exists_isCompact_open_preimage_eq_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (W : Z.Opens) (hW : IsCompact (W : Set Z)) :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ i ⁻¹ᵁ U = W := by
  obtain ⟨V, hV, hWV⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp W.isOpen
  have himage : i '' (W : Set Z) ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    change z ∈ i ⁻¹' V
    rw [hWV]
    exact hz
  obtain ⟨U, hUc, hUo, hWU, hUV⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between
      (hW.image i.continuous) hV himage
  refine ⟨⟨U, hUo⟩, hUc, ?_⟩
  ext z
  constructor
  · intro hz
    change z ∈ (W : Set Z)
    rw [← hWV]
    exact hUV hz
  · intro hz
    exact hWU ⟨z, hz, rfl⟩

end AlgebraicGeometry
