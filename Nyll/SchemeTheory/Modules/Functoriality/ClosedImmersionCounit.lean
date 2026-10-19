/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionUnit
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPushforward
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.Topology.Maps.Basic

/-!
# The actual pullback counit for a closed immersion

For a morphism inducing the source topology, every source open is the
preimage of a target open. The original pushforward therefore detects
isomorphisms of module sheaves by their original maps on sections.

For a closed immersion, the direct image of a quasicoherent module is
quasicoherent. Its original pullback unit is an epimorphism. The right
triangle identity makes the direct image of the original counit its
inverse, and detection by pushforward proves that the counit is an
isomorphism.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- If the source topology is induced from the target, the original
pushforward detects isomorphisms of module sheaves. -/
theorem isIso_of_pushforward_isIso_of_isInducing
    (hf : Topology.IsInducing f) {M N : X.Modules} (φ : M ⟶ N)
    [IsIso ((pushforward f).map φ)] : IsIso φ := by
  apply Hom.isIso_iff_isIso_app.mpr
  intro U
  obtain ⟨V, hV, hVU⟩ := hf.isOpen_iff.mp U.isOpen
  let W : Y.Opens := ⟨V, hV⟩
  have hW : f ⁻¹ᵁ W = U := SetLike.coe_injective hVU
  have hpush : IsIso (((pushforward f).map φ).app W) :=
    Hom.isIso_iff_isIso_app.mp
      (inferInstance : IsIso ((pushforward f).map φ)) W
  have hφ : IsIso (φ.app (f ⁻¹ᵁ W)) := by
    rw [← pushforward_map_app f φ W]
    exact hpush
  exact Eq.mp (congrArg (fun Z : X.Opens => IsIso (φ.app Z)) hW) hφ

/-- The original pullback-pushforward counit of a quasicoherent
module under a closed immersion is an isomorphism. -/
theorem isIso_pullbackCounit_of_isClosedImmersion [IsClosedImmersion f]
    (N : X.Modules) [N.IsQuasicoherent] :
    IsIso ((pullbackPushforwardAdjunction f).counit.app N) := by
  have : ((pushforward f).obj N).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom f N
  let adj : pullback f ⊣ pushforward f := pullbackPushforwardAdjunction f
  let ε : (pullback f).obj ((pushforward f).obj N) ⟶ N := adj.counit.app N
  let η : (pushforward f).obj N ⟶
      (pushforward f).obj ((pullback f).obj ((pushforward f).obj N)) :=
    adj.unit.app ((pushforward f).obj N)
  let β : (pushforward f).obj ((pullback f).obj ((pushforward f).obj N)) ⟶
      (pushforward f).obj N := (pushforward f).map ε
  have : Epi η := epi_pullbackUnit_of_isClosedImmersion f ((pushforward f).obj N)
  have hηβ : η ≫ β = 𝟙 ((pushforward f).obj N) := adj.right_triangle_components N
  have hβη : β ≫ η =
      𝟙 ((pushforward f).obj ((pullback f).obj ((pushforward f).obj N))) := by
    apply (cancel_epi η).mp
    rw [← Category.assoc, hηβ, Category.id_comp, Category.comp_id]
  let e : (pushforward f).obj ((pullback f).obj ((pushforward f).obj N)) ≅
      (pushforward f).obj N :=
    { hom := β
      inv := η
      hom_inv_id := hβη
      inv_hom_id := hηβ }
  have : IsIso β := e.isIso_hom
  exact isIso_of_pushforward_isIso_of_isInducing f f.isClosedEmbedding.isInducing ε

end AlgebraicGeometry.Scheme.Modules
