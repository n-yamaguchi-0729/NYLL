/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationMap

/-!
# Uniqueness of the chosen geometric-stalk specialization map

The map induced by a chosen field-valued lift is characterized by its action
on the germs of the original pointed étale neighborhoods. This records the
uniqueness principle separately from the construction and does not assert a
proper-family fundamental-group comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω Ψ : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω] [Field Ψ]
  (s : R →+* Ω) (t : R →+* Ψ)
  (ψ : geometricStalk (Spec.map (CommRingCat.ofHom s)) →+* Ψ)
  (hψ : ψ.comp (geometricStalkStructureMap s) = t)

/-- Any morphism inducing the prescribed map on every original étale germ
is the already constructed geometric-stalk specialization map. -/
theorem geometricStalkSpecializationMap_unique
    (F : geometricStalk (Spec.map (CommRingCat.ofHom s)) ⟶
      geometricStalk (Spec.map (CommRingCat.ofHom t)))
    (hF : ∀ (W : (Spec (.of R)).Etale)
      (w : (Scheme.pointEtaleNeighborhoods
        (Spec.map (CommRingCat.ofHom s))).fiber.obj W),
      geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫ F =
        geometricStalkGerm (Spec.map (CommRingCat.ofHom t)) W
          (pointedEtaleSpecialization s t ψ hψ W w)) :
    F = geometricStalkSpecializationMap s t ψ hψ := by
  apply (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom s))).presheafFiber_hom_ext
  intro W w
  change geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫ F =
    geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫
      geometricStalkSpecializationMap s t ψ hψ
  rw [hF, geometricStalkGerm_specializationMap]

end EtaleFundamentalGroups.StrictHenselian
