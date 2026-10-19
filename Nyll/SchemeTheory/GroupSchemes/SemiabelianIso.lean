/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.Semiabelian

/-! # Transport of actual semiabelian extensions by group-scheme isomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]
  {G H : CommGrp (Over (Spec (CommRingCat.of K)))}

namespace SemiabelianExtension

/-- Transport an actual extension by an isomorphism of its middle group. -/
def ofIso (E : SemiabelianExtension G) (e : G ≅ H) : SemiabelianExtension H := by
  let a : G.X ≅ H.X := (CommGrp.forget _).mapIso e
  have h : (E.inclusion.hom.hom.hom ≫ a.hom) ≫
      (a.inv ≫ E.projection.hom.hom.hom) = 1 := by
    rw [Category.assoc, ← Category.assoc a.hom, a.hom_inv_id, Category.id_comp,
      E.condition]
  exact {
    torus := E.torus
    quotient := E.quotient
    inclusion := E.inclusion ≫ e.hom
    projection := e.inv ≫ E.projection
    condition := h
    isKernel := Fork.isLimitOfIsos _ E.isKernel
      (Fork.ofι (E.inclusion.hom.hom.hom ≫ a.hom)
        (h.trans (MonObj.comp_one (E.inclusion.hom.hom.hom ≫ a.hom)).symm))
      a (Iso.refl _) (Iso.refl _)
      ((a.hom_inv_id_assoc E.projection.hom.hom.hom).trans (Category.comp_id _).symm)
      ((MonObj.comp_one a.hom).trans (Category.comp_id _).symm)
      (Category.id_comp _)
    projection_smooth := by
      have : Smooth E.projection.hom.hom.hom.left := E.projection_smooth
      change Smooth (a.inv.left ≫ E.projection.hom.hom.hom.left)
      infer_instance
    projection_surjective := by
      have : Surjective E.projection.hom.hom.hom.left := E.projection_surjective
      change Surjective (a.inv.left ≫ E.projection.hom.hom.hom.left)
      infer_instance }

end SemiabelianExtension

namespace IsSemiabelian

/-- An actual group-scheme isomorphism transports semiabelianity. -/
theorem of_iso (e : G ≅ H) [IsSemiabelian G] : IsSemiabelian H := by
  obtain ⟨E⟩ := exists_extension (G := G)
  exact (E.ofIso e).isSemiabelian

/-- An actual group-scheme isomorphism preserves and reflects semiabelianity. -/
theorem iso_iff (e : G ≅ H) : IsSemiabelian G ↔ IsSemiabelian H :=
  ⟨fun _ => of_iso e, fun _ => of_iso e.symm⟩

end IsSemiabelian

end AlgebraicGeometry
