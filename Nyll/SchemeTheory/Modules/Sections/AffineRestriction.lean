/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Sections.RestrictSemilinear
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Ring.CompTypeclasses

/-!
# Original linear sections of the canonical affine restriction

For the canonical chart of an affine open, the coefficient isomorphism
followed by restriction back to the original open is the identity. Thus
the actual semilinear section comparison becomes linear over the
original section ring. This uses the actual `fromSpec` structure map,
not an arbitrary identification of its coefficient action.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

/-- The canonical affine chart's actual section map on the whole
spectrum is the original inverse spectrum coefficient isomorphism. -/
theorem fromSpec_appLE_top :
    hU.fromSpec.appLE U ⊤ hU.fromSpec_preimage_self.ge = (ΓSpecIso Γ(X, U)).inv := by
  let R : CommRingCat.{u} := Γ(X, U)
  let j : Spec R ⟶ X := hU.fromSpec
  let i : (⊤ : (Spec R).Opens) ⟶ j ⁻¹ᵁ U := eqToHom hU.fromSpec_preimage_self.symm
  let k : j ⁻¹ᵁ U ⟶ (⊤ : (Spec R).Opens) := eqToHom hU.fromSpec_preimage_self
  have h : j.app U = (ΓSpecIso R).inv ≫ (Spec R).presheaf.map k.op := hU.fromSpec_app_self
  change j.app U ≫ (Spec R).presheaf.map i.op = (ΓSpecIso R).inv
  rw [h, Category.assoc, ← CategoryTheory.Functor.map_comp,
    Subsingleton.elim (k.op ≫ i.op) (𝟙 _), CategoryTheory.Functor.map_id, Category.comp_id]

private theorem fromSpec_coefficient_comp :
    let j := hU.fromSpec
    let hImage : j ''ᵁ ⊤ = U := j.image_top_eq_opensRange.trans hU.opensRange_fromSpec
    (ΓSpecIso Γ(X, U)).inv ≫ (j.appIso ⊤).inv ≫
        X.presheaf.map (eqToHom hImage.symm).op = 𝟙 Γ(X, U) := by
  intro j hImage
  let i : U ⟶ j ''ᵁ ⊤ := eqToHom hImage.symm
  let k : j ''ᵁ ⊤ ⟶ U := homOfLE hImage.le
  have h₁ : (ΓSpecIso Γ(X, U)).inv ≫ (j.appIso ⊤).inv = X.presheaf.map k.op := by
    have h := j.appLE_appIso_inv (U := U) (V := ⊤) hU.fromSpec_preimage_self.ge
    exact (congrArg (fun a : Γ(X, U) ⟶ Γ(Spec Γ(X, U), ⊤) =>
      a ≫ (j.appIso ⊤).inv) (fromSpec_appLE_top U hU).symm).trans h
  rw [← Category.assoc, h₁, ← CategoryTheory.Functor.map_comp,
    Subsingleton.elim (k.op ≫ i.op) (𝟙 _), CategoryTheory.Functor.map_id]

/-- The actual sections of the canonical affine restriction are
linearly equivalent to the original sections over the original ring. -/
def affineRestrictionSectionsEquiv (M : X.Modules) :
    (moduleSpecΓFunctor (R := Γ(X, U))).obj (M.restrict hU.fromSpec) ≃ₗ[Γ(X, U)] Γ(M, U) := by
  let R : CommRingCat.{u} := Γ(X, U)
  let j : Spec R ⟶ X := hU.fromSpec
  let hImage : j ''ᵁ ⊤ = U := j.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  let i : U ⟶ j ''ᵁ ⊤ := eqToHom hImage.symm
  let eR : R ≃+* Γ(X, j ''ᵁ ⊤) := specRestrictionRingEquiv j
  have _hσ : RingHomInvPair (eR : R →+* Γ(X, j ''ᵁ ⊤))
      (eR.symm : Γ(X, j ''ᵁ ⊤) →+* R) := RingHomInvPair.of_ringEquiv eR
  have _hσ' : RingHomInvPair (eR.symm : Γ(X, j ''ᵁ ⊤) →+* R)
      (eR : R →+* Γ(X, j ''ᵁ ⊤)) := RingHomInvPair.of_ringEquiv_symm eR
  let eM := specRestrictionSectionsEquiv j M
  let eU : Γ(M, j ''ᵁ ⊤) ≅ Γ(M, U) :=
    M.presheaf.mapIso (eqToIso hImage).symm.op
  refine { eM.toAddEquiv.trans eU.addCommGroupIsoToAddEquiv with map_smul' := ?_ }
  intro r x
  have h₁ := congrArg (fun y : Γ(M, j ''ᵁ ⊤) => eU.hom y) (eM.map_smulₛₗ r x)
  have h₂ := M.map_smul i (eR r) (eM x)
  have hc : X.presheaf.map i.op (eR r) = r :=
    congrArg (fun a : Γ(X, U) ⟶ Γ(X, U) => a r) (fromSpec_coefficient_comp U hU)
  exact h₁.trans (h₂.trans (congrArg (fun a : Γ(X, U) => a • eU.hom (eM x)) hc))

/-- The linear affine comparison keeps the original restriction
section isomorphism and the original transport of the image open. -/
theorem affineRestrictionSectionsEquiv_apply (M : X.Modules)
    (x : (moduleSpecΓFunctor (R := Γ(X, U))).obj (M.restrict hU.fromSpec)) :
    affineRestrictionSectionsEquiv U hU M x =
      M.presheaf.map
        (eqToHom (hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec).symm).op
        ((M.restrictAppIso hU.fromSpec ⊤).hom x) := rfl

end AlgebraicGeometry.Scheme.Modules
