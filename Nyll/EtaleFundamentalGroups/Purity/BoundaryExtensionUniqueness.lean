/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.BoundaryScalarHartogs
import Nyll.SchemeTheory.Modules.Functoriality.RelativeSpecDirectImage

/-!
# Recovery of finite extensions from their depth-two open part

The original algebra restriction is an isomorphism by scalar Hartogs on
the extension itself. Its relative spectrum therefore recovers that same
finite extension over the original base.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme.Modules

/-- Every original structure-sheaf map to a depth-two open is invertible,
including on nonaffine opens. -/
theorem isIso_open_app_of_boundary_two_le_depth
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (W : X.Opens) : IsIso (U.ι.app W) := by
  let η := (restrictAdjunction U.ι).unit.app (𝟙_ X.Modules)
  have : IsIso η :=
    isIso_structure_unit_of_locallyNoetherian_boundary_two_le_depth X U hdepth
  have hb : Function.Bijective (η.app W) := ConcreteCategory.bijective_of_isIso (η.app W)
  change Function.Bijective
    (X.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op) at hb
  have hres : IsIso (U.ι.app W ≫ (U.ι.appIso (U.ι ⁻¹ᵁ W)).inv) := by
    rw [Scheme.Hom.app_appIso_inv]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hb
  exact IsIso.of_isIso_comp_right (U.ι.app W) (U.ι.appIso (U.ι ⁻¹ᵁ W)).inv

namespace Scheme.DirectImageAlgebra

/-- A depth-two boundary on the actual source makes its original
open direct-image algebra map an isomorphism. -/
theorem isIso_boundaryMap {Y X : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (T : Y.Opens)
    (hdepth : ∀ y : Y, y ∉ T →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y) (Y.presheaf.stalk y)) :
    IsIso (map (T.ι ≫ f) f T.ι rfl) := by
  let φ := map (T.ι ≫ f) f T.ι rfl
  have (W : X.Opensᵒᵖ) : IsIso (φ.hom.app W) := by
    change IsIso (T.ι.appLE (f ⁻¹ᵁ W.unop)
      (T.ι ⁻¹ᵁ (f ⁻¹ᵁ W.unop)) le_rfl)
    rw [Scheme.Hom.appLE_eq_app]
    exact isIso_open_app_of_boundary_two_le_depth Y T hdepth _
  have hφ : IsIso φ.hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((TopCat.Sheaf.forget CommRingCat.{u} X).map φ) := hφ
  exact isIso_of_reflects_iso φ (TopCat.Sheaf.forget CommRingCat.{u} X)

/-- The original affine extension is recovered from the direct-image
algebra of its open part whenever its own boundary has depth at least two. -/
def relativeSpecBoundaryIso {Y X : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : Y ⟶ X) [IsAffineHom f] (T : Y.Opens)
    [(Scheme.RelativeSpec.underlyingModule (structureMap (T.ι ≫ f))).IsQuasicoherent]
    (hdepth : ∀ y : Y, y ∉ T →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y) (Y.presheaf.stalk y)) :
    RelativeSpec.scheme (structureMap (T.ι ≫ f)) ≅ Y := by
  have : (RelativeSpec.underlyingModule (structureMap f)).IsQuasicoherent :=
    isQuasicoherent_underlyingModule f
  have : IsIso (map (T.ι ≫ f) f T.ι rfl) := isIso_boundaryMap f T hdepth
  exact RelativeSpec.iso (structureMap f) (structureMap (T.ι ≫ f))
    (asIso (map (T.ι ≫ f) f T.ι rfl)) ≪≫ relativeSpecIso f

/-- Recovery of a depth-two extension retains the original map to the base. -/
@[reassoc]
theorem relativeSpecBoundaryIso_hom_toBase {Y X : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : Y ⟶ X) [IsAffineHom f] (T : Y.Opens)
    [(RelativeSpec.underlyingModule (structureMap (T.ι ≫ f))).IsQuasicoherent]
    (hdepth : ∀ y : Y, y ∉ T →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y) (Y.presheaf.stalk y)) :
    (relativeSpecBoundaryIso f T hdepth).hom ≫ f =
      RelativeSpec.toBase (structureMap (T.ι ≫ f)) := by
  have : (RelativeSpec.underlyingModule (structureMap f)).IsQuasicoherent :=
    isQuasicoherent_underlyingModule f
  change (RelativeSpec.map (structureMap f) (structureMap (T.ι ≫ f))
    (map (T.ι ≫ f) f T.ι rfl) ≫ (relativeSpecIso f).hom) ≫ f = _
  rw [Category.assoc, relativeSpecIso_hom_toBase]
  exact RelativeSpec.map_toBase _ _ _ (structureMap_map _ _ _ rfl)

end Scheme.DirectImageAlgebra
end AlgebraicGeometry
