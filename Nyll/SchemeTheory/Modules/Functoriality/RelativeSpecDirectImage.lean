/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.AffineSourceColimit
import Nyll.SchemeTheory.Modules.Functoriality.DirectImageAlgebraMap
import Nyll.SchemeTheory.Modules.Functoriality.RelativeSpecMap
import Nyll.SchemeTheory.Modules.Quasicoherent.DirectImageAlgebraQuasicoherent
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Recovering an affine morphism from its actual direct-image algebra

The source of an affine morphism and the relative spectrum of its native
direct-image algebra are colimits of the same affine section spectra.
The uniqueness isomorphism recovers the original source, its structure
morphism, and every morphism over the base. All chart comparisons use the
original `fromSpec` and `appLE` maps of the given schemes.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.DirectImageAlgebra

variable {T T' X : Scheme.{u}}

local instance underlyingModule_isQuasicoherent (g : T ⟶ X) [IsAffineHom g] :
    (RelativeSpec.underlyingModule (structureMap g)).IsQuasicoherent :=
  isQuasicoherent_underlyingModule g

local instance diagram_isLocallyDirected (g : T ⟶ X) [IsAffineHom g] :
    ((RelativeSpec.gluingData (structureMap g)).functor ⋙
      Scheme.forget).IsLocallyDirected :=
  RelativeSpec.gluingData_isLocallyDirected (structureMap g)

/-- The original source is recovered from the literal direct-image
algebra by uniqueness of the colimit of its affine section spectra. -/
def relativeSpecIso (g : T ⟶ X) [IsAffineHom g] :
    RelativeSpec.scheme (structureMap g) ≅ T :=
  IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit (RelativeSpec.gluingData (structureMap g)).functor)
    (AffineSourceColimit.coconeIsColimit g)

/-- The recovery isomorphism sends each constructed affine chart to
the original inverse-image affine open by its original `fromSpec` morphism. -/
@[reassoc]
theorem openCover_relativeSpecIso_hom (g : T ⟶ X) [IsAffineHom g]
    (U : X.AffineZariskiSite) :
    (RelativeSpec.openCover (structureMap g)).f U ≫ (relativeSpecIso g).hom =
      (U.2.preimage g).fromSpec :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (RelativeSpec.gluingData (structureMap g)).functor)
    (AffineSourceColimit.coconeIsColimit g) U

/-- The inverse recovery map preserves the same original affine chart. -/
@[reassoc]
theorem fromSpec_relativeSpecIso_inv (g : T ⟶ X) [IsAffineHom g]
    (U : X.AffineZariskiSite) :
    (U.2.preimage g).fromSpec ≫ (relativeSpecIso g).inv =
      (RelativeSpec.openCover (structureMap g)).f U := by
  let S : Scheme.{u} := Spec Γ(T, g ⁻¹ᵁ U.1)
  let e : RelativeSpec.scheme (structureMap g) ≅ T := relativeSpecIso g
  let j : S ⟶ RelativeSpec.scheme (structureMap g) :=
    (RelativeSpec.openCover (structureMap g)).f U
  let p : S ⟶ T := (U.2.preimage g).fromSpec
  have hj : j ≫ e.hom = p := openCover_relativeSpecIso_hom g U
  calc
    p ≫ e.inv = (j ≫ e.hom) ≫ e.inv :=
      congrArg (fun k : S ⟶ T => k ≫ e.inv) hj.symm
    _ = j ≫ (e.hom ≫ e.inv) := Category.assoc j e.hom e.inv
    _ = j ≫ 𝟙 (RelativeSpec.scheme (structureMap g)) :=
      congrArg (fun k => j ≫ k) e.hom_inv_id
    _ = j := Category.comp_id j

/-- Recovery respects the given affine morphism to the original base. -/
@[reassoc]
theorem relativeSpecIso_hom_toBase (g : T ⟶ X) [IsAffineHom g] :
    (relativeSpecIso g).hom ≫ g = RelativeSpec.toBase (structureMap g) := by
  apply colimit.hom_ext
  intro U
  change (RelativeSpec.openCover (structureMap g)).f U ≫
      ((relativeSpecIso g).hom ≫ g) =
    (RelativeSpec.openCover (structureMap g)).f U ≫ RelativeSpec.toBase (structureMap g)
  rw [← Category.assoc, openCover_relativeSpecIso_hom, RelativeSpec.openCover_toBase]
  change (U.2.preimage g).fromSpec ≫ g = Spec.map (g.app U.1) ≫ U.2.fromSpec
  exact ((congrArg (fun a : Γ(X, U.1) ⟶ Γ(T, g ⁻¹ᵁ U.1) =>
      Spec.map a ≫ U.2.fromSpec) (g.app_eq_appLE (U := U.1))).trans
    (IsAffineOpen.SpecMap_appLE_fromSpec g U.2 (U.2.preimage g) le_rfl)).symm

/-- The inverse recovery isomorphism is also over the original base. -/
@[reassoc]
theorem relativeSpecIso_inv_toBase (g : T ⟶ X) [IsAffineHom g] :
    (relativeSpecIso g).inv ≫ RelativeSpec.toBase (structureMap g) = g := by
  rw [← relativeSpecIso_hom_toBase, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- A morphism over the base is recovered from its literal direct-image
algebra-section maps under the constructed relative-spectrum isomorphisms. -/
@[reassoc]
theorem relativeSpecIso_naturality (g : T ⟶ X) (g' : T' ⟶ X)
    [IsAffineHom g] [IsAffineHom g'] (r : T ⟶ T') (h : r ≫ g' = g) :
    RelativeSpec.map (structureMap g') (structureMap g) (map g g' r h) ≫
        (relativeSpecIso g').hom =
      (relativeSpecIso g).hom ≫ r := by
  apply colimit.hom_ext
  intro i
  let U : X.AffineZariskiSite := i
  let A : CommRingCat.{u} := Γ(T, g ⁻¹ᵁ U.1)
  let B : CommRingCat.{u} := Γ(T', g' ⁻¹ᵁ U.1)
  let a : B ⟶ A := (map g g' r h).hom.app (op U.1)
  let Y : Scheme.{u} := RelativeSpec.scheme (structureMap g)
  let Y' : Scheme.{u} := RelativeSpec.scheme (structureMap g')
  let e : Y ≅ T := relativeSpecIso g
  let e' : Y' ≅ T' := relativeSpecIso g'
  let j : Spec A ⟶ Y := (RelativeSpec.openCover (structureMap g)).f U
  let j' : Spec B ⟶ Y' := (RelativeSpec.openCover (structureMap g')).f U
  let p : Spec A ⟶ T := (U.2.preimage g).fromSpec
  let p' : Spec B ⟶ T' := (U.2.preimage g').fromSpec
  let f : Y ⟶ Y' := RelativeSpec.map (structureMap g') (structureMap g) (map g g' r h)
  have hf : j ≫ f = Spec.map a ≫ j' :=
    RelativeSpec.openCover_map (structureMap g') (structureMap g) (map g g' r h) U
  have hj : j ≫ e.hom = p := openCover_relativeSpecIso_hom g U
  have hj' : j' ≫ e'.hom = p' := openCover_relativeSpecIso_hom g' U
  have ha : Spec.map a ≫ p' = p ≫ r :=
    IsAffineOpen.SpecMap_appLE_fromSpec r (U.2.preimage g') (U.2.preimage g)
    (map_preimage_le g g' r h U.1)
  calc
    j ≫ (f ≫ e'.hom) = (j ≫ f) ≫ e'.hom := (Category.assoc j f e'.hom).symm
    _ = (Spec.map a ≫ j') ≫ e'.hom :=
      congrArg (fun k : Spec A ⟶ Y' => k ≫ e'.hom) hf
    _ = Spec.map a ≫ (j' ≫ e'.hom) := Category.assoc (Spec.map a) j' e'.hom
    _ = Spec.map a ≫ p' := congrArg (fun k : Spec B ⟶ T' => Spec.map a ≫ k) hj'
    _ = p ≫ r := ha
    _ = (j ≫ e.hom) ≫ r := congrArg (fun k : Spec A ⟶ T => k ≫ r) hj.symm
    _ = j ≫ (e.hom ≫ r) := Category.assoc j e.hom r

end AlgebraicGeometry.Scheme.DirectImageAlgebra
