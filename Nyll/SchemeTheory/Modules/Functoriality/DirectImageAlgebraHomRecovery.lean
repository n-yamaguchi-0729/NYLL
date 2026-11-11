/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Functoriality.RelativeSpecDirectImage
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Faithfulness and reconstruction for actual direct-image algebra maps

The direct-image algebra detects maps to an affine morphism even when the
source is not affine over the base. For two affine morphisms, every map of
their actual direct-image algebras reconstructs a scheme map, with that
same algebra map and the original triangle over the base.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.RelativeSpec

/-- The actual sectionwise spectrum construction detects algebra maps. -/
theorem map_injective {X : Scheme.{u}} {A B : TopCat.Sheaf CommRingCat.{u} X}
    (α : X.sheaf ⟶ A) (β : X.sheaf ⟶ B)
    [(underlyingModule α).IsQuasicoherent] [(underlyingModule β).IsQuasicoherent] :
    Function.Injective (map α β) := by
  intro φ ψ h
  apply Sheaf.hom_ext
  have hBasis : Opens.IsBasis (Set.range (fun U : X.affineOpens => U.1)) := by
    simpa only [Subtype.range_coe] using X.isBasis_affineOpens
  apply TopCat.Sheaf.hom_ext A.obj B hBasis
  intro U
  let V : X.AffineZariskiSite := ⟨U.1, U.2⟩
  have : IsOpenImmersion ((openCover α).f V) := (openCover α).map_prop V
  apply Spec.map_injective
  apply (cancel_mono ((openCover α).f V)).mp
  exact (openCover_map α β φ V).symm.trans
    ((congrArg (fun k => (openCover β).f V ≫ k) h).trans (openCover_map α β ψ V))

end AlgebraicGeometry.Scheme.RelativeSpec

namespace AlgebraicGeometry.Scheme.DirectImageAlgebra

variable {T T' T'' X : Scheme.{u}}

/-- The actual algebra maps reverse the original scheme composition. -/
theorem map_comp (f : T ⟶ X) (g : T' ⟶ X) (h : T'' ⟶ X)
    (r : T ⟶ T') (s : T' ⟶ T'') (hr : r ≫ g = f) (hs : s ≫ h = g) :
    map f h (r ≫ s) ((Category.assoc r s h).trans
      ((congrArg (fun k => r ≫ k) hs).trans hr)) =
      map g h s hs ≫ map f g r hr := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact (Scheme.Hom.appLE_comp_appLE r s (h ⁻¹ᵁ U.unop)
    (g ⁻¹ᵁ U.unop) (f ⁻¹ᵁ U.unop)
    (map_preimage_le g h s hs U.unop) (map_preimage_le f g r hr U.unop)).symm

private theorem resLE_appTop_eq (r : T ⟶ T') (U : T'.Opens) (V : T.Opens)
    (hr : V ≤ r ⁻¹ᵁ U) :
    (r.resLE U V hr).appTop = U.topIso.hom ≫ r.appLE U V hr ≫ V.topIso.inv :=
  Scheme.Hom.resLE_app_top r hr

private theorem open_ι_comp_eq_of_appLE_eq
    (r s : T ⟶ T') (U : T'.Opens) (V : T.Opens) [IsAffine U.toScheme]
    (hr : V ≤ r ⁻¹ᵁ U) (hs : V ≤ s ⁻¹ᵁ U)
    (h : r.appLE U V hr = s.appLE U V hs) : V.ι ≫ r = V.ι ≫ s := by
  have hres : r.resLE U V hr = s.resLE U V hs := by
    apply ext_of_isAffine
    rw [resLE_appTop_eq r U V hr, resLE_appTop_eq s U V hs, h]
  exact (Scheme.Hom.resLE_comp_ι r hr).symm.trans
    ((congrArg (fun k : V.toScheme ⟶ U.toScheme => k ≫ U.ι) hres).trans
      (Scheme.Hom.resLE_comp_ι s hs))

private theorem open_ι_comp_eq_of_map_eq
    (f : T ⟶ X) (g : T' ⟶ X) [IsAffineHom g]
    (r s : T ⟶ T') (hr : r ≫ g = f) (hs : s ≫ g = f)
    (h : map f g r hr = map f g s hs) (U : X.Opens) (hU : IsAffineOpen U) :
    (f ⁻¹ᵁ U).ι ≫ r = (f ⁻¹ᵁ U).ι ≫ s := by
  have : IsAffine (g ⁻¹ᵁ U).toScheme := hU.preimage g
  apply open_ι_comp_eq_of_appLE_eq r s (g ⁻¹ᵁ U) (f ⁻¹ᵁ U)
    (map_preimage_le f g r hr U) (map_preimage_le f g s hs U)
  exact congrArg (fun k : sheaf g ⟶ sheaf f => k.hom.app (op U)) h

/-- Maps to an affine morphism are detected by the original direct-image
algebra, with no affineness assumption on the source. -/
theorem hom_ext (f : T ⟶ X) (g : T' ⟶ X) [IsAffineHom g]
    (r s : T ⟶ T') (hr : r ≫ g = f) (hs : s ≫ g = f)
    (h : map f g r hr = map f g s hs) : r = s := by
  let C := T.openCoverOfIsOpenCover (fun U : X.affineOpens => f ⁻¹ᵁ U.1)
    (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top X))
  apply C.hom_ext
  intro U
  exact open_ι_comp_eq_of_map_eq f g r s hr hs h U.1 U.2

attribute [local instance] underlyingModule_isQuasicoherent

/-- Reconstruct a map between the original affine sources from a map of
their original direct-image algebras. -/
def homOfAlgebraMap (f : T ⟶ X) (g : T' ⟶ X)
    [IsAffineHom f] [IsAffineHom g] (φ : sheaf g ⟶ sheaf f) : T ⟶ T' :=
  (relativeSpecIso f).inv ≫
    RelativeSpec.map (structureMap g) (structureMap f) φ ≫ (relativeSpecIso g).hom

/-- The structural algebra identity gives the original triangle over the base. -/
@[reassoc]
theorem homOfAlgebraMap_toBase (f : T ⟶ X) (g : T' ⟶ X)
    [IsAffineHom f] [IsAffineHom g] (φ : sheaf g ⟶ sheaf f)
    (hφ : structureMap g ≫ φ = structureMap f) : homOfAlgebraMap f g φ ≫ g = f := by
  change ((relativeSpecIso f).inv ≫
    RelativeSpec.map (structureMap g) (structureMap f) φ ≫ (relativeSpecIso g).hom) ≫ g = f
  rw [Category.assoc, Category.assoc, relativeSpecIso_hom_toBase,
    RelativeSpec.map_toBase _ _ _ hφ, relativeSpecIso_inv_toBase]

/-- Reconstruction recovers the supplied actual algebra map, not merely
an abstract isomorphic algebra. -/
theorem map_homOfAlgebraMap (f : T ⟶ X) (g : T' ⟶ X)
    [IsAffineHom f] [IsAffineHom g] (φ : sheaf g ⟶ sheaf f)
    (hφ : structureMap g ≫ φ = structureMap f) :
    map f g (homOfAlgebraMap f g φ) (homOfAlgebraMap_toBase f g φ hφ) = φ := by
  apply RelativeSpec.map_injective (structureMap g) (structureMap f)
  apply (cancel_mono (relativeSpecIso g).hom).mp
  rw [relativeSpecIso_naturality f g (homOfAlgebraMap f g φ)]
  change (relativeSpecIso f).hom ≫ ((relativeSpecIso f).inv ≫
    RelativeSpec.map (structureMap g) (structureMap f) φ ≫ (relativeSpecIso g).hom) = _
  rw [Iso.hom_inv_id_assoc]

end AlgebraicGeometry.Scheme.DirectImageAlgebra
