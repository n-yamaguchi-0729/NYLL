/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Functoriality.AlgebraObjectSections
public import Nyll.SchemeTheory.Modules.Functoriality.AlgebraObjectSheaf
public import Nyll.SchemeTheory.Modules.Functoriality.AlgebraSheafObjectMap
public import Nyll.SchemeTheory.Modules.Functoriality.RelativeSpecMap
public import Nyll.SchemeTheory.Modules.Tensor.TensorSectionMaps

/-!
# Algebra-object morphisms on the actual sheaves and relative spectra

A native module morphism preserving the unit and multiplication induces
ring homomorphisms on the already constructed section rings. Its original
restriction naturality gives a morphism of those ring sheaves, and the
unit identity gives the structure-sheaf triangle. The existing relative
spectrum construction therefore supplies the original scheme morphism
over the base. Recovery of the underlying module retains the given map.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Modules.AlgebraObject

variable {X : Scheme.{u}} {F G : X.Modules}
  [MonObj F] [IsCommMonObj F] [MonObj G] [IsCommMonObj G]
  (φ : F ⟶ G) [IsMonHom φ]

/-- The original section map preserves the already constructed ring operations. -/
def sectionRingMap (U : X.Opens) : sectionRing F U →+* sectionRing G U where
  toFun x := φ.app U x
  map_zero' := (φ.app U).hom.map_zero
  map_add' := (φ.app U).hom.map_add
  map_one' := by
    have h₁ := congrArg (φ.app U) (sectionRing_one F U)
    have h₂ : φ.app U (η[F].app U (unitSection U)) =
        η[G].app U (unitSection U) :=
      congrArg (fun a : (𝟙_ X.Modules) ⟶ G => a.app U (unitSection U))
        (IsMonHom.one_hom φ)
    exact h₁.trans (h₂.trans (sectionRing_one G U).symm)
  map_mul' x y := by
    let a : Γ(F, U) := x
    let b : Γ(F, U) := y
    have h₁ := congrArg (φ.app U) (sectionRing_mul F U a b)
    have h₂ : φ.app U (μ[F].app U (tensorSections a b)) =
        μ[G].app U ((φ ⊗ₘ φ).app U (tensorSections a b)) :=
      congrArg (fun k : F ⊗ F ⟶ G => k.app U (tensorSections a b))
        (IsMonHom.mul_hom φ)
    have h₃ := congrArg (μ[G].app U)
      (tensorHom_app_tensorSections φ φ (U := U) a b)
    have h₄ := (sectionRing_mul G U (φ.app U a) (φ.app U b)).symm
    exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- The ring homomorphism has the original native section function. -/
theorem sectionRingMap_apply (U : X.Opens) (x : Γ(F, U)) :
    sectionRingMap φ U x = (show sectionRing G U from φ.app U x) := rfl

/-- The original unit identity identifies the two coefficient maps. -/
theorem sectionRingMap_coefficientMap (U : X.Opens) (r : Γ(X, U)) :
    sectionRingMap φ U (coefficientMap F U r) = coefficientMap G U r := by
  have h₁ := congrArg (φ.app U) (coefficientMap_apply F U r)
  have h₂ : φ.app U (η[F].app U r) = η[G].app U r :=
    congrArg (fun a : (𝟙_ X.Modules) ⟶ G => a.app U r) (IsMonHom.one_hom φ)
  exact h₁.trans (h₂.trans (coefficientMap_apply G U r).symm)

/-- The native module map defines a morphism of the actual algebra sheaves. -/
def sheafMap : sheaf F ⟶ sheaf G where
  hom :=
    { app U := ConcreteCategory.ofHom (C := CommRingCat)
        (X := sectionRing F U.unop) (Y := sectionRing G U.unop)
        (sectionRingMap φ U.unop)
      naturality := by
        intro U V i
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro x
        exact congrArg (fun k : Γ(F, U.unop) ⟶ Γ(G, V.unop) => k x)
          (φ.mapPresheaf.naturality i) }

/-- Its component is the ring homomorphism of the original section types. -/
theorem sheafMap_app (U : X.Opens) :
    ((sheafMap φ).hom.app (op U)).hom = sectionRingMap φ U := rfl

/-- The native unit compatibility is exactly the structure-sheaf triangle. -/
theorem structureMap_sheafMap : structureMap F ≫ sheafMap φ = structureMap G := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact sectionRingMap_coefficientMap φ U.unop r

/-- The recovered native module morphism is the original morphism under
the existing identity-on-sections recovery isomorphisms. -/
theorem underlyingModuleMap_sheafMap :
    RelativeSpec.underlyingModuleMap (structureMap F) (structureMap G)
        (sheafMap φ) (structureMap_sheafMap φ) ≫ (underlyingModuleIso G).hom =
      (underlyingModuleIso F).hom ≫ φ := by
  apply Modules.hom_ext
  intro U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  rfl

/-- The induced morphism of the actual relative spectra reverses the
original algebra-object morphism. -/
def relativeSpecMap [F.IsQuasicoherent] [G.IsQuasicoherent] :
    RelativeSpec.scheme (structureMap G) ⟶ RelativeSpec.scheme (structureMap F) :=
  RelativeSpec.map (structureMap F) (structureMap G) (sheafMap φ)

/-- The constructed scheme morphism is over the original base. -/
@[reassoc]
theorem relativeSpecMap_toBase [F.IsQuasicoherent] [G.IsQuasicoherent] :
    relativeSpecMap φ ≫ RelativeSpec.toBase (structureMap F) =
      RelativeSpec.toBase (structureMap G) :=
  RelativeSpec.map_toBase (structureMap F) (structureMap G) (sheafMap φ)
    (structureMap_sheafMap φ)

/-- On each original affine chart, the map is the spectrum of the
native section-ring homomorphism. -/
@[reassoc]
theorem openCover_relativeSpecMap [F.IsQuasicoherent] [G.IsQuasicoherent]
    (U : X.AffineZariskiSite) :
    (RelativeSpec.openCover (structureMap G)).f U ≫ relativeSpecMap φ =
      Spec.map ((sheafMap φ).hom.app (op U.1)) ≫
        (RelativeSpec.openCover (structureMap F)).f U :=
  RelativeSpec.openCover_map (structureMap F) (structureMap G) (sheafMap φ) U

end AlgebraicGeometry.Scheme.Modules.AlgebraObject

namespace AlgebraicGeometry.Scheme.RelativeSpec

variable {X : Scheme.{u}} {A B : TopCat.Sheaf CommRingCat.{u} X}
  (α : X.sheaf ⟶ A) (β : X.sheaf ⟶ B) (φ : A ⟶ B) (hφ : α ≫ φ = β)

/-- The new construction recovers an existing algebra-sheaf morphism
through the already constructed algebra-sheaf recovery isomorphisms. -/
theorem sheafMap_underlyingModuleMap :
    Modules.AlgebraObject.sheafMap (underlyingModuleMap α β φ hφ) ≫
        (recoveredSheafIso β).hom = (recoveredSheafIso α).hom ≫ φ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  rfl

end AlgebraicGeometry.Scheme.RelativeSpec
