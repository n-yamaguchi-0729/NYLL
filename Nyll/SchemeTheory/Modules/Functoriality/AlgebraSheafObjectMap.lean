/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Functoriality.AlgebraSheafObject
public import Nyll.SchemeTheory.Modules.Functoriality.AlgebraObjectSheaf
public import Nyll.SchemeTheory.Modules.Functoriality.DirectImageAlgebraMap
public import Nyll.SchemeTheory.Modules.Functoriality.RelativeSpecMap

/-!
# Algebra-sheaf recovery and the actual transition morphisms

The canonical algebra object on the underlying module recovers the original
ring sheaf and its structural map. An actual morphism of algebra sheaves
preserves its unit and multiplication as native module morphisms. Consequently
the transition maps of a finite-cover tower have exactly the algebraic
compatibility required when their underlying module maps are algebraized.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativeSpec

variable {X : Scheme.{u}} {A B : TopCat.Sheaf CommRingCat.{u} X}
  (α : X.sheaf ⟶ A) (β : X.sheaf ⟶ B)

/-- The original algebra-sheaf morphism preserves the canonical native
monoid structures, including the actual tensor-product multiplication. -/
instance underlyingModuleMapIsMonHom (φ : A ⟶ B) (hφ : α ≫ φ = β) :
    IsMonHom (underlyingModuleMap α β φ hφ) where
  one_hom := by
    apply Modules.hom_ext
    intro U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro r
    have h₁ := congrArg ((underlyingModuleMap α β φ hφ).app U)
      (underlyingModule_one_app α U r)
    have h₂ := congrArg (fun f : X.sheaf ⟶ B => f.hom.app (op U) r) hφ
    exact h₁.trans (h₂.trans (underlyingModule_one_app β U r).symm)
  mul_hom := by
    apply Modules.tensor_hom_ext
    intro U x y
    let a : A.obj.obj (op U) := x
    let b : A.obj.obj (op U) := y
    let m : underlyingModule α ⟶ underlyingModule β := underlyingModuleMap α β φ hφ
    have ht := Modules.tensorHom_app_tensorSections m m (U := U) x y
    have h₁ := congrArg (m.app U) (underlyingModule_mul_app α U a b)
    have h₂ := (φ.hom.app (op U)).hom.map_mul a b
    have h₃ := (underlyingModule_mul_app β U
      (φ.hom.app (op U) a) (φ.hom.app (op U) b)).symm
    have h₄ := congrArg (μ[underlyingModule β].app U) ht.symm
    exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- The recovered ring structure is the original ring structure on sections. -/
def recoveredSectionRingEquiv (U : X.Opens) :
    Modules.AlgebraObject.sectionRing (underlyingModule α) U ≃+* A.obj.obj (op U) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := underlyingModule_mul_app α U x y
  map_add' _ _ := rfl

/-- Recovering the ring sheaf from its native algebra object gives the
original sheaf, by the identity on each original section. -/
def recoveredSheafIso :
    Modules.AlgebraObject.sheaf (underlyingModule α) ≅ A := by
  apply (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X)
    CommRingCat.{u}).preimageIso
  refine NatIso.ofComponents
    (fun U => (recoveredSectionRingEquiv α U.unop).toCommRingCatIso) ?_
  intro U V i
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  rfl

/-- The recovery isomorphism carries the native unit back to the original
map from the structure sheaf. -/
theorem recoveredSheafIso_structureMap :
    Modules.AlgebraObject.structureMap (underlyingModule α) ≫
      (recoveredSheafIso α).hom = α := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact underlyingModule_one_app α U.unop r

/-- The two constructions of the relative spectrum agree by the actual
identity-on-sections algebra recovery, without choosing new affine models. -/
def recoveredRelativeSpecIso [(underlyingModule α).IsQuasicoherent] :
    scheme α ≅ scheme (Modules.AlgebraObject.structureMap (underlyingModule α)) :=
  iso (Modules.AlgebraObject.structureMap (underlyingModule α)) α
    (recoveredSheafIso α)

/-- The recovered relative spectrum has the original structure morphism. -/
@[reassoc]
theorem recoveredRelativeSpecIso_toBase [(underlyingModule α).IsQuasicoherent] :
    (recoveredRelativeSpecIso α).hom ≫
      toBase (Modules.AlgebraObject.structureMap (underlyingModule α)) = toBase α :=
  map_toBase _ _ _ (recoveredSheafIso_structureMap α)

end AlgebraicGeometry.Scheme.RelativeSpec

namespace AlgebraicGeometry.Scheme.Modules.AlgebraObject

variable {X : Scheme.{u}} (F : X.Modules) [MonObj F] [IsCommMonObj F]

/-- Recovery of an algebra object preserves its original unit and
multiplication, not only its underlying additive sheaf. -/
instance underlyingModuleIso_hom_isMonHom : IsMonHom (underlyingModuleIso F).hom where
  one_hom := by
    apply Modules.hom_ext
    intro U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro r
    have h₁ := underlyingModuleIso_hom_app F U
      (η[RelativeSpec.underlyingModule (structureMap F)].app U r)
    have h₂ := RelativeSpec.underlyingModule_one_app (structureMap F) U r
    exact h₁.trans (h₂.trans (coefficientMap_apply F U r))
  mul_hom := by
    apply Modules.tensor_hom_ext
    intro U x y
    let S : X.Modules := RelativeSpec.underlyingModule (structureMap F)
    let e : S ≅ F := underlyingModuleIso F
    let a : sectionRing F U := x
    let b : sectionRing F U := y
    have ht := Modules.tensorHom_app_tensorSections e.hom e.hom (U := U) x y
    have h₁ := underlyingModuleIso_hom_app F U (μ[S].app U (Modules.tensorSections x y))
    have h₂ := RelativeSpec.underlyingModule_mul_app (structureMap F) U a b
    have h₃ := sectionRing_mul F U a b
    have h₄ := congrArg (μ[F].app U) ht.symm
    exact h₁.trans (h₂.trans (h₃.trans h₄))

end AlgebraicGeometry.Scheme.Modules.AlgebraObject
