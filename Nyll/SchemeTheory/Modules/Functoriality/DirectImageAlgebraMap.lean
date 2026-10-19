/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.DirectImageAlgebra
import Nyll.SchemeTheory.Modules.Quasicoherent.DirectImageAlgebraQuasicoherent
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeOfFiniteSections
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Actual morphisms and finite generation of direct-image algebras

A commuting triangle of schemes induces a morphism between their native
direct-image ring sheaves over the common target. Its components are the
original scheme map on sections, with the preimage-open identification
supplied by the triangle. The same components give a morphism of the
actual underlying modules.

For a finite morphism, the section algebra on every affine open is finite.
Consequently its genuine underlying sheaf is quasicoherent and of finite
type. For a closed transition, all its affine components are surjective.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.RelativeSpec

variable {X : Scheme.{u}} {A B : TopCat.Sheaf CommRingCat.{u} X}

/-- A morphism of actual algebra sheaves induces the same section maps on
the native underlying modules, using the given structural triangle. -/
def underlyingModuleMap (α : X.sheaf ⟶ A) (β : X.sheaf ⟶ B)
    (φ : A ⟶ B) (hφ : α ≫ φ = β) : underlyingModule α ⟶ underlyingModule β := by
  let f (U : X.Opensᵒᵖ) :
      (underlyingModule α).val.obj U ⟶ (underlyingModule β).val.obj U := by
    let aU : Γ(X, U.unop) →+* A.obj.obj U := (α.hom.app U).hom
    let bU : Γ(X, U.unop) →+* B.obj.obj U := (β.hom.app U).hom
    let q : A.obj.obj U →+* B.obj.obj U := (φ.hom.app U).hom
    refine ModuleCat.ofHom
      (X := (underlyingModule α).val.obj U)
      (Y := (underlyingModule β).val.obj U)
      { toFun := fun x => q (show A.obj.obj U from x)
        map_add' := fun x y => q.map_add (show A.obj.obj U from x) (show A.obj.obj U from y)
        map_smul' := ?_ }
    intro a x
    let y : A.obj.obj U := x
    change q (aU a * y) = bU a * q y
    rw [q.map_mul]
    have hU : q.comp aU = bU :=
      congrArg (fun k : X.sheaf ⟶ B => (k.hom.app U).hom) hφ
    exact congrArg (fun z : B.obj.obj U => z * q y) (RingHom.congr_fun hU a)
  refine ⟨{ app := f, naturality := ?_ }⟩
  intro U V i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun k : A.obj.obj U ⟶ B.obj.obj V => k x) (φ.hom.naturality i)

/-- The underlying-module morphism retains its original ring-section component. -/
theorem underlyingModuleMap_app_apply (α : X.sheaf ⟶ A) (β : X.sheaf ⟶ B)
    (φ : A ⟶ B) (hφ : α ≫ φ = β) (U : X.Opens) (x : A.obj.obj (op U)) :
    (underlyingModuleMap α β φ hφ).app U x = φ.hom.app (op U) x := rfl

end AlgebraicGeometry.Scheme.RelativeSpec

namespace AlgebraicGeometry.Scheme.DirectImageAlgebra

variable {T T' X : Scheme.{u}} (g : T ⟶ X) (g' : T' ⟶ X)
  (r : T ⟶ T') (h : r ≫ g' = g)

include h in
/-- The commuting triangle identifies the source preimage with the
iterated preimage required by the actual section homomorphism. -/
theorem map_preimage_le (U : X.Opens) : g ⁻¹ᵁ U ≤ r ⁻¹ᵁ (g' ⁻¹ᵁ U) := by
  subst g
  exact le_rfl

/-- Pulling back sections along a scheme map over the common target gives
the actual morphism of direct-image algebra sheaves. -/
def map : sheaf g' ⟶ sheaf g where
  hom :=
    { app U := r.appLE (g' ⁻¹ᵁ U.unop) (g ⁻¹ᵁ U.unop)
        (map_preimage_le g g' r h U.unop)
      naturality := by
        intro U V i
        change T'.presheaf.map ((Opens.map g'.base).map i.unop).op ≫
            r.appLE (g' ⁻¹ᵁ V.unop) (g ⁻¹ᵁ V.unop) _ =
          r.appLE (g' ⁻¹ᵁ U.unop) (g ⁻¹ᵁ U.unop) _ ≫
            T.presheaf.map ((Opens.map g.base).map i.unop).op
        rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map] }

/-- The actual direct-image morphism is a morphism of algebras over the
structure sheaf of the fixed target. -/
theorem structureMap_map : structureMap g' ≫ map g g' r h = structureMap g := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change g'.app U.unop ≫ r.appLE (g' ⁻¹ᵁ U.unop) (g ⁻¹ᵁ U.unop) _ = g.app U.unop
  subst g
  change g'.app U.unop ≫
      r.appLE (g' ⁻¹ᵁ U.unop) (r ⁻¹ᵁ (g' ⁻¹ᵁ U.unop)) le_rfl =
    g'.app U.unop ≫ r.app (g' ⁻¹ᵁ U.unop)
  rw [Scheme.Hom.appLE_eq_app]

/-- The genuine native-module transition underlying the algebra transition. -/
def moduleMap : RelativeSpec.underlyingModule (structureMap g') ⟶
    RelativeSpec.underlyingModule (structureMap g) :=
  RelativeSpec.underlyingModuleMap (structureMap g') (structureMap g)
    (map g g' r h) (structureMap_map g g' r h)

/-- Both transitions use the original scheme map on the actual inverse-image opens. -/
theorem moduleMap_app_apply (U : X.Opens) (x : Γ(T', g' ⁻¹ᵁ U)) :
    (moduleMap g g' r h).app U x =
      r.appLE (g' ⁻¹ᵁ U) (g ⁻¹ᵁ U) (map_preimage_le g g' r h U) x := rfl

/-- A closed transition is surjective on sections over each affine open
of the target whose preimage at the later level is affine. -/
theorem map_app_surjective [IsClosedImmersion r] (U : X.Opens)
    (hU : IsAffineOpen (g' ⁻¹ᵁ U)) : Function.Surjective ((map g g' r h).hom.app (op U)) := by
  subst g
  change Function.Surjective (r.appLE (g' ⁻¹ᵁ U) (r ⁻¹ᵁ (g' ⁻¹ᵁ U)) le_rfl)
  rw [Scheme.Hom.appLE_eq_app]
  exact r.app_surjective (g' ⁻¹ᵁ U) hU

variable {g g' r h}

/-- Every affine section of the actual finite direct-image module is
finite under its native action by base sections. -/
theorem moduleFinite_sections (g : T ⟶ X) [IsFinite g]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(RelativeSpec.underlyingModule (structureMap g), U) :=
  g.finite_app U hU

/-- A finite direct image has a native finite-type underlying module,
constructed from its actual finite affine section algebras. -/
theorem isFiniteType_underlyingModule (g : T ⟶ X) [IsFinite g] :
    (RelativeSpec.underlyingModule (structureMap g)).IsFiniteType := by
  have hQ : (RelativeSpec.underlyingModule (structureMap g)).IsQuasicoherent :=
    isQuasicoherent_underlyingModule g
  exact Modules.isFiniteType_of_finite_affine_sections
    (RelativeSpec.underlyingModule (structureMap g)) (moduleFinite_sections g)

end AlgebraicGeometry.Scheme.DirectImageAlgebra
