/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Functoriality.FiniteRelativeSpec
public import Nyll.SchemeTheory.Modules.Sections.IhomSections
public import Nyll.SchemeTheory.Modules.Tensor.TensorSectionBraiding
public import Nyll.SchemeTheory.Modules.Tensor.PresheafPullbackMonoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorSectionMaps
public import Nyll.SchemeTheory.Modules.Tensor.TensorSectionNaturality
public import Nyll.SchemeTheory.Modules.Tensor.TensorSectionSheafification
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal

/-!
# The native algebra object of a sheaf of commutative algebras

The existing lax monoidal restriction-of-scalars functor carries the unit
monoid over the algebra sheaf to its underlying module presheaf. Monoidal
sheafification and its counit transport this monoid to the native underlying
module sheaf. Its unit and multiplication retain the original structural
map and ring multiplication on every open.

This supplies the algebra structures on the actual finite-cover module
sheaves, before any formal algebraization of their underlying modules.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativeSpec

variable {X : Scheme.{u}} {A : TopCat.Sheaf CommRingCat.{u} X}
  (α : X.sheaf ⟶ A)

/-- The monoid object on the underlying presheaf induced by restriction of scalars. -/
@[instance_reducible]
def presheafMonObj : MonObj (underlyingModule α).val :=
  Functor.monObjObj
    (F := PresheafOfModules.restrictScalars
      (PresheafOfModules.ringCatHom α.hom))
    (𝟙_ (PresheafOfModulesOfCommRing.{u} A.obj))

private def presheafMul :
    (underlyingModule α).val ⊗ (underlyingModule α).val ⟶
      (underlyingModule α).val :=
  let : MonObj (underlyingModule α).val := presheafMonObj α
  μ[(underlyingModule α).val]

local instance presheafSectionsModule (P : X.PresheafOfModules) (U : X.Opens) :
    Module Γ(X, U) (P.obj (op U)) := (P.obj (op U)).isModule

private theorem presheafMul_app (U : X.Opens) (x y : A.obj.obj (op U)) :
    (presheafMul α).app (op U)
      ((x : (underlyingModule α).val.obj (op U)) ⊗ₜ[Γ(X, U)]
        (y : (underlyingModule α).val.obj (op U))) = x * y := by
  let r : Γ(X, U) →+* A.obj.obj (op U) := (α.hom.app (op U)).hom
  let M : ModuleCat (A.obj.obj (op U)) := 𝟙_ (ModuleCat (A.obj.obj (op U)))
  let S : ModuleCat Γ(X, U) := (ModuleCat.restrictScalars r).obj M
  change (λ_ M).hom
      ((Functor.LaxMonoidal.μ (ModuleCat.restrictScalars r) M M)
        ((x : S) ⊗ₜ[Γ(X, U)] (y : S))) = x * y
  rw [ModuleCat.restrictScalars_μ_tmul]
  exact ModuleCat.MonoidalCategory.leftUnitor_hom_apply (M := M) x y

/-- Sheafifying the underlying presheaf recovers the original sheaf of modules. -/
def nativeCounitIso (F : X.Modules) :
    (Modules.sheafify X).obj F.val ≅ F :=
  SheafOfModules.sheafifyCounitIso X.sheaf.obj X.ringCatSheaf.property F

/-- The actual algebra sheaf has a canonical monoid structure on its native
underlying module. The tensor is the existing sheaf tensor product. -/
instance underlyingModuleMonObj : MonObj (underlyingModule α) := by
  let : MonObj (underlyingModule α).val := presheafMonObj α
  let : MonObj ((Modules.sheafify X).obj (underlyingModule α).val) :=
    Functor.monObjObj (F := Modules.sheafify X) (underlyingModule α).val
  exact MonObj.ofIso (nativeCounitIso (underlyingModule α))

private theorem counitIso_inv_app (F : X.Modules) (U : X.Opens)
    (x : Γ(F, U)) :
    (nativeCounitIso F).inv.app U x =
      ((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app F.val).app
        (op U) x := by
  let e : (Modules.sheafify X).obj F.val ≅ F := nativeCounitIso F
  have h := SheafOfModules.counit_val_app_unit F (op U) x
  have he := congrArg (fun y => e.inv.app U y) h
  have hid := congrArg (fun f : (Modules.sheafify X).obj F.val ⟶
      (Modules.sheafify X).obj F.val =>
    f.app U (((SheafOfModules.sheafifyAdj
      X.sheaf.obj X.ringCatSheaf.property).unit.app F.val).app (op U) x))
    e.hom_inv_id
  exact he.symm.trans hid

/-- Multiplication on the native tensor sections is the original section-ring
multiplication, rather than a new operation on the underlying section type. -/
theorem underlyingModule_mul_app (U : X.Opens) (x y : A.obj.obj (op U)) :
    μ[underlyingModule α].app U (Modules.tensorSections x y) = x * y := by
  let F : X.Modules := underlyingModule α
  let SF : X.Modules := (Modules.sheafify X).obj F.val
  let e : SF ≅ F := nativeCounitIso F
  let c : SF ⊗ SF ⟶ (Modules.sheafify X).obj (F.val ⊗ F.val) :=
    Functor.LaxMonoidal.μ (Modules.sheafify X) F.val F.val
  let m : (Modules.sheafify X).obj (F.val ⊗ F.val) ⟶ SF :=
    (Modules.sheafify X).map (presheafMul α)
  let adj := SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property
  let t : (F.val ⊗ F.val).obj (op U) :=
    (x : F.val.obj (op U)) ⊗ₜ[Γ(X, U)] (y : F.val.obj (op U))
  have ht := Modules.tensorHom_app_tensorSections e.inv e.inv
    (U := U) (show Γ(F, U) from x) (show Γ(F, U) from y)
  have hu := congrArg₂
    (fun (s t : Γ(SF, U)) => Modules.tensorSections s t)
    (counitIso_inv_app F U x) (counitIso_inv_app F U y)
  have hc := Modules.sheafify_mu_app_tensorSections F.val F.val
    (U := U) (show F.val.obj (op U) from x) (show F.val.obj (op U) from y)
  have hm := SheafOfModules.sheafify_map_val_app_unit
    (J := Opens.grothendieckTopology X)
    (𝒪 := X.sheaf.obj) (h𝒪 := X.ringCatSheaf.property) (presheafMul α) (op U) t
  have h₁ := congrArg
    (fun z : Γ(SF ⊗ SF, U) => e.hom.app U (m.app U (c.app U z))) ht
  have h₂ := congrArg
    (fun z : Γ(SF ⊗ SF, U) => e.hom.app U (m.app U (c.app U z))) hu
  have h₃ := congrArg
    (fun z : Γ((Modules.sheafify X).obj (F.val ⊗ F.val), U) =>
      e.hom.app U (m.app U z)) hc
  have h₄ := congrArg (fun z : Γ(SF, U) => e.hom.app U z) hm
  have h₅ := congrArg (fun z : F.val.obj (op U) =>
    e.hom.app U ((adj.unit.app F.val).app (op U) z)) (presheafMul_app α U x y)
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans
    (h₅.trans (SheafOfModules.counit_val_app_unit F (op U) (x * y))))))

/-- The unit morphism is precisely the original structural map on every
open, with the original restricted scalar action. -/
theorem underlyingModule_one_app (U : X.Opens) (r : Γ(X, U)) :
    η[underlyingModule α].app U r = α.hom.app (op U) r := by
  let F : X.Modules := underlyingModule α
  let a : A.obj.obj (op U) := η[F].app U r
  let u : Γ(F, U) := (1 : A.obj.obj (op U))
  have h := congrArg (fun f : (𝟙_ X.Modules) ⊗ F ⟶ F =>
    f.app U (Modules.tensorSections r u)) (MonObj.one_mul F)
  have ht := Modules.whiskerRight_app_tensorSections (η[F]) F (U := U) r u
  have hs : (r • u : Γ(F, U)) = α.hom.app (op U) r * (1 : A.obj.obj (op U)) := rfl
  have hm := (underlyingModule_mul_app α U a (1 : A.obj.obj (op U))).symm.trans
    ((congrArg (μ[F].app U) ht.symm).trans
      (h.trans ((Modules.leftUnitor_hom_app_tensorSections r u).trans hs)))
  exact (mul_one a).symm.trans (hm.trans (mul_one (α.hom.app (op U) r)))

/-- Ring commutativity on actual sections makes the native algebra object
commutative for the existing sheaf braiding. -/
instance underlyingModuleIsCommMonObj : IsCommMonObj (underlyingModule α) where
  mul_comm := by
    apply Modules.tensor_hom_ext
    intro U x y
    let a : A.obj.obj (op U) := x
    let b : A.obj.obj (op U) := y
    have h := Modules.braiding_hom_app_tensorSections (U := U) x y
    change μ[underlyingModule α].app U
        ((β_ (underlyingModule α) (underlyingModule α)).hom.app U
          (Modules.tensorSections x y)) =
      μ[underlyingModule α].app U (Modules.tensorSections x y)
    exact (congrArg (μ[underlyingModule α].app U) h).trans
      ((underlyingModule_mul_app α U b a).trans
        ((mul_comm b a).trans (underlyingModule_mul_app α U a b).symm))

end AlgebraicGeometry.Scheme.RelativeSpec
