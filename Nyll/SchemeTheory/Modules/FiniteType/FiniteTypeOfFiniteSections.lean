/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeTilde
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeSchemeRestriction
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite type from the actual finite affine section modules

For a quasicoherent native sheaf of modules, finite generation of the
modules of sections on affine opens supplies actual finite local
generating families. The proof transports the finite tilde generators
through the canonical affine counit and the open-to-slice equivalence.
No local presentation or finite-type sheaf is assumed as extra data.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite actual global sections on a spectrum give finite type of a
quasicoherent sheaf through the canonical tilde counit. -/
theorem isFiniteType_of_finite_moduleSpecΓ {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M)] : M.IsFiniteType := by
  let G : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj M
  let ε : (tilde (R := R) G : (Spec R).Modules) ⟶ M := fromTildeΓ (R := R) M
  have hε : IsIso (C := (Spec R).Modules) ε :=
    isIso_fromTildeΓ_of_isQuasicoherent (R := R) M
  let eScheme : (tilde (R := R) G : (Spec R).Modules) ≅ M :=
    asIso (C := (Spec R).Modules) ε
  let e : (show SheafOfModules.{u} (Spec R).ringCatSheaf from tilde G) ≅
      (show SheafOfModules.{u} (Spec R).ringCatSheaf from M) :=
    (sheafOfModulesEquivalence (Spec R)).functor.mapIso eScheme
  exact SheafOfModules.IsFiniteType.of_iso
    (C := (Spec R).Opens) (R := (Spec R).ringCatSheaf)
    (M := tilde G) (N := M) e (isFiniteType_tilde_of_finite G)

/-- The actual inverse restriction comparison transports finite affine
sections to the original coefficient ring of a spectrum. -/
theorem moduleFinite_moduleSpecΓ_restrict_of_finite_sections
    {X : Scheme.{u}} (M : X.Modules) {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j]
    [Module.Finite Γ(X, j ''ᵁ ⊤) Γ(M, j ''ᵁ ⊤)] :
    Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (M.restrict j)) := by
  let N : (Spec R).Modules := M.restrict j
  let σ : Γ(X, j ''ᵁ ⊤) →+* R :=
    ((j.appIso ⊤).hom ≫ (Scheme.ΓSpecIso R).hom).hom
  let e : Γ(N, ⊤) ≅ Γ(M, j ''ᵁ ⊤) := M.restrictAppIso j ⊤
  have hscalar (r : R) (x : Γ(N, ⊤)) :
      r • x = (Scheme.ΓSpecIso R).inv r • x := by
    have hid : (Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op = 𝟙 _ := by
      rw [Subsingleton.elim (⊤ : (Spec R).Opens).leTop (𝟙 _), op_id,
        CategoryTheory.Functor.map_id]
    rw [smul_Spec_def, hid]
    rfl
  let l : Γ(M, j ''ᵁ ⊤) →ₛₗ[σ] Γ(N, ⊤) :=
    { toAddHom := e.inv.hom.toAddHom
      map_smul' := by
        intro a x
        have h := congrArg (fun k : Γ(M, j ''ᵁ ⊤) ⟶ Γ(N, ⊤) => k x)
          (M.smul_restrictAppIso_inv j ⊤ a)
        change e.inv (a • x) = (j.appIso ⊤).hom a • e.inv x at h
        rw [hscalar]
        change e.inv (a • x) =
          (Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom ((j.appIso ⊤).hom a)) • e.inv x
        rw [Iso.hom_inv_id_apply]
        exact h }
  exact Module.Finite.of_surjective l (ConcreteCategory.bijective_of_isIso e.inv).surjective

/-- Finite sections on every affine open supply native finite type. The
local generators are constructed from those actual sections. -/
theorem isFiniteType_of_finite_affine_sections {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent]
    (hfinite : ∀ (U : X.Opens), IsAffineOpen U → Module.Finite Γ(X, U) Γ(M, U)) :
    M.IsFiniteType := by
  apply SheafOfModules.IsFiniteType.of_coversTop M
    (fun U : X.affineOpens => U.1)
    ((Opens.coversTop_iff X _).mpr (iSup_affineOpens_eq_top X))
  intro U
  have hU : IsAffineOpen U.1 := U.2
  let j : Spec Γ(X, U.1) ⟶ X := hU.fromSpec
  have hj : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
  have hImage : j ''ᵁ ⊤ = U.1 :=
    hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  have hfiniteImage : Module.Finite Γ(X, j ''ᵁ ⊤) Γ(M, j ''ᵁ ⊤) :=
    Eq.mp (congrArg (fun W : X.Opens => Module.Finite Γ(X, W) Γ(M, W)) hImage.symm)
      (hfinite U.1 hU)
  have hfiniteSpec : Module.Finite Γ(X, U.1)
      ((moduleSpecΓFunctor (R := Γ(X, U.1))).obj (M.restrict j)) :=
    moduleFinite_moduleSpecΓ_restrict_of_finite_sections M j
  have hSpec : (M.restrict j).IsFiniteType :=
    isFiniteType_of_finite_moduleSpecΓ (M.restrict j)
  have hOpen : ((M.restrict j).restrict hU.isoSpec.hom).IsFiniteType :=
    isFiniteType_restrictFunctor hU.isoSpec.hom (M.restrict j) hSpec
  let e : ((M.restrict j).restrict hU.isoSpec.hom) ≅ M.restrict U.1.ι :=
    ((restrictFunctorComp hU.isoSpec.hom j).app M).symm ≪≫
      (restrictFunctorCongr hU.isoSpec_hom_fromSpec).app M
  have hRestrict : (M.restrict U.1.ι).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso
      (C := U.1.toScheme.Opens) (R := U.1.toScheme.ringCatSheaf)
      (M := (M.restrict j).restrict hU.isoSpec.hom) (N := M.restrict U.1.ι)
      ((sheafOfModulesEquivalence U.1.toScheme).functor.mapIso e) hOpen
  exact isFiniteType_over_of_restrict M U.1 hRestrict

end AlgebraicGeometry.Scheme.Modules
