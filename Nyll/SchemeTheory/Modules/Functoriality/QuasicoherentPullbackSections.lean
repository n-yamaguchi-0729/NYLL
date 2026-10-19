/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.PullbackSections
import Nyll.SchemeTheory.Modules.Functoriality.PullbackSectionComposition
import Nyll.SchemeTheory.Modules.Functoriality.SpecPullbackSections
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPullback
import Nyll.SchemeTheory.Modules.Sections.AffinePullbackUnit
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Actual pullback sections for arbitrary affine opens

For a quasicoherent module, the original scalar-extension section map
is invertible whenever the two chosen opens are affine and the source
open is contained in the inverse image of the target open.

The proof uses the actual commuting square of the canonical affine
charts. The chart section equivalences are linear over the original
section rings and retain the original pullback units. Their square
comparison therefore identifies this precise scalar-adjoint map with
the already constructed spectrum map. Neither invertibility of a
comparison nor a chosen affine presentation is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

private theorem specUnit_eq_subordinate {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec R).Modules) (h : (⊤ : (Spec S).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤)
    (x : (moduleSpecΓFunctor (R := R)).obj M) :
    (pullbackUnitSections (Spec.map φ) ⊤ ⊤ h).app M x =
      (specPullbackUnitSections φ).app M x := by
  let y : Γ(M, ⊤) := x
  let N : (Spec S).Modules := (pullback (Spec.map φ)).obj M
  have h₁ := pullbackUnitSections_app_apply (Spec.map φ) ⊤ ⊤ h M y
  have h₂ := specPullbackUnitSections_app_apply φ M x
  have hi : (homOfLE h).op = 𝟙 (op (⊤ : (Spec S).Opens)) := Subsingleton.elim _ _
  have hm : N.presheaf.map (homOfLE h).op = 𝟙 (Γ(N, ⊤)) :=
    (congrArg (fun i : op (⊤ : (Spec S).Opens) ⟶ op ⊤ => N.presheaf.map i) hi).trans
      (N.presheaf.map_id (op ⊤))
  have h₃ := congrArg (fun a : Γ(N, ⊤) ⟶ Γ(N, ⊤) => a (pullbackLocalSection (Spec.map φ) y))
    hm
  exact h₁.trans (h₃.trans h₂.symm)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)

include hU hV

/-- The original scalar-extension map on affine sections of a
quasicoherent module is an isomorphism. -/
theorem isIso_pullbackSectionsMap (M : Y.Modules) [M.IsQuasicoherent] :
    IsIso (pullbackSectionsMap f U V hVU M) := by
  let R : CommRingCat.{u} := Γ(Y, U)
  let S : CommRingCat.{u} := Γ(X, V)
  let φ : R ⟶ S := f.appLE U V hVU
  let p : Spec S ⟶ Spec R := Spec.map φ
  let j : Spec S ⟶ X := hV.fromSpec
  let k : Spec R ⟶ Y := hU.fromSpec
  let hsq : j ≫ f = p ≫ k := (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU).symm
  let N : (Spec R).Modules := (pullback k).obj M
  let P : ModuleCat.{u} R := (moduleSectionsFunctor U).obj M
  let Q : ModuleCat.{u} S := (moduleSectionsFunctor V).obj ((pullback f).obj M)
  let P' : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj N
  let Q' : ModuleCat.{u} S := (moduleSpecΓFunctor (R := S)).obj ((pullback p).obj N)
  let eU : P' ≃ₗ[R] P := affineChartPullbackSectionsEquiv U hU M
  let eV : (moduleSpecΓFunctor (R := S)).obj ((pullback j).obj ((pullback f).obj M)) ≃ₗ[S]
      Q := affineChartPullbackSectionsEquiv V hV ((pullback f).obj M)
  let eSq := pullbackSquareIso f p j k hsq M
  let E : ModuleCat.{u} R ⥤ ModuleCat.{u} S := ModuleCat.extendScalars φ.hom
  let eA : E.obj P ≅ E.obj P' := E.mapIso eU.symm.toModuleIso
  let eB : Q ≅ Q' := eV.symm.toModuleIso ≪≫
    (moduleSpecΓFunctor (R := S)).mapIso eSq
  let α : E.obj P ⟶ Q := pullbackSectionsMap f U V hVU M
  let β : E.obj P' ⟶ Q' := specPullbackSectionsMap φ N
  have htop : (⊤ : (Spec S).Opens) ≤ p ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_top]
  have hunit : ∀ x : P,
      eB.hom ((pullbackUnitSections f U V hVU).app M x) =
        (specPullbackUnitSections φ).app N (eU.symm x) := by
    intro x
    let y : Γ((pullback f).obj M, V) := (pullbackUnitSections f U V hVU).app M x
    let z : Γ(N, ⊤) := (pullbackUnitSections k U ⊤ hU.fromSpec_preimage_self.ge).app M x
    have h₁ := congrArg
      (fun a : Γ((pullback j).obj ((pullback f).obj M), ⊤) => eSq.hom.app ⊤ a)
      (affineChartPullbackSectionsEquiv_symm_apply V hV ((pullback f).obj M) y)
    have h₂ := pullbackSquareIso_hom_unit f p j k hsq M U V ⊤ ⊤
      hVU hU.fromSpec_preimage_self.ge hV.fromSpec_preimage_self.ge htop x
    have h₃ := specUnit_eq_subordinate φ N htop z
    have h₄ := congrArg (fun a : P' => (specPullbackUnitSections φ).app N a)
      (affineChartPullbackSectionsEquiv_symm_apply U hU M x).symm
    exact h₁.trans (h₂.trans (h₃.trans h₄))
  have h : α ≫ eB.hom = eA.hom ≫ β := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    have h₁ := congrArg (fun y : Q => eB.hom y)
      (pullbackSectionsMap_one_tmul f U V hVU M x)
    have h₂ := specPullbackSectionsMap_one_tmul φ N (eU.symm x)
    have h₃ := ModuleCat.ExtendScalars.map_tmul φ.hom eU.symm.toModuleIso.hom (1 : S) x
    exact h₁.trans ((hunit x).trans (h₂.symm.trans (congrArg β h₃).symm))
  have : N.IsQuasicoherent := isQuasicoherent_pullback k M
  have hβ : IsIso β := isIso_specPullbackSectionsMap φ N
  have ha : IsIso eA.hom := eA.isIso_hom
  have hb : IsIso eB.hom := eB.isIso_hom
  have hr : IsIso (eA.hom ≫ β) := inferInstance
  have hl : IsIso (α ≫ eB.hom) :=
    Eq.mp (congrArg (fun a : E.obj P ⟶ Q' => IsIso a) h.symm) hr
  exact (isIso_comp_right_iff α eB.hom).mp hl

/-- Original sections of the actual affine pullback are the scalar
extension of the original sections along the actual section ring map. -/
def affinePullbackSectionsEquiv (M : Y.Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars (f.appLE U V hVU).hom).obj ((moduleSectionsFunctor U).obj M)
      ≃ₗ[Γ(X, V)]
      Γ((pullback f).obj M, V) := by
  let α := pullbackSectionsMap f U V hVU M
  have hα : IsIso α := isIso_pullbackSectionsMap f U V hU hV hVU M
  exact (asIso α).toLinearEquiv

/-- The affine pullback equivalence retains the original scalar times
the original unit section restricted to the chosen affine open. -/
theorem affinePullbackSectionsEquiv_tmul (M : Y.Modules) [M.IsQuasicoherent]
    (s : Γ(X, V)) (x : Γ(M, U)) :
    affinePullbackSectionsEquiv f U V hU hV hVU M
        (s ⊗ₜ[Γ(Y, U),(f.appLE U V hVU).hom] x) =
      s • ((pullback f).obj M).presheaf.map (homOfLE hVU).op (pullbackLocalSection f x) :=
  pullbackSectionsMap_tmul f U V hVU M s x

end AlgebraicGeometry.Scheme.Modules
