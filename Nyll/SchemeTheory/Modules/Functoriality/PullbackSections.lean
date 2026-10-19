/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Original pullback maps on sections over subordinate opens

For an open `V` contained in the inverse image of `U`, restrict the
original pullback adjunction unit to `V`. This produces a semilinear
section map for the actual coefficient homomorphism `f.appLE U V`.
Its scalar adjoint is the canonical scalar-extension map, and sends
each pure tensor to the original scalar times the restricted unit.

All maps are constructed for arbitrary modules and arbitrary opens.
Affineness and quasicoherence enter only when proving that this actual
map is invertible.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
  (hVU : V ≤ f ⁻¹ᵁ U)

/-- The restricted original pullback unit, with the original scalar
restriction along the actual map on structure sheaf sections. -/
def pullbackUnitSections :
    moduleSectionsFunctor U ⟶ pullback f ⋙ moduleSectionsFunctor V ⋙
      ModuleCat.restrictScalars (f.appLE U V hVU).hom where
  app M := by
    let P : ModuleCat.{u} Γ(Y, U) := (moduleSectionsFunctor U).obj M
    let Q : ModuleCat.{u} Γ(X, V) := (moduleSectionsFunctor V).obj ((pullback f).obj M)
    let i : V ⟶ f ⁻¹ᵁ U := homOfLE hVU
    let l : Γ(M, U) →ₛₗ[(f.appLE U V hVU).hom] Γ((pullback f).obj M, V) :=
      { toFun := fun x => ((pullback f).obj M).presheaf.map i.op (pullbackLocalSection f x)
        map_add' := by
          intro x y
          exact (congrArg (fun z : Γ((pullback f).obj M, f ⁻¹ᵁ U) =>
            ((pullback f).obj M).presheaf.map i.op z)
            (pullbackLocalSection_add f x y)).trans
              ((((pullback f).obj M).presheaf.map i.op).hom.map_add
                (pullbackLocalSection f x) (pullbackLocalSection f y))
        map_smul' := by
          intro r x
          have h₁ := congrArg (fun z : Γ((pullback f).obj M, f ⁻¹ᵁ U) =>
            ((pullback f).obj M).presheaf.map i.op z)
            (pullbackLocalSection_smul f r x)
          have h₂ := Scheme.Modules.map_smul ((pullback f).obj M) i
            (f.app U r) (pullbackLocalSection f x)
          exact h₁.trans h₂ }
    exact (ModuleCat.semilinearMapAddEquiv (f.appLE U V hVU).hom P Q) l
  naturality {M N} θ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let i : V ⟶ f ⁻¹ᵁ U := homOfLE hVU
    let θ' : (pullback f).obj M ⟶ (pullback f).obj N := (pullback f).map θ
    have h₁ := congrArg (fun z : Γ((pullback f).obj N, f ⁻¹ᵁ U) =>
      ((pullback f).obj N).presheaf.map i.op z) (pullbackLocalSection_app f θ x)
    have h₂ := congrArg
      (fun k : Γ((pullback f).obj M, f ⁻¹ᵁ U) ⟶ Γ((pullback f).obj N, V) =>
        k (pullbackLocalSection f x)) (θ'.mapPresheaf.naturality i.op)
    exact h₁.trans h₂.symm

/-- The unit section comparison is the original unit followed by
the actual restriction to the given subordinate open. -/
theorem pullbackUnitSections_app_apply (M : Y.Modules) (x : Γ(M, U)) :
    (pullbackUnitSections f U V hVU).app M x =
      ((pullback f).obj M).presheaf.map (homOfLE hVU).op (pullbackLocalSection f x) := rfl

/-- The original scalar-extension map on sections over subordinate opens. -/
def pullbackSectionsMap (M : Y.Modules) :
    (ModuleCat.extendScalars (f.appLE U V hVU).hom).obj ((moduleSectionsFunctor U).obj M) ⟶
      (moduleSectionsFunctor V).obj ((pullback f).obj M) :=
  ((ModuleCat.extendRestrictScalarsAdj (f.appLE U V hVU).hom).homEquiv
    ((moduleSectionsFunctor U).obj M)
    ((moduleSectionsFunctor V).obj ((pullback f).obj M))).symm
      ((pullbackUnitSections f U V hVU).app M)

/-- A pure tensor with one maps to the original restricted pullback unit. -/
theorem pullbackSectionsMap_one_tmul (M : Y.Modules) (x : Γ(M, U)) :
    pullbackSectionsMap f U V hVU M
        ((1 : Γ(X, V)) ⊗ₜ[Γ(Y, U),(f.appLE U V hVU).hom] x) =
      ((pullback f).obj M).presheaf.map (homOfLE hVU).op (pullbackLocalSection f x) := by
  let P : ModuleCat.{u} Γ(Y, U) := (moduleSectionsFunctor U).obj M
  let Q : ModuleCat.{u} Γ(X, V) := (moduleSectionsFunctor V).obj ((pullback f).obj M)
  let e := (ModuleCat.extendRestrictScalarsAdj (f.appLE U V hVU).hom).homEquiv P Q
  have h := congrArg
    (fun k : P ⟶ (ModuleCat.restrictScalars (f.appLE U V hVU).hom).obj Q => k x)
    (e.apply_symm_apply ((pullbackUnitSections f U V hVU).app M))
  have h₁ := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
    (pullbackSectionsMap f U V hVU M) x
  exact h₁.symm.trans h

/-- Each original pure tensor maps to its scalar multiple of the
actual pullback unit, restricted to the given open. -/
theorem pullbackSectionsMap_tmul (M : Y.Modules) (s : Γ(X, V)) (x : Γ(M, U)) :
    pullbackSectionsMap f U V hVU M (s ⊗ₜ[Γ(Y, U),(f.appLE U V hVU).hom] x) =
      s • (show (moduleSectionsFunctor V).obj ((pullback f).obj M) from
        ((pullback f).obj M).presheaf.map (homOfLE hVU).op (pullbackLocalSection f x)) := by
  have ht := ModuleCat.ExtendScalars.smul_tmul (f.appLE U V hVU).hom s (1 : Γ(X, V)) x
  have h₁ := ht.trans (congrArg
    (fun a : Γ(X, V) => a ⊗ₜ[Γ(Y, U),(f.appLE U V hVU).hom] x) (mul_one s))
  have h₂ := (pullbackSectionsMap f U V hVU M).hom.map_smul s
    ((1 : Γ(X, V)) ⊗ₜ[Γ(Y, U),(f.appLE U V hVU).hom] x)
  have h₃ := congrArg
    (fun y : (moduleSectionsFunctor V).obj ((pullback f).obj M) => s • y)
    (pullbackSectionsMap_one_tmul f U V hVU M x)
  exact (congrArg (pullbackSectionsMap f U V hVU M) h₁.symm).trans (h₂.trans h₃)

/-- The actual scalar-extension map is natural in the original module
morphism and its actual pullback. -/
theorem pullbackSectionsMap_naturality {M N : Y.Modules} (θ : M ⟶ N) :
    (ModuleCat.extendScalars (f.appLE U V hVU).hom).map ((moduleSectionsFunctor U).map θ) ≫
        pullbackSectionsMap f U V hVU N =
      pullbackSectionsMap f U V hVU M ≫
        (moduleSectionsFunctor V).map ((pullback f).map θ) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  have hmap := ModuleCat.ExtendScalars.map_tmul (f.appLE U V hVU).hom
    ((moduleSectionsFunctor U).map θ) (1 : Γ(X, V)) x
  have hunit := congrArg
    (fun k : (moduleSectionsFunctor U).obj M ⟶
      (ModuleCat.restrictScalars (f.appLE U V hVU).hom).obj
        ((moduleSectionsFunctor V).obj ((pullback f).obj N)) => k x)
    ((pullbackUnitSections f U V hVU).naturality θ)
  have hright := congrArg
    (fun y : (moduleSectionsFunctor V).obj ((pullback f).obj M) =>
      ((moduleSectionsFunctor V).map ((pullback f).map θ)) y)
    (pullbackSectionsMap_one_tmul f U V hVU M x).symm
  exact (congrArg (pullbackSectionsMap f U V hVU N) hmap).trans
    ((pullbackSectionsMap_one_tmul f U V hVU N
      (((moduleSectionsFunctor U).map θ) x)).trans (hunit.trans hright))

end AlgebraicGeometry.Scheme.Modules
