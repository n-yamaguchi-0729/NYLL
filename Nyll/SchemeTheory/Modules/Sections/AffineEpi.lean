/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Surjectivity of actual affine sections of quasicoherent epimorphisms

The native tilde--Gamma counit transports an epimorphism between
quasicoherent sheaves on a spectrum to an epimorphism of tilde modules.
Faithfulness of tilde reflects it to the actual global section map.

Restriction to the spectrum of any affine open then gives surjectivity
of the original section map on that open. The argument retains the
original sheaf morphism and the canonical restriction comparison.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasicoherent epimorphism on a spectrum is surjective on its actual
global sections. -/
theorem surjective_moduleSpecΓ_of_epi {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (φ : M ⟶ N) [Epi φ] :
    Function.Surjective ((moduleSpecΓFunctor (R := R)).map φ) := by
  let ΓM : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj M
  let ΓN : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj N
  let γ : ΓM ⟶ ΓN := (moduleSpecΓFunctor (R := R)).map φ
  let εM : (tilde.functor R).obj ΓM ⟶ M := fromTildeΓ (R := R) M
  let εN : (tilde.functor R).obj ΓN ⟶ N := fromTildeΓ (R := R) N
  have hM : IsIso (C := (Spec R).Modules) εM :=
    isIso_fromTildeΓ_of_isQuasicoherent (R := R) M
  have hN : IsIso (C := (Spec R).Modules) εN :=
    isIso_fromTildeΓ_of_isQuasicoherent (R := R) N
  let eM : (tilde.functor R).obj ΓM ≅ M := asIso (C := (Spec R).Modules) εM
  let eN : (tilde.functor R).obj ΓN ≅ N := asIso (C := (Spec R).Modules) εN
  have hnat : (tilde.functor R).map γ ≫ eN.hom = eM.hom ≫ φ :=
    (tilde.adjunction (R := R)).counit.naturality φ
  have hcomp : Epi (C := (Spec R).Modules) ((tilde.functor R).map γ ≫ eN.hom) :=
    Eq.mp (congrArg (fun a => Epi (C := (Spec R).Modules) a) hnat.symm)
      (epi_comp (C := (Spec R).Modules) eM.hom φ)
  have hγ : Epi ((tilde.functor R).map γ) :=
    (epi_comp_iff_of_isIso (C := (Spec R).Modules) ((tilde.functor R).map γ) eN.hom).mp hcomp
  have hΓ : Epi γ := (tilde.functor R).epi_of_epi_map hγ
  exact (ModuleCat.epi_iff_surjective γ).mp hΓ

/-- A native quasicoherent epimorphism is surjective on the original
sections of every affine open. -/
theorem Hom.app_surjective_of_epi_of_isAffineOpen {X : Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (φ : M ⟶ N) [Epi φ] (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (φ.app U) := by
  let j : Spec Γ(X, U) ⟶ X := hU.fromSpec
  have hj : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
  let ψ : M.restrict j ⟶ N.restrict j := (restrictFunctor j).map φ
  have hψ : Epi ψ := Functor.map_epi (restrictFunctor j) φ
  have hΓ : Function.Surjective ((moduleSpecΓFunctor (R := Γ(X, U))).map ψ) :=
    surjective_moduleSpecΓ_of_epi ψ
  have hImage : j ''ᵁ ⊤ = U :=
    j.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  have hs : Function.Surjective (φ.app (j ''ᵁ ⊤)) := by
    intro y
    let eM : Γ(M.restrict j, ⊤) ≅ Γ(M, j ''ᵁ ⊤) := M.restrictAppIso j ⊤
    let eN : Γ(N.restrict j, ⊤) ≅ Γ(N, j ''ᵁ ⊤) := N.restrictAppIso j ⊤
    obtain ⟨x, hx⟩ := hΓ (eN.inv y)
    have hx' : ψ.app ⊤ x = eN.inv y := hx
    have hnat : ψ.app ⊤ ≫ eN.hom = eM.hom ≫ φ.app (j ''ᵁ ⊤) := rfl
    refine ⟨eM.hom x, ?_⟩
    calc
      φ.app (j ''ᵁ ⊤) (eM.hom x) = eN.hom (ψ.app ⊤ x) :=
        (congrArg (fun a : Γ(M.restrict j, ⊤) ⟶ Γ(N, j ''ᵁ ⊤) => a x) hnat).symm
      _ = eN.hom (eN.inv y) := congrArg (fun z => eN.hom z) hx'
      _ = y := Iso.inv_hom_id_apply eN y
  exact Eq.mp (congrArg (fun W : X.Opens => Function.Surjective (φ.app W)) hImage) hs

end AlgebraicGeometry.Scheme.Modules
