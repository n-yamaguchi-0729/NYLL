/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreeLocus
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeAffineSections
public import Nyll.SchemeTheory.Modules.Frames.BasisMapEqIsAffineOpen
public import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionCounit
public import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
public import Nyll.SchemeTheory.Modules.Functoriality.QuasicoherentPullbackSections
public import Nyll.SchemeTheory.Modules.Sections.InverseLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Localization.Module

/-!
# Native finite local bases from free affine sections

The existing affine pullback section comparison transports a finite
basis to every smaller affine open. Its original unit formula identifies
these basis vectors with restrictions of the original sections. The
existing affine-basis gluing theorem supplies all smaller opens.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]

/-- A finite basis on an affine open restricts to actual compatible
bases on all smaller opens of a quasicoherent module sheaf. -/
theorem isFiniteFreeOn_of_basis_affine {U : X.Opens} (hU : IsAffineOpen U)
    {n : ℕ} (b : Module.Basis (Fin n) Γ(X, U) Γ(M, U)) :
    IsFiniteFreeOn M U := by
  refine ⟨n, b, forall_exists_basis_map_eq_of_forall_isAffineOpen M b ?_⟩
  intro W hWU hW
  let adj := pullbackPushforwardAdjunction (𝟙 X)
  let κ : (pullback (𝟙 X)).obj M ⟶ M :=
    (adj.homEquiv M M).symm ((pushforwardId X).inv.app M)
  have : IsIso (adj.counit.app M) :=
    isIso_pullbackCounit_of_isClosedImmersion (𝟙 X) M
  have : IsIso κ := by
    change IsIso ((adj.homEquiv M M).symm ((pushforwardId X).inv.app M))
    rw [Adjunction.homEquiv_counit]
    infer_instance
  let R : CommRingCat.{u} := Γ(X, U)
  let S : CommRingCat.{u} := Γ(X, W)
  let ρ : R ⟶ S := Scheme.Hom.appLE (𝟙 X) U W hWU
  let _algebra : Algebra R S := ρ.hom.toAlgebra
  let e₀ : S ⊗[R] Γ(M, U) ≃ₗ[S] Γ((pullback (𝟙 X)).obj M, W) :=
    affinePullbackSectionsEquiv (𝟙 X) U W hU hW hWU M
  let e₁ : Γ((pullback (𝟙 X)).obj M, W) ≃ₗ[S] Γ(M, W) :=
    ((moduleSectionsFunctor W).mapIso (asIso κ)).toLinearEquiv
  let e : S ⊗[R] Γ(M, U) ≃ₗ[S] Γ(M, W) := e₀.trans e₁
  refine ⟨(b.baseChange S).map e, ?_⟩
  intro i
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply]
  change e₁ (e₀ ((1 : S) ⊗ₜ[R] b i)) =
    M.presheaf.map (homOfLE hWU).op (b i)
  have ht : e₀ ((1 : S) ⊗ₜ[R] b i) =
      (1 : S) • ((pullback (𝟙 X)).obj M).presheaf.map (homOfLE hWU).op
        (pullbackLocalSection (𝟙 X) (b i)) :=
    affinePullbackSectionsEquiv_tmul (𝟙 X) U W hU hW hWU M 1 (b i)
  rw [ht, one_smul]
  have hres := map_homOfLE_pullbackLocalSection (𝟙 X) hWU (b i)
  change κ.app W
      (((pullback (𝟙 X)).obj M).presheaf.map (homOfLE hWU).op
        (pullbackLocalSection (𝟙 X) (b i))) =
    M.presheaf.map (homOfLE hWU).op (b i)
  exact (congrArg
    (fun z : Γ((pullback (𝟙 X)).obj M, (𝟙 X) ⁻¹ᵁ W) =>
      κ.app ((𝟙 X) ⁻¹ᵁ W) z) hres).trans
    (homEquiv_symm_app_pullbackLocalSection (𝟙 X)
      ((pushforwardId X).inv.app M) (M.presheaf.map (homOfLE hWU).op (b i)))

/-- Finite free original affine sections give an original local
trivialization, without assuming a separate sheaf comparison. -/
theorem isFiniteFreeOn_of_free_affineSections {U : X.Opens} (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) Γ(M, U)] [Module.Free Γ(X, U) Γ(M, U)] :
    IsFiniteFreeOn M U := by
  classical
  let K := Module.Free.ChooseBasisIndex Γ(X, U) Γ(M, U)
  let b : Module.Basis (Fin (Fintype.card K)) Γ(X, U) Γ(M, U) :=
    (Module.Free.chooseBasis Γ(X, U) Γ(M, U)).reindex (Fintype.equivFin K)
  exact isFiniteFreeOn_of_basis_affine M hU b

/-- The actual quasicoherent sections on a basic open inherit
freeness from their canonical localized section module. -/
theorem moduleFree_basicOpen_sections_of_free_localizedModule
    {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U))
    [Module.Free (Localization.Away r) (LocalizedModule.Away r Γ(M, U))] :
    Module.Free Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) := by
  have : IsAffine U.toScheme := hU
  have hUqs : IsQuasiSeparated (U : Set X) := by
    apply (isQuasiSeparated_iff_quasiSeparatedSpace (U : Set X) U.2).mpr
    change QuasiSeparatedSpace U.toScheme
    infer_instance
  let R : CommRingCat.{u} := Γ(X, U)
  let S : CommRingCat.{u} := Γ(X, X.basicOpen r)
  let ρ : R →+* S := (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let _algebra : Algebra R S := ρ.toAlgebra
  let B : ModuleCat.{u} S := ModuleCat.of S Γ(M, X.basicOpen r)
  let _moduleR : Module R B := Module.compHom B ρ
  have : IsScalarTower R S B := IsScalarTower.of_compHom R S B
  have : IsLocalization.Away r S := hU.isLocalization_basicOpen r
  let l : Γ(M, U) →ₗ[R] B :=
    (M.val.map (homOfLE (X.basicOpen_le r)).op).hom
  have : IsLocalizedModule.Away r l :=
    isLocalizedModule_basicOpen_of_isQuasicoherent_of_qcqs M hU.isCompact hUqs r
  let L := Localization.Away r
  let a : L ≃ₐ[R] S := IsLocalization.algEquiv (Submonoid.powers r) L S
  let _moduleL : Module L B := Module.compHom B a.toRingHom
  have : IsScalarTower R L B := IsScalarTower.of_algebraMap_smul fun c x => by
    change a (algebraMap R L c) • x = c • x
    rw [a.commutes]
    exact IsScalarTower.algebraMap_smul S c x
  let e : LocalizedModule.Away r Γ(M, U) ≃ₗ[R] B :=
    IsLocalizedModule.iso (Submonoid.powers r) l
  let eL := e.extendScalarsOfIsLocalization (Submonoid.powers r) L
  have : Module.Free L B := Module.Free.of_equiv eL
  let ident : B →ₛₗ[a.toRingHom] B :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have : RingHomInvPair a.toRingHom a.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv a.toRingEquiv
  have : RingHomInvPair a.symm.toRingHom a.toRingHom :=
    RingHomInvPair.symm a.toRingHom a.symm.toRingHom
  let eS : B ≃ₛₗ[a.toRingHom] B :=
    LinearEquiv.ofBijective ident Function.bijective_id
  exact Module.Free.of_equiv eS

/-- Freeness of the localization of finite affine sections at a point
gives an actual finite local basis near that point. -/
theorem mem_finiteFreeLocus_of_free_localized_affineSections
    [IsLocallyNoetherian X] [M.IsFiniteType]
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum Γ(X, U))
    [Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl Γ(M, U))] :
    hU.fromSpec p ∈ finiteFreeLocus M := by
  have : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.Finite Γ(X, U) Γ(M, U) :=
    moduleFinite_sections_of_isFiniteType M U hU
  have : Module.FinitePresentation Γ(X, U) Γ(M, U) :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨r, hr, hfree, _hrank⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl Γ(M, U))
      (Localization.AtPrime p.asIdeal)
  have : Module.Free (Localization.Away r) (LocalizedModule.Away r Γ(M, U)) := hfree
  have : Module.Free Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
    moduleFree_basicOpen_sections_of_free_localizedModule M hU r
  have : Module.Finite Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
    moduleFinite_sections_of_isFiniteType M (X.basicOpen r) (hU.basicOpen r)
  apply (mem_finiteFreeLocus_iff M (hU.fromSpec p)).mpr
  refine ⟨X.basicOpen r, ?_, isFiniteFreeOn_of_free_affineSections M (hU.basicOpen r)⟩
  change p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r
  rw [hU.fromSpec_preimage_basicOpen]
  exact hr

end AlgebraicGeometry.Scheme.Modules
