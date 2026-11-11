/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Sheaves.IdealSheafModule
public import Nyll.SchemeTheory.Sheaves.IdealSheafDataRangeModuleIotaAppInjective
public import Nyll.SchemeTheory.Modules.Submodules.FiniteAffineSectionSubmodule
public import Nyll.SchemeTheory.Modules.Quasicoherent.DirectImageAlgebraQuasicoherent
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentImage
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPushforward
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentAffineLocalization
public import Nyll.SchemeTheory.Modules.Sections.InverseLimit
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite-type subideals of an actual ideal sheaf

A quasicoherent module map into the structure module gives an actual ideal
sheaf through its affine section images. The existing finite-type submodule
extension theorem, applied inside the original ideal module, supplies finite
subideals containing any prescribed affine-local ideal section. Consequently
the directed family of these actual finite subideals exhausts the original
ideal, with no Noetherian assumption on the scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The actual ideal module is quasicoherent because the quotient map is affine. -/
theorem isQuasicoherent_module (I : X.IdealSheafData) : I.module.IsQuasicoherent := by
  have : (show X.Modules from SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Modules.isQuasicoherent_unit X
  have : (show I.subscheme.Modules from
      SheafOfModules.unit I.subscheme.ringCatSheaf).IsQuasicoherent :=
    Modules.isQuasicoherent_unit I.subscheme
  have : ((SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf)).IsQuasicoherent :=
    Modules.isQuasicoherent_pushforward_of_isAffineHom
      I.subschemeι (SheafOfModules.unit I.subscheme.ringCatSheaf)
  exact SheafOfModules.isQuasicoherent_kernel_native I.subschemeι.unitToPushforwardUnit

/-- The section map into the tensor unit, with the target written as the
original structure ring and carrying its original multiplication action. -/
def moduleMapToRingSections (M : X.Modules) (φ : M ⟶ 𝟙_ X.Modules) (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(X, U) where
  toFun := φ.app U
  map_add' x y := map_add (φ.app U).hom x y
  map_smul' r x := Modules.Hom.app_smul φ r x

/-- The actual affine section images of a quasicoherent module map form an ideal sheaf. -/
def ofModuleMap (M : X.Modules) [M.IsQuasicoherent] (φ : M ⟶ 𝟙_ X.Modules) :
    X.IdealSheafData where
  ideal U := LinearMap.range (moduleMapToRingSections M φ U.1)
  map_ideal_basicOpen U f := by
    let V : X.Opens := X.basicOpen f
    let ρ : Γ(X, U.1) →+* Γ(X, V) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
    have hnat (x : Γ(M, U.1)) :
        moduleMapToRingSections M φ V
            (M.presheaf.map (homOfLE (X.basicOpen_le f)).op x) =
          ρ (moduleMapToRingSections M φ U.1 x) :=
      ConcreteCategory.congr_hom
        (φ.mapPresheaf.naturality (homOfLE (X.basicOpen_le f)).op) x
    change Ideal.map ρ (LinearMap.range (moduleMapToRingSections M φ U.1)) =
      LinearMap.range (moduleMapToRingSections M φ V)
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      rintro _ ⟨x, rfl⟩
      exact ⟨M.presheaf.map (homOfLE (X.basicOpen_le f)).op x, hnat x⟩
    · rintro _ ⟨y, rfl⟩
      obtain ⟨n, x, hx⟩ := (Modules.basicOpenLocalization_of_isQuasicoherent M U f).1 y
      have hmem : ρ (moduleMapToRingSections M φ U.1 x) ∈
          Ideal.map ρ (LinearMap.range (moduleMapToRingSections M φ U.1)) :=
        Ideal.mem_map_of_mem ρ ⟨x, rfl⟩
      have hunit : IsUnit (ρ (f ^ n)) := by
        rw [map_pow]
        exact (RingedSpace.isUnit_res_basicOpen X.toRingedSpace f).pow n
      have hmul : ρ (f ^ n) • moduleMapToRingSections M φ V y ∈
          Ideal.map ρ (LinearMap.range (moduleMapToRingSections M φ U.1)) := by
        rw [← hnat x, hx, map_smul] at hmem
        exact hmem
      exact (Submodule.smul_mem_iff_of_isUnit _ hunit).mp hmul

/-- The constructed ideal retains the literal affine section map. -/
theorem ofModuleMap_ideal (M : X.Modules) [M.IsQuasicoherent]
    (φ : M ⟶ 𝟙_ X.Modules) (U : X.affineOpens) :
    (ofModuleMap M φ).ideal U =
      LinearMap.range (moduleMapToRingSections M φ U.1) := rfl

/-- A finite-type source gives a finitely generated ideal on every affine open. -/
theorem fg_ofModuleMap_ideal (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (φ : M ⟶ 𝟙_ X.Modules) (U : X.affineOpens) :
    ((ofModuleMap M φ).ideal U).FG := by
  have : Module.Finite Γ(X, U.1) Γ(M, U.1) :=
    Modules.moduleFinite_sections_of_isFiniteType M U.1 U.2
  exact Submodule.fg_range (moduleMapToRingSections M φ U.1)

/-- A prescribed section of an actual ideal on an affine open belongs to
an actual subideal which is finitely generated on every affine open. -/
theorem exists_finite_subideal_containing_section
    [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (U : X.affineOpens) (a : Γ(X, U.1)) (ha : a ∈ I.ideal U) :
    ∃ J : X.IdealSheafData, J ≤ I ∧ (∀ V : X.affineOpens, (J.ideal V).FG) ∧
      a ∈ J.ideal U := by
  have : I.module.IsQuasicoherent := isQuasicoherent_module I
  have ha' : a ∈ Set.range (I.moduleι.app U.1) := by
    rw [(I.range_moduleIota_app_and_injective U).1]
    exact ha
  obtain ⟨x, hx⟩ := ha'
  obtain ⟨N, hNqc, hNft, hNx⟩ :=
    Modules.exists_finiteType_submodule_containing_sections_of_isCompact
      (show SheafOfModules.{u} X.ringCatSheaf from I.module) U.1 U.2.isCompact
      (fun _ : PUnit.{u + 1} => x)
  let M : X.Modules := N.toSheafOfModules
  have : M.IsQuasicoherent := hNqc
  have : M.IsFiniteType := hNft
  let ι : M ⟶ I.module := (Modules.sheafOfModulesEquivalence X).inverse.map N.ι
  let φ : M ⟶ 𝟙_ X.Modules := ι ≫ I.moduleι
  refine ⟨ofModuleMap M φ, ?_, fg_ofModuleMap_ideal M φ, ?_⟩
  · intro V
    rintro _ ⟨y, rfl⟩
    have hy : I.moduleι.app V.1 (ι.app V.1 y) ∈ Set.range (I.moduleι.app V.1) :=
      ⟨ι.app V.1 y, rfl⟩
    rw [(I.range_moduleIota_app_and_injective V).1] at hy
    exact hy
  · refine ⟨⟨x, hNx PUnit.unit⟩, ?_⟩
    exact hx

/-- The finite subideal family is an actual subtype of the ideal-sheaf lattice. -/
abbrev FiniteSubideal (I : X.IdealSheafData) :=
  {J : X.IdealSheafData // J ≤ I ∧ ∀ U : X.affineOpens, (J.ideal U).FG}

instance (I : X.IdealSheafData) : Nonempty (FiniteSubideal I) :=
  ⟨⟨⊥, bot_le, fun _ => Submodule.fg_bot⟩⟩

instance (I : X.IdealSheafData) : IsDirected (FiniteSubideal I) (· ≤ ·) where
  directed J K :=
    ⟨⟨J.1 ⊔ K.1, sup_le J.2.1 K.2.1,
      fun U => Submodule.FG.sup (J.2.2 U) (K.2.2 U)⟩,
      (le_sup_left : J.1 ≤ J.1 ⊔ K.1), (le_sup_right : K.1 ≤ J.1 ⊔ K.1)⟩

/-- The actual finite subideals exhaust every affine component of the original ideal. -/
theorem finiteSubideals_exhaustive [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (U : X.affineOpens) (a : Γ(X, U.1)) :
    a ∈ I.ideal U ↔ ∃ J : FiniteSubideal I, a ∈ J.1.ideal U := by
  constructor
  · intro ha
    obtain ⟨J, hJI, hJfg, haJ⟩ := exists_finite_subideal_containing_section I U a ha
    exact ⟨⟨J, hJI, hJfg⟩, haJ⟩
  · rintro ⟨J, haJ⟩
    exact J.2.1 U haJ

/-- The original ideal is the supremum of its constructed finite subideals. -/
theorem iSup_finiteSubideals [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) : ⨆ J : FiniteSubideal I, J.1 = I := by
  apply le_antisymm
  · exact iSup_le fun J => J.2.1
  · intro U a ha
    obtain ⟨J, hJ⟩ := (finiteSubideals_exhaustive I U a).mp ha
    exact (le_iSup (fun J : FiniteSubideal I => J.1) J) U hJ

end AlgebraicGeometry.Scheme.IdealSheafData
