/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Functoriality.FiniteRelativeSpec
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreeAffineSections
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Flat relative spectra and finite local bases

The constructed affine charts identify flatness of the structural map
with flatness of the original section algebras. For a finite-type algebra
over a locally Noetherian base, these are equivalent to actual finite
local bases for its underlying module sheaf; the rank is allowed to vary.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Flat affine sections of a finite-type quasicoherent sheaf give actual
finite local bases over a locally Noetherian scheme. -/
theorem finiteFreeLocus_eq_top_of_flat_affineSections
    {X : Scheme.{u}} [IsLocallyNoetherian X] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    (hflat : ∀ (U : X.Opens), IsAffineOpen U → Module.Flat Γ(X, U) Γ(M, U)) :
    finiteFreeLocus M = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := x) (U := ⊤) (Set.mem_univ x)
  have hx : x ∈ Set.range hU.fromSpec := hU.range_fromSpec.symm ▸ hxU
  obtain ⟨p, rfl⟩ := hx
  have : Module.Finite Γ(X, U) Γ(M, U) := moduleFinite_sections_of_isFiniteType M U hU
  have : Module.Flat Γ(X, U) Γ(M, U) := hflat U hU
  have : p.asIdeal.IsPrime := p.isPrime
  have : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl Γ(M, U)) :=
    Module.free_of_flat_of_isLocalRing
  exact mem_finiteFreeLocus_of_free_localized_affineSections M hU p

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.RelativeSpec

variable {X : Scheme.{u}} {A : TopCat.Sheaf CommRingCat.{u} X}
  (α : X.sheaf ⟶ A) [(underlyingModule α).IsQuasicoherent]

/-- Flatness is detected on the original affine section algebras of the
constructed relative spectrum. -/
theorem flat_toBase_iff : Flat (toBase α) ↔
    ∀ U : X.AffineZariskiSite, (α.hom.app (op U.1)).hom.Flat := by
  have hlocal : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{u}) (Q := RingHom.Flat)
  have : MorphismProperty.RespectsIso (@Flat.{u}) := hlocal.toRespects
  constructor
  · intro hf U
    have : Flat (Spec.map (α.hom.app (op U.1)) ≫ U.2.isoSpec.inv) :=
      MorphismProperty.of_isPullback (isPullback_affineModel α U).flip hf
    exact Flat.SpecMap_iff.mp
      ((MorphismProperty.cancel_right_of_respectsIso @Flat _ U.2.isoSpec.inv).mp
        (inferInstanceAs (Flat (Spec.map (α.hom.app (op U.1)) ≫ U.2.isoSpec.inv))))
  · intro hf
    apply (IsZariskiLocalAtSource.iff_of_openCover (openCover α)).mpr
    intro i
    let U : X.AffineZariskiSite := i
    have hspec : Flat (Spec.map (α.hom.app (op U.1))) := Flat.SpecMap_iff.mpr (hf U)
    have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    have hj : Flat U.2.fromSpec :=
      HasRingHomProperty.of_isOpenImmersion (P := @Flat) RingHom.Flat.containsIdentities
    have hmodel : Flat (Spec.map (α.hom.app (op U.1)) ≫ U.2.fromSpec) :=
      Flat.comp (Spec.map (α.hom.app (op U.1))) U.2.fromSpec (hf := hspec) (hg := hj)
    exact Eq.mp (congrArg Flat (openCover_toBase α U).symm) hmodel

/-- For a finite-type algebra on a locally Noetherian scheme, the actual
relative spectrum is flat precisely when its original module has finite
local bases everywhere. -/
theorem flat_toBase_iff_finiteFreeLocus_eq_top [IsLocallyNoetherian X]
    [(underlyingModule α).IsFiniteType] :
    Flat (toBase α) ↔ Modules.finiteFreeLocus (underlyingModule α) = ⊤ := by
  rw [flat_toBase_iff]
  constructor
  · intro hf
    apply Modules.finiteFreeLocus_eq_top_of_flat_affineSections
    intro U hU
    exact hf ⟨U, hU⟩
  · intro hfree U
    exact Modules.moduleFlat_sections_of_finiteFreeLocus_eq_top (underlyingModule α)
      hfree U.1 U.2

end AlgebraicGeometry.Scheme.RelativeSpec
