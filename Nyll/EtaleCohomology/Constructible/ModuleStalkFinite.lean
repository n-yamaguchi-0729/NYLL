/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.LocallyConstant
public import Nyll.EtaleCohomology.Constructible.Locality
public import Nyll.EtaleCohomology.Constructible.Restriction
public import Nyll.EtaleCohomology.Sites.PointConstantFiber
public import Nyll.EtaleCohomology.Sites.PullbackStalks
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Nyll.SchemeTheory.LocalGeometry.ImmersionToField
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite generation of actual geometric module stalks

A finite type local system has its original finite constant model at every
geometric stalk. For a constructible sheaf, pull back to the geometric point
and choose its actual nonempty stratum; its immersion into the field spectrum is
an isomorphism. Existing inverse-image stalk comparisons over the separably closed field then
transport finite generation to the original stalk. The coefficient ring is
arbitrary and need not be finite or Noetherian.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

/-- Actual finite constant models supply finite generation of every
geometric stalk of a finite type local system. -/
theorem moduleFinite_geometricStalk_of_isEtaleFiniteTypeLocallyConstant
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (hG : IsEtaleFiniteTypeLocallyConstant R G)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Module.Finite R (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} R)).obj G) := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (s default)
  obtain ⟨l, hl, _⟩ :=
    Scheme.exists_fac_of_etale_of_isSepClosed (𝒰.f i) s y hy
  obtain ⟨M, hM, ⟨eM⟩⟩ := h𝒰 i
  have : Module.Finite R M := hM
  let Φ := Scheme.pointSmallEtale l
  let e : M ≅ ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} R)).obj G :=
    ((Φ.constantSheafCompFiberIso (ModuleCat.{u} R)
      (terminalIsTerminal : IsTerminal (⊤_ (𝒰.X i).Etale))).app M).symm ≪≫
      (Φ.sheafFiber (A := ModuleCat.{u} R)).mapIso eM.symm ≪≫
      (etalePullbackStalkIso (𝒰.f i) l R).app G ≪≫
      eqToIso (congrArg (fun t : Spec (.of Ω) ⟶ X =>
        ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u} R)).obj G) hl)
  exact Module.Finite.of_surjective e.hom.hom
    ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance)

/-- The affine-local constructibility definition supplies finite generation
of the original geometric stalk over a separably closed field. -/
theorem moduleFinite_geometricStalk_of_isEtaleConstructible
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (hG : IsEtaleConstructible R G)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Module.Finite R (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} R)).obj G) := by
  let GΩ := (etalePullback s R).obj G
  have hGΩ : IsEtaleConstructible R GΩ := hG.pullback s
  obtain ⟨S, hS⟩ :=
    (isEtaleConstructible_iff_hasFiniteConstructibleStratification (R := R) GΩ).mp hGΩ
  obtain ⟨i, y, _⟩ := S.cover (default : Spec (CommRingCat.of Ω))
  have : IsImmersion (S.map i) := S.isImmersion i
  have : Nonempty (S.stratum i) := ⟨y⟩
  have : IsIso (S.map i) := Scheme.isIso_of_isImmersion_toSpecField (S.map i)
  let l : Spec (CommRingCat.of Ω) ⟶ S.stratum i := inv (S.map i)
  have hl : l ≫ S.map i = 𝟙 (Spec (CommRingCat.of Ω)) :=
    IsIso.inv_hom_id (S.map i)
  have : Module.Finite R
      (((Scheme.pointSmallEtale l).sheafFiber (A := ModuleCat.{u} R)).obj
        ((etalePullback (S.map i) R).obj GΩ)) :=
    moduleFinite_geometricStalk_of_isEtaleFiniteTypeLocallyConstant _ (hS i) l
  let e :
      ((Scheme.pointSmallEtale l).sheafFiber (A := ModuleCat.{u} R)).obj
        ((etalePullback (S.map i) R).obj GΩ) ≅
      ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber
        (A := ModuleCat.{u} R)).obj GΩ :=
    (etalePullbackStalkIso (S.map i) l R).app GΩ ≪≫
      eqToIso (congrArg (fun t : Spec (.of Ω) ⟶ Spec (.of Ω) =>
        ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u} R)).obj GΩ) hl)
  have : Module.Finite R
      (((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber
        (A := ModuleCat.{u} R)).obj GΩ) :=
    Module.Finite.of_surjective e.hom.hom
      ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance)
  let e' :
      ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber
        (A := ModuleCat.{u} R)).obj GΩ ≅
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} R)).obj G :=
    (etalePullbackStalkIso s (𝟙 (Spec (.of Ω))) R).app G ≪≫
      eqToIso (congrArg (fun t : Spec (.of Ω) ⟶ X =>
        ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u} R)).obj G)
        (Category.id_comp s))
  exact Module.Finite.of_surjective e'.hom.hom
    ((ModuleCat.epi_iff_surjective e'.hom).mp inferInstance)

end EtaleCohomology
