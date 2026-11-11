/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedPullbackSections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAlgebraObjects
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelUnit
public import Nyll.SchemeTheory.Modules.Functoriality.AlgebraObjectMap
public import Nyll.SchemeTheory.Modules.Functoriality.RelativeSpecDirectImage
public import Nyll.AlgebraicCurves.Geometry.Schemes.BaseChange.IsPullbackIsoSpecQuotientCompMorphismRestrictEq
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual relative spectrum of an algebraized adic cover

The original monoid maps give morphisms from the original closed-level
covers to the constructed relative spectrum. On every original affine
open, the quotient comparison identifies their ring maps as the quotient
by the image of the original coefficient ideal. The existing quotient
pushout theorem therefore recovers the actual affine closed-level square.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (F : X.Modules) [F.IsQuasicoherent] [MonObj F] [IsCommMonObj F]
  (n : ℕ) (σ : F ⟶ moduleSheaf f I V n) [IsMonHom σ]

local instance algebraStructure_underlyingModule_isQuasicoherent :
    (Scheme.RelativeSpec.underlyingModule (algebraStructure f I V n)).IsQuasicoherent :=
  moduleSheaf_isQuasicoherent f I V n

/-- The algebraized comparison retains the original ring sheaf of the
actual finite cover, using the existing identity-on-sections recovery. -/
def algebraizedSheafMap :
    Scheme.Modules.AlgebraObject.sheaf F ⟶ algebraSheaf f I V n :=
  Scheme.Modules.AlgebraObject.sheafMap σ ≫
    (Scheme.RelativeSpec.recoveredSheafIso (algebraStructure f I V n)).hom

omit [F.IsQuasicoherent] in
/-- The unit law retains the original structure map of the cover. -/
theorem algebraizedSheafMap_structure :
    Scheme.Modules.AlgebraObject.structureMap F ≫
      algebraizedSheafMap f I V F n σ = algebraStructure f I V n := by
  let G : X.Modules := moduleSheaf f I V n
  let α := Scheme.Modules.AlgebraObject.structureMap F
  let k : Scheme.Modules.AlgebraObject.sheaf F ⟶ Scheme.Modules.AlgebraObject.sheaf G :=
    Scheme.Modules.AlgebraObject.sheafMap σ
  let e : Scheme.Modules.AlgebraObject.sheaf G ≅ algebraSheaf f I V n :=
    Scheme.RelativeSpec.recoveredSheafIso (algebraStructure f I V n)
  have hk : α ≫ k = Scheme.Modules.AlgebraObject.structureMap G :=
    Scheme.Modules.AlgebraObject.structureMap_sheafMap σ
  have he : Scheme.Modules.AlgebraObject.structureMap G ≫ e.hom =
      algebraStructure f I V n :=
    Scheme.RelativeSpec.recoveredSheafIso_structureMap (algebraStructure f I V n)
  exact (Category.assoc α k e.hom).symm.trans
    ((congrArg (fun a => a ≫ e.hom) hk).trans he)

/-- The actual finite cover maps to the relative spectrum of the
constructed algebra object by the given original comparison. -/
def algebraizedCoverMap :
    (cover f I V n).left ⟶
      Scheme.RelativeSpec.scheme (Scheme.Modules.AlgebraObject.structureMap F) :=
  (Scheme.DirectImageAlgebra.relativeSpecIso (coverToOriginal f I V n)).inv ≫
    Scheme.RelativeSpec.map (Scheme.Modules.AlgebraObject.structureMap F)
      (algebraStructure f I V n) (algebraizedSheafMap f I V F n σ)

/-- This morphism preserves the original map to the ambient scheme. -/
@[reassoc]
theorem algebraizedCoverMap_toBase :
    algebraizedCoverMap f I V F n σ ≫
      Scheme.RelativeSpec.toBase (Scheme.Modules.AlgebraObject.structureMap F) =
        coverToOriginal f I V n := by
  let α := Scheme.Modules.AlgebraObject.structureMap F
  let β := algebraStructure f I V n
  let e : Scheme.RelativeSpec.scheme β ≅ (cover f I V n).left :=
    Scheme.DirectImageAlgebra.relativeSpecIso (coverToOriginal f I V n)
  let m : Scheme.RelativeSpec.scheme β ⟶ Scheme.RelativeSpec.scheme α :=
    Scheme.RelativeSpec.map α β (algebraizedSheafMap f I V F n σ)
  have hm : m ≫ Scheme.RelativeSpec.toBase α = Scheme.RelativeSpec.toBase β :=
    Scheme.RelativeSpec.map_toBase α β (algebraizedSheafMap f I V F n σ)
      (algebraizedSheafMap_structure f I V F n σ)
  have he : e.inv ≫ Scheme.RelativeSpec.toBase β = coverToOriginal f I V n :=
    Scheme.DirectImageAlgebra.relativeSpecIso_inv_toBase (coverToOriginal f I V n)
  exact (Category.assoc e.inv m (Scheme.RelativeSpec.toBase α)).trans
    ((congrArg (fun a => e.inv ≫ a) hm).trans he)

/-- On the original affine chart this is the spectrum of the actual
algebra map on sections, followed by the constructed affine chart. -/
@[reassoc]
theorem fromSpec_algebraizedCoverMap (U : X.AffineZariskiSite) :
    (U.2.preimage (coverToOriginal f I V n)).fromSpec ≫
        algebraizedCoverMap f I V F n σ =
      Spec.map ((algebraizedSheafMap f I V F n σ).hom.app (op U.1)) ≫
        (Scheme.RelativeSpec.openCover
          (Scheme.Modules.AlgebraObject.structureMap F)).f U := by
  let α := Scheme.Modules.AlgebraObject.structureMap F
  let β := algebraStructure f I V n
  let e : Scheme.RelativeSpec.scheme β ≅ (cover f I V n).left :=
    Scheme.DirectImageAlgebra.relativeSpecIso (coverToOriginal f I V n)
  let m : Scheme.RelativeSpec.scheme β ⟶ Scheme.RelativeSpec.scheme α :=
    Scheme.RelativeSpec.map α β (algebraizedSheafMap f I V F n σ)
  let w := (U.2.preimage (coverToOriginal f I V n)).fromSpec
  have he : w ≫ e.inv = (Scheme.RelativeSpec.openCover β).f U :=
    Scheme.DirectImageAlgebra.fromSpec_relativeSpecIso_inv (coverToOriginal f I V n) U
  have hm : (Scheme.RelativeSpec.openCover β).f U ≫ m =
      Spec.map ((algebraizedSheafMap f I V F n σ).hom.app (op U.1)) ≫
        (Scheme.RelativeSpec.openCover α).f U :=
    Scheme.RelativeSpec.openCover_map α β (algebraizedSheafMap f I V F n σ) U
  exact (Category.assoc w e.inv m).symm.trans
    ((congrArg (fun a => a ≫ m) he).trans hm)

variable
  [IsIso ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I n))).map σ)]

/-- The original affine comparison is surjective, because it factors
as the original closed-level quotient followed by the proved comparison. -/
theorem algebraizedSheafMap_app_surjective (U : X.affineOpens) :
    Function.Surjective
      ((algebraizedSheafMap f I V F n σ).hom.app (op U.1)).hom := by
  let Q : X.Modules := levelPullbackModule f I F n
  let e : Q ≅ moduleSheaf f I V n := moduleSheafLevelQuotientIso f I V F n σ
  have he : Function.Surjective (e.hom.app U.1) :=
    (ConcreteCategory.bijective_of_isIso (e.hom.app U.1)).surjective
  have hη := levelPullbackUnit_app_surjective f I F n U
  have hc : ∀ x : Γ(F, U.1),
      e.hom.app U.1 ((levelPullbackUnit f I F n).app U.1 x) = σ.app U.1 x := by
    intro x
    exact congrArg (fun k : F ⟶ moduleSheaf f I V n => k.app U.1 x)
      (levelUnit_moduleSheafLevelQuotientIso_hom f I V F n σ)
  intro y
  obtain ⟨z, hz⟩ := he y
  obtain ⟨x, hx⟩ := hη z
  refine ⟨x, ?_⟩
  change σ.app U.1 x = y
  exact (hc x).symm.trans ((congrArg (e.hom.app U.1) hx).trans hz)

/-- The actual ring comparison has the image of the original closed
coefficient ideal as its kernel. The section algebra retains the native
scalar action, so the existing module-kernel formula applies directly. -/
theorem algebraizedSheafMap_app_ker (U : X.affineOpens) :
    RingHom.ker ((algebraizedSheafMap f I V F n σ).hom.app (op U.1)).hom =
      (RingHom.ker
        ((Limits.pullback.fst f (baseInclusion I n)).app U.1).hom).map
          (Scheme.Modules.AlgebraObject.coefficientMap F U.1) := by
  let R : CommRingCat.{u} := Γ(X, U.1)
  let C : CommRingCat.{u} := Scheme.Modules.AlgebraObject.sectionRing F U.1
  let _ : Algebra R C := Scheme.Modules.AlgebraObject.sectionAlgebra F U.1
  let J : Ideal R := (sectionsIdeal f I U.1) ^ (n + 1)
  let Q : X.Modules := levelPullbackModule f I F n
  let e : Q ≅ moduleSheaf f I V n := moduleSheafLevelQuotientIso f I V F n σ
  have he : Function.Injective (e.hom.app U.1) :=
    (ConcreteCategory.bijective_of_isIso (e.hom.app U.1)).injective
  have hc : ∀ x : Γ(F, U.1),
      e.hom.app U.1 ((levelPullbackUnit f I F n).app U.1 x) = σ.app U.1 x := by
    intro x
    exact congrArg (fun k : F ⟶ moduleSheaf f I V n => k.app U.1 x)
      (levelUnit_moduleSheafLevelQuotientIso_hom f I V F n σ)
  rw [levelProjection_app_ker]
  change RingHom.ker ((algebraizedSheafMap f I V F n σ).hom.app (op U.1)).hom =
    J.map (algebraMap R C)
  ext x
  change σ.app U.1 x = 0 ↔ x ∈ J.map (algebraMap R C)
  have hz : σ.app U.1 x = 0 ↔ (levelPullbackUnit f I F n).app U.1 x = 0 := by
    rw [← hc x]
    exact map_eq_zero_iff (e.hom.app U.1).hom he
  have hJ : x ∈ J • (⊤ : Submodule R C) ↔ x ∈ J.map (algebraMap R C) :=
    Iff.of_eq (congrArg (fun S : Submodule R C => x ∈ S)
      (Ideal.smul_top_eq_map (R := R) (S := C) J))
  exact hz.trans ((levelPullbackUnit_app_eq_zero_iff f I F n U x).trans hJ)

private theorem actualRingSquare_isPushout
    {R R₀ C B : Type u} [CommRing R] [CommRing R₀] [CommRing C] [CommRing B]
    (π : R →+* R₀) (c : R →+* C) (q : C →+* B) (b : R₀ →+* B)
    (hπ : Function.Surjective π) (hq : Function.Surjective q)
    (hker : RingHom.ker q = (RingHom.ker π).map c)
    (hcomm : q.comp c = b.comp π) :
    IsPushout (CommRingCat.ofHom c) (CommRingCat.ofHom π)
      (CommRingCat.ofHom q) (CommRingCat.ofHom b) := by
  let J : Ideal C := (RingHom.ker π).map c
  let e : C ⧸ J ≃+* B :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hq)
  have he (x : C) : e (Ideal.Quotient.mk J x) = q x := by
    change RingHom.quotientKerEquivOfSurjective hq
      (Ideal.quotEquivOfEq hker.symm (Ideal.Quotient.mk J x)) = q x
    rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  let τ : R₀ →+* C ⧸ J :=
    AlgebraicCurves.Geometry.Schemes.Proofs.QuotientPullback.E163TC.tau π hπ c
  have hτ (x : R₀) : e (τ x) = b x := by
    obtain ⟨r, rfl⟩ := hπ x
    rw [AlgebraicCurves.Geometry.Schemes.Proofs.QuotientPullback.E163TC.tau_apply]
    exact (he (c r)).trans (RingHom.congr_fun hcomm r)
  have hp :=
    AlgebraicCurves.Geometry.Schemes.Proofs.QuotientPullback.E163TC.isPushout_quotient
      π hπ c
  apply hp.of_iso (Iso.refl (CommRingCat.of R)) (Iso.refl (CommRingCat.of C))
    (Iso.refl (CommRingCat.of R₀)) e.toCommRingCatIso
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · apply CommRingCat.hom_ext
    exact RingHom.ext he
  · apply CommRingCat.hom_ext
    exact RingHom.ext hτ

/-- The actual affine rings of the closed cover form the required
pushout of the original base ring and the algebraized section ring. -/
theorem algebraizedSheafMap_affine_isPushout (U : X.affineOpens) :
    let i : level f I n ⟶ X := Limits.pullback.fst f (baseInclusion I n)
    IsPushout
      ((Scheme.Modules.AlgebraObject.structureMap F).hom.app (op U.1))
      (i.app U.1)
      ((algebraizedSheafMap f I V F n σ).hom.app (op U.1))
      ((cover f I V n).hom.app (i ⁻¹ᵁ U.1)) := by
  intro i
  apply actualRingSquare_isPushout
    (i.app U.1).hom (Scheme.Modules.AlgebraObject.coefficientMap F U.1)
    ((algebraizedSheafMap f I V F n σ).hom.app (op U.1)).hom
    ((cover f I V n).hom.app (i ⁻¹ᵁ U.1)).hom
  · exact Scheme.Hom.app_surjective i U.1 U.2
  · exact algebraizedSheafMap_app_surjective f I V F n σ U
  · exact algebraizedSheafMap_app_ker f I V F n σ U
  · apply RingHom.ext
    intro r
    have h := congrArg (fun k : X.sheaf ⟶ algebraSheaf f I V n =>
      k.hom.app (op U.1) r) (algebraizedSheafMap_structure f I V F n σ)
    exact h

private theorem algebraizedCoverMap_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback
      (Spec.map ((algebraizedSheafMap f I V F n σ).hom.app (op U.1)))
      ((U.2.preimage (coverToOriginal f I V n)).fromSpec ≫ (cover f I V n).hom)
      ((Scheme.RelativeSpec.openCover
        (Scheme.Modules.AlgebraObject.structureMap F)).f U ≫
          Scheme.RelativeSpec.toBase (Scheme.Modules.AlgebraObject.structureMap F))
      (Limits.pullback.fst f (baseInclusion I n)) := by
  let i : level f I n ⟶ X := Limits.pullback.fst f (baseInclusion I n)
  let c : (cover f I V n).left ⟶ level f I n := (cover f I V n).hom
  let g : (cover f I V n).left ⟶ X := coverToOriginal f I V n
  let hU₀ : IsAffineOpen (i ⁻¹ᵁ U.1) := U.2.preimage i
  have hbase :
      IsPullback (Spec.map (i.app U.1)) hU₀.fromSpec U.2.fromSpec i := by
    apply IsOpenImmersion.isPullback
    · have h := IsAffineOpen.SpecMap_appLE_fromSpec i U.2 hU₀ le_rfl
      exact ((congrArg (fun k => Spec.map k ≫ U.2.fromSpec)
        (i.app_eq_appLE (U := U.1))).trans h).symm
    · rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec]
  have hp := algebraizedSheafMap_affine_isPushout f I V F n σ ⟨U.1, U.2⟩
  have hs := isPullback_SpecMap_of_isPushout
    ((Scheme.Modules.AlgebraObject.structureMap F).hom.app (op U.1))
    (i.app U.1)
    ((algebraizedSheafMap f I V F n σ).hom.app (op U.1))
    (c.app (i ⁻¹ᵁ U.1)) hp
  have h := hs.paste_vert hbase
  have hleft :
      Spec.map (c.app (i ⁻¹ᵁ U.1)) ≫ hU₀.fromSpec =
        (U.2.preimage g).fromSpec ≫ c := by
    have hc := IsAffineOpen.SpecMap_appLE_fromSpec c hU₀ (U.2.preimage g) le_rfl
    exact (congrArg (fun k => Spec.map k ≫ hU₀.fromSpec)
      (c.app_eq_appLE (U := i ⁻¹ᵁ U.1))).trans hc
  have hright :
      Spec.map ((Scheme.Modules.AlgebraObject.structureMap F).hom.app (op U.1)) ≫
          U.2.fromSpec =
        (Scheme.RelativeSpec.openCover
          (Scheme.Modules.AlgebraObject.structureMap F)).f U ≫
            Scheme.RelativeSpec.toBase (Scheme.Modules.AlgebraObject.structureMap F) :=
    (Scheme.RelativeSpec.openCover_toBase
      (Scheme.Modules.AlgebraObject.structureMap F) U).symm
  let t := Spec.map ((algebraizedSheafMap f I V F n σ).hom.app (op U.1))
  exact Eq.mp
    (congrArg₂
      (fun (l : Spec Γ((cover f I V n).left, g ⁻¹ᵁ U.1) ⟶ level f I n)
        (r : Spec ((Scheme.Modules.AlgebraObject.sheaf F).obj.obj (op U.1)) ⟶ X) =>
          IsPullback t l r i) hleft hright) h

/-- The actual morphism from every original closed-level cover is the
base change of the constructed relative spectrum. Both projections are
the original morphisms, including the original closed-level inclusion. -/
theorem algebraizedCoverMap_isPullback :
    IsPullback (algebraizedCoverMap f I V F n σ) (cover f I V n).hom
      (Scheme.RelativeSpec.toBase (Scheme.Modules.AlgebraObject.structureMap F))
      (Limits.pullback.fst f (baseInclusion I n)) := by
  let α := Scheme.Modules.AlgebraObject.structureMap F
  let Z : Scheme.{u} := Scheme.RelativeSpec.scheme α
  let p : Z ⟶ X := Scheme.RelativeSpec.toBase α
  let r : (cover f I V n).left ⟶ Z := algebraizedCoverMap f I V F n σ
  let c : (cover f I V n).left ⟶ level f I n := (cover f I V n).hom
  let i : level f I n ⟶ X := Limits.pullback.fst f (baseInclusion I n)
  let g : (cover f I V n).left ⟶ X := coverToOriginal f I V n
  let 𝒰 : Z.OpenCover := Scheme.RelativeSpec.openCover α
  apply Scheme.isPullback_of_openCover r c p i 𝒰
  intro U
  let w : Spec Γ((cover f I V n).left, g ⁻¹ᵁ U.1) ⟶ (cover f I V n).left :=
    (U.2.preimage g).fromSpec
  let z : Spec ((Scheme.Modules.AlgebraObject.sheaf F).obj.obj (op U.1)) ⟶ Z := 𝒰.f U
  let t : Spec Γ((cover f I V n).left, g ⁻¹ᵁ U.1) ⟶
      Spec ((Scheme.Modules.AlgebraObject.sheaf F).obj.obj (op U.1)) :=
    Spec.map ((algebraizedSheafMap f I V F n σ).hom.app (op U.1))
  have : IsOpenImmersion z := 𝒰.map_prop U
  have : IsOpenImmersion w := IsAffineOpen.isOpenImmersion_fromSpec (U.2.preimage g)
  have hw : w ≫ r = t ≫ z := fromSpec_algebraizedCoverMap f I V F n σ U
  have hrange : r ⁻¹ᵁ z.opensRange = w.opensRange := by
    have hpU : p ⁻¹ᵁ U.1 = z.opensRange := Scheme.RelativeSpec.toBase_preimage α U
    have hrp : r ≫ p = g := algebraizedCoverMap_toBase f I V F n σ
    have hwU : w.opensRange = g ⁻¹ᵁ U.1 :=
      IsAffineOpen.opensRange_fromSpec (U.2.preimage g)
    calc
      r ⁻¹ᵁ z.opensRange = r ⁻¹ᵁ (p ⁻¹ᵁ U.1) :=
        congrArg (fun W : Z.Opens => r ⁻¹ᵁ W) hpU.symm
      _ = (r ≫ p) ⁻¹ᵁ U.1 := (Scheme.Hom.comp_preimage r p U.1).symm
      _ = g ⁻¹ᵁ U.1 :=
        congrArg (fun k : (cover f I V n).left ⟶ X => k ⁻¹ᵁ U.1) hrp
      _ = w.opensRange := hwU.symm
  have hchart : IsPullback t w z r := IsOpenImmersion.isPullback t w z r hw hrange
  let e : Spec Γ((cover f I V n).left, g ⁻¹ᵁ U.1) ≅ Limits.pullback r z :=
    hchart.flip.isoPullback
  have hlocal : IsPullback t (w ≫ c) (z ≫ p) i :=
    algebraizedCoverMap_chart_isPullback f I V F n σ U
  change IsPullback (Limits.pullback.snd r z) (Limits.pullback.fst r z ≫ c) (z ≫ p) i
  apply hlocal.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · exact (Category.comp_id t).trans hchart.flip.isoPullback_hom_snd.symm
  · calc
      (w ≫ c) ≫ (Iso.refl _).hom = w ≫ c := Category.comp_id _
      _ = (e.hom ≫ Limits.pullback.fst r z) ≫ c :=
        congrArg (fun k => k ≫ c) hchart.flip.isoPullback_hom_fst.symm
      _ = e.hom ≫ (Limits.pullback.fst r z ≫ c) := Category.assoc _ _ _
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
