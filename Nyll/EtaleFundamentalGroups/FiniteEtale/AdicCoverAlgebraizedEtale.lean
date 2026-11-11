/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAlgebraizedRelativeSpec
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreeLocus
public import Nyll.SchemeTheory.Modules.Functoriality.RelativeSpecEtaleBasicOpen
public import Nyll.SchemeTheory.RingTheory.Descent.AlgebraizedRingEtaleNeighborhood
public import Nyll.SchemeTheory.Etale.FiniteNeighborhoodSection
public import Nyll.SchemeTheory.Cohomology.Sheaves.ModulePresheafLerayQuasicoherentRelHPresheafChow
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Étaleness of the actual algebraized relative spectrum

The native finite locally free module supplies finite flat section
algebras. The original closed-level comparison gives their actual quotient
pushouts. The local algebra criterion produces étale basic opens around
every closed-fiber point, and the existing relative-spectrum charts
identify these with the original structure morphism. Universal closedness
over the local base makes these neighborhoods cover the whole base scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Opposite TopologicalSpace
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules
open AlgebraicCurves.Cohomology.Sheaves.Proofs
open OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow.AlgebraicGeometry.OModulePresheaf.Leray

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] [MonObj F] [IsCommMonObj F]
  (σ : F ⟶ moduleSheaf f I V 0) [IsMonHom σ]
  [IsIso ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I 0))).map σ)]

include σ in
/-- The actual affine section algebra is étale on a basic neighborhood of
each coefficient prime lying on the original closed level. -/
theorem algebraizedSection_exists_etale_basicOpen
    (hF : finiteFreeLocus F = ⊤) (U : X.AffineZariskiSite)
    (p : PrimeSpectrum Γ(X, U.1))
    (hp : RingHom.ker
      ((Limits.pullback.fst f (baseInclusion I 0)).app U.1).hom ≤ p.asIdeal) :
    ∃ r : Γ(X, U.1), r ∉ p.asIdeal ∧
      ((algebraMap (AlgebraObject.sectionRing F U.1)
          (Localization.Away (AlgebraObject.coefficientMap F U.1 r))).comp
        (AlgebraObject.coefficientMap F U.1)).Etale := by
  let R : CommRingCat.{u} := Γ(X, U.1)
  let C : CommRingCat.{u} := AlgebraObject.sectionRing F U.1
  let i : level f I 0 ⟶ X := Limits.pullback.fst f (baseInclusion I 0)
  let g : (cover f I V 0).left ⟶ level f I 0 := (cover f I V 0).hom
  let π := i.app U.1
  let c : R ⟶ C := (AlgebraObject.structureMap F).hom.app (op U.1)
  let q := (algebraizedSheafMap f I V F 0 σ).hom.app (op U.1)
  let b := g.app (i ⁻¹ᵁ U.1)
  have hfinite : c.hom.Finite := by
    let _ : Algebra R C := AlgebraObject.sectionAlgebra F U.1
    exact RingHom.finite_algebraMap.mpr
      (moduleFinite_sections_of_isFiniteType F U.1 U.2)
  have hflat : c.hom.Flat := by
    let _ : Algebra R C := AlgebraObject.sectionAlgebra F U.1
    exact RingHom.flat_algebraMap_iff.mpr
      (moduleFlat_sections_of_finiteFreeLocus_eq_top F hF U.1 U.2)
  have hfp : c.hom.FinitePresentation := by
    let _ : Algebra R C := AlgebraObject.sectionAlgebra F U.1
    have : IsNoetherianRing R :=
      IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
    have : Module.Finite R C := moduleFinite_sections_of_isFiniteType F U.1 U.2
    have : Module.FinitePresentation R C := Module.finitePresentation_of_finite R C
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hb : b.hom.Etale := by
    have : IsFinite g := (cover f I V 0).prop.1
    have : Etale g := (cover f I V 0).prop.2
    have h := g.etale_appLE (U.2.preimage i) ((U.2.preimage i).preimage g) le_rfl
    exact Eq.mp (congrArg (fun k => k.hom.Etale)
      (g.appLE_eq_app (U := i ⁻¹ᵁ U.1))) h
  let _ : Algebra R C := c.hom.toAlgebra
  obtain ⟨r, hr, he⟩ :=
    SchemeTheory.exists_etale_away_of_isPushout_closedFiber π c q b
      (Scheme.Hom.app_surjective i U.1 U.2)
      (algebraizedSheafMap_affine_isPushout f I V F 0 σ ⟨U.1, U.2⟩)
      p hp hfinite hflat hfp hb
  exact ⟨r, hr, RingHom.etale_algebraMap.mpr he⟩

variable [IsLocalRing A]

/-- Every point on the actual closed fiber has a neighborhood on which
the constructed relative spectrum is étale over the original scheme. -/
theorem algebraizedCover_exists_etale_neighborhood_closedFiber
    (V : MorphismProperty.Over
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
        (level f (IsLocalRing.maximalIdeal A) 0))
    (σ : F ⟶ moduleSheaf f (IsLocalRing.maximalIdeal A) V 0) [IsMonHom σ]
    [IsIso ((Scheme.Modules.pullback
      (Limits.pullback.fst f (baseInclusion (IsLocalRing.maximalIdeal A) 0))).map σ)]
    (hF : finiteFreeLocus F = ⊤)
    (x : X) (hx : f x = IsLocalRing.closedPoint A) :
    ∃ W : X.Opens, x ∈ W ∧
      Etale (Scheme.RelativeSpec.toBase (AlgebraObject.structureMap F) ∣_ W) := by
  obtain ⟨U, hU, hxU, _hUtop⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := hU.range_fromSpec ▸ hxU
  have hmap : Spec.map (f.constToPresheaf.app (op U)) = hU.fromSpec ≫ f :=
    specMap_algebraMap_eq_fromSpec_comp f hU
  have hp : PrimeSpectrum.comap (f.constToPresheaf.app (op U)).hom p =
      IsLocalRing.closedPoint A := by
    change Spec.map (f.constToPresheaf.app (op U)) p = IsLocalRing.closedPoint A
    rw [hmap, Scheme.Hom.comp_apply]
    exact hx
  have hIp : sectionsIdeal f (IsLocalRing.maximalIdeal A) U ≤ p.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    exact (congrArg PrimeSpectrum.asIdeal hp).ge
  have hker : RingHom.ker
      ((Limits.pullback.fst f
        (baseInclusion (IsLocalRing.maximalIdeal A) 0)).app U).hom ≤ p.asIdeal := by
    have hk := levelProjection_app_ker f (IsLocalRing.maximalIdeal A) 0 ⟨U, hU⟩
    exact hk.le.trans ((pow_one (sectionsIdeal f (IsLocalRing.maximalIdeal A) U)).le.trans hIp)
  obtain ⟨r, hr, he⟩ := algebraizedSection_exists_etale_basicOpen
    f (IsLocalRing.maximalIdeal A) V F σ hF ⟨U, hU⟩ p hker
  refine ⟨X.basicOpen r, ?_, ?_⟩
  · change p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r
    rw [hU.fromSpec_preimage_basicOpen]
    exact hr
  · exact Scheme.RelativeSpec.etale_restrict_basicOpen_of_etale_away
      (AlgebraObject.structureMap F) ⟨U, hU⟩ r he

/-- The actual algebraized relative spectrum is étale everywhere: its
étale target neighborhoods contain the closed fiber, so universal
closedness over the local base forces them to cover the whole scheme. -/
theorem algebraizedCover_etale [UniversallyClosed f]
    (V : MorphismProperty.Over
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
        (level f (IsLocalRing.maximalIdeal A) 0))
    (σ : F ⟶ moduleSheaf f (IsLocalRing.maximalIdeal A) V 0) [IsMonHom σ]
    [IsIso ((Scheme.Modules.pullback
      (Limits.pullback.fst f (baseInclusion (IsLocalRing.maximalIdeal A) 0))).map σ)]
    (hF : finiteFreeLocus F = ⊤) :
    Etale (Scheme.RelativeSpec.toBase (AlgebraObject.structureMap F)) := by
  have : IsZariskiLocalAtTarget (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (@Etale : MorphismProperty Scheme.{u})
  let p := Scheme.RelativeSpec.toBase (AlgebraObject.structureMap F)
  let S := {W : X.Opens // Etale (p ∣_ W)}
  let W : X.Opens := ⨆ i : S, i.1
  have hfiber (x : X) (hx : f x = IsLocalRing.closedPoint A) : x ∈ W := by
    obtain ⟨U, hxU, hU⟩ :=
      algebraizedCover_exists_etale_neighborhood_closedFiber f F V σ hF x hx
    exact (le_iSup (fun i : S => i.1) ⟨U, hU⟩) hxU
  obtain ⟨B, hB, hBW⟩ := f.exists_preimage_le_of_fiber_subset
    (IsLocalRing.closedPoint A) W hfiber
  have hBtop : B = ⊤ := (IsLocalRing.closedPoint_mem_iff B).mp hB
  have hWtop : W = ⊤ := by
    apply top_unique
    intro x _hx
    apply hBW
    change f x ∈ B
    rw [hBtop]
    trivial
  exact IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @Etale) (fun i : S => i.1) hWtop (fun i => i.2)

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
