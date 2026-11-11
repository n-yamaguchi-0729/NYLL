/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Functoriality.DirectImageAlgebra
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Recovering the original affine cover inside its extended relative spectrum

For an affine morphism over an open subscheme, the relative spectrum of
its composite direct-image algebra restricts to the original source.
The two schemes are colimits of the same actual affine section spectra.
The comparison uses the original chart maps and is over the given open.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A cocone of affine preimage charts is a colimit when its chart maps are open immersions. -/
def isColimitOfAffinePreimageCharts {B : Scheme.{u}}
    {D : B.AffineZariskiSite ⥤ Scheme.{u}} (c : Cocone D) (p : c.pt ⟶ B)
    [hopen : ∀ W, IsOpenImmersion (c.ι.app W)]
    (hrange : ∀ W, (c.ι.app W).opensRange = p ⁻¹ᵁ W.1) : IsColimit c := by
  let C : c.pt.OpenCover := (AffineZariskiSite.directedCover B).pullback₁ p
  have (W : B.AffineZariskiSite) : IsOpenImmersion (C.f W) := C.map_prop W
  let e (W : B.AffineZariskiSite) : C.X W ≅ D.obj W :=
    IsOpenImmersion.isoOfRangeEq (C.f W) (c.ι.app W) (by
      change Set.range (pullback.fst p W.1.ι) = Set.range (c.ι.app W)
      rw [Pullback.range_fst, Opens.range_ι]
      exact congrArg (fun V : c.pt.Opens => (V : Set c.pt)) (hrange W).symm)
  have he (W : B.AffineZariskiSite) : (e W).hom ≫ c.ι.app W = C.f W :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let E : C.functorOfLocallyDirected ≅ D := NatIso.ofComponents e (by
    intro W Z i
    have : IsOpenImmersion (c.ι.app Z) := hopen Z
    apply (cancel_mono (c.ι.app Z)).mp
    calc
      (C.trans i ≫ (e Z).hom) ≫ c.ι.app Z = C.trans i ≫ C.f Z :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k : C.X Z ⟶ c.pt => C.trans i ≫ k) (he Z))
      _ = C.f W := C.trans_map i
      _ = (e W).hom ≫ c.ι.app W := (he W).symm
      _ = ((e W).hom ≫ D.map i) ≫ c.ι.app Z := by
        rw [Category.assoc, c.w i])
  refine (IsColimit.precomposeHomEquiv E c) ?_
  refine IsColimit.ofIsoColimit C.isColimitCoconeOfLocallyDirected ?_
  refine Cocone.ext (Iso.refl c.pt) ?_
  intro W
  exact (Category.comp_id (C.f W)).trans (he W).symm

namespace DirectImageAlgebra

/-- An open immersion sends affine opens to affine opens and their basic-open inclusions. -/
def imageAffineFunctor {B X : Scheme.{u}} (j : B ⟶ X) [IsOpenImmersion j] :
    B.AffineZariskiSite ⥤ X.AffineZariskiSite where
  obj W := ⟨j ''ᵁ W.1, W.2.image_of_isOpenImmersion j⟩
  map {W Z} i := homOfLE (by
    obtain ⟨r, hr⟩ := i.le
    exact ⟨(j.appIso Z.1).inv r,
      (image_basicOpen j r).symm.trans (congrArg (j ''ᵁ ·) hr)⟩)

variable {X V : Scheme.{u}} (U : X.Opens) (π : V ⟶ U.toScheme)

/-- The recovery chart has the original affine inverse image. -/
theorem recovery_preimage (W : U.toScheme.AffineZariskiSite) :
    (π ≫ U.ι) ⁻¹ᵁ (U.ι ''ᵁ W.1) = π ⁻¹ᵁ W.1 :=
  congrArg (π ⁻¹ᵁ ·) (U.ι.preimage_image_eq W.1)

variable [IsAffineHom π]

/-- The inverse image of an affine chart in the given open is affine in the original source. -/
theorem recovery_isAffineOpen (W : U.toScheme.AffineZariskiSite) :
    IsAffineOpen ((π ≫ U.ι) ⁻¹ᵁ (U.ι ''ᵁ W.1)) :=
  Eq.mp (congrArg IsAffineOpen (recovery_preimage U π W).symm) (W.2.preimage π)

variable [(RelativeSpec.underlyingModule (structureMap (π ≫ U.ι))).IsQuasicoherent]

/-- The relative-spectrum chart diagram indexed by affine opens of the given open subscheme. -/
abbrev recoveryDiagram : U.toScheme.AffineZariskiSite ⥤ Scheme.{u} :=
  imageAffineFunctor U.ι ⋙ (RelativeSpec.gluingData (structureMap (π ≫ U.ι))).functor

/-- The original source and its affine chart maps form a cocone over the recovery diagram. -/
def originalRecoveryCocone : Cocone (recoveryDiagram U π) where
  pt := V
  ι :=
    { app W := (recovery_isAffineOpen U π W).fromSpec
      naturality {W Z} i := by
        change Spec.map (V.presheaf.map
            ((Opens.map (π ≫ U.ι).base).map
              ((AffineZariskiSite.toOpensFunctor X).map
                ((imageAffineFunctor U.ι).map i))).op) ≫
            (recovery_isAffineOpen U π Z).fromSpec =
          (recovery_isAffineOpen U π W).fromSpec ≫ 𝟙 V
        exact ((recovery_isAffineOpen U π Z).map_fromSpec
          (recovery_isAffineOpen U π W) _).trans (Category.comp_id _).symm }

/-- The original source is the colimit of the recovery chart diagram. -/
def originalRecoveryIsColimit : IsColimit (originalRecoveryCocone U π) := by
  have (W : U.toScheme.AffineZariskiSite) :
      IsOpenImmersion ((originalRecoveryCocone U π).ι.app W) :=
    (recovery_isAffineOpen U π W).isOpenImmersion_fromSpec
  apply isColimitOfAffinePreimageCharts (originalRecoveryCocone U π) π
  intro W
  exact (recovery_isAffineOpen U π W).opensRange_fromSpec.trans
    (recovery_preimage U π W)

/-- The structural morphism of the relative spectrum of the composite direct-image algebra. -/
abbrev recoveryBase : RelativeSpec.scheme (structureMap (π ≫ U.ι)) ⟶ X :=
  RelativeSpec.toBase (structureMap (π ≫ U.ι))

/-- The canonical map from a recovery chart into the ambient relative spectrum. -/
abbrev ambientRecoveryChart (W : U.toScheme.AffineZariskiSite) :
    (recoveryDiagram U π).obj W ⟶ RelativeSpec.scheme (structureMap (π ≫ U.ι)) :=
  (RelativeSpec.openCover (structureMap (π ≫ U.ι))).f ((imageAffineFunctor U.ι).obj W)

/-- Each ambient recovery chart is an open immersion. -/
instance ambientRecoveryChart_isOpenImmersion (W : U.toScheme.AffineZariskiSite) :
    IsOpenImmersion (ambientRecoveryChart U π W) :=
  (RelativeSpec.openCover (structureMap (π ≫ U.ι))).map_prop _

omit [IsAffineHom π] in
private theorem ambientRecoveryChart_range (W : U.toScheme.AffineZariskiSite) :
    (ambientRecoveryChart U π W).opensRange =
      recoveryBase U π ⁻¹ᵁ (U.ι ''ᵁ W.1) :=
  (RelativeSpec.toBase_preimage (structureMap (π ≫ U.ι))
    ((imageAffineFunctor U.ι).obj W)).symm

omit [IsAffineHom π] in
/-- Every recovery chart lies over the given open subscheme. -/
theorem ambientRecoveryChart_range_subset (W : U.toScheme.AffineZariskiSite) :
    Set.range (ambientRecoveryChart U π W) ⊆ Set.range (recoveryBase U π ⁻¹ᵁ U).ι := by
  rw [Opens.range_ι]
  have hU : U.ι ''ᵁ W.1 ≤ U :=
    (U.ι.image_le_opensRange W.1).trans_eq U.opensRange_ι
  exact (ambientRecoveryChart_range U π W).le.trans ((recoveryBase U π).preimage_mono hU)

/-- The ambient recovery chart factored through the inverse image of the given open. -/
def restrictedRecoveryChart (W : U.toScheme.AffineZariskiSite) :
    (recoveryDiagram U π).obj W ⟶ (recoveryBase U π ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (recoveryBase U π ⁻¹ᵁ U).ι (ambientRecoveryChart U π W)
    (ambientRecoveryChart_range_subset U π W)

omit [IsAffineHom π] in
/-- The recovery-chart factorization is an open immersion. -/
theorem restrictedRecoveryChart_isOpenImmersion
    (W : U.toScheme.AffineZariskiSite) : IsOpenImmersion (restrictedRecoveryChart U π W) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift
    (recoveryBase U π ⁻¹ᵁ U).ι (ambientRecoveryChart U π W)
    (ambientRecoveryChart_range_subset U π W)))

attribute [local instance] restrictedRecoveryChart_isOpenImmersion

omit [IsAffineHom π] in
private theorem restrictedRecoveryChart_fac (W : U.toScheme.AffineZariskiSite) :
    restrictedRecoveryChart U π W ≫ (recoveryBase U π ⁻¹ᵁ U).ι =
      ambientRecoveryChart U π W :=
  IsOpenImmersion.lift_fac _ _ _

omit [IsAffineHom π] in
/-- The restricted recovery chart covers the corresponding inverse-image open. -/
theorem restrictedRecoveryChart_range (W : U.toScheme.AffineZariskiSite) :
    (restrictedRecoveryChart U π W).opensRange =
      (recoveryBase U π ∣_ U) ⁻¹ᵁ W.1 := by
  apply (recoveryBase U π ⁻¹ᵁ U).ι.image_injective
  calc
    (recoveryBase U π ⁻¹ᵁ U).ι ''ᵁ (restrictedRecoveryChart U π W).opensRange =
        (restrictedRecoveryChart U π W ≫ (recoveryBase U π ⁻¹ᵁ U).ι).opensRange :=
      (Hom.opensRange_comp _ _).symm
    _ = (ambientRecoveryChart U π W).opensRange := by
      exact Opens.ext (congrArg
        (fun k : (recoveryDiagram U π).obj W ⟶
          RelativeSpec.scheme (structureMap (π ≫ U.ι)) => Set.range k)
        (restrictedRecoveryChart_fac U π W))
    _ = recoveryBase U π ⁻¹ᵁ (U.ι ''ᵁ W.1) := ambientRecoveryChart_range U π W
    _ = (recoveryBase U π ⁻¹ᵁ U).ι ''ᵁ ((recoveryBase U π ∣_ U) ⁻¹ᵁ W.1) :=
      (image_morphismRestrict_preimage (recoveryBase U π) U W.1).symm

/-- The restricted relative spectrum and its chart maps form a recovery cocone. -/
def restrictedRecoveryCocone : Cocone (recoveryDiagram U π) where
  pt := (recoveryBase U π ⁻¹ᵁ U).toScheme
  ι :=
    { app := restrictedRecoveryChart U π
      naturality {W Z} i := by
        apply (cancel_mono (recoveryBase U π ⁻¹ᵁ U).ι).mp
        change ((recoveryDiagram U π).map i ≫ restrictedRecoveryChart U π Z) ≫
            (recoveryBase U π ⁻¹ᵁ U).ι =
          (restrictedRecoveryChart U π W ≫ 𝟙 (recoveryBase U π ⁻¹ᵁ U).toScheme) ≫
            (recoveryBase U π ⁻¹ᵁ U).ι
        rw [Category.assoc, restrictedRecoveryChart_fac, Category.comp_id,
          restrictedRecoveryChart_fac]
        exact RelativeSpec.restriction_openCover (structureMap (π ≫ U.ι))
          ((imageAffineFunctor U.ι).map i) }

/-- The restricted relative spectrum is the colimit of its recovery chart diagram. -/
def restrictedRecoveryIsColimit : IsColimit (restrictedRecoveryCocone U π) := by
  have (W : U.toScheme.AffineZariskiSite) :
      IsOpenImmersion ((restrictedRecoveryCocone U π).ι.app W) :=
    restrictedRecoveryChart_isOpenImmersion U π W
  apply isColimitOfAffinePreimageCharts (restrictedRecoveryCocone U π)
    (recoveryBase U π ∣_ U)
  exact restrictedRecoveryChart_range U π

/-- The original affine source is the restriction of the actual relative
spectrum of its composite direct-image algebra to the given open. -/
def relativeSpecRestrictIso :
    (RelativeSpec.toBase (structureMap (π ≫ U.ι)) ⁻¹ᵁ U).toScheme ≅ V :=
  (restrictedRecoveryIsColimit U π).coconePointUniqueUpToIso
    (originalRecoveryIsColimit U π)

private theorem relativeSpecRestrictIso_chart (W : U.toScheme.AffineZariskiSite) :
    restrictedRecoveryChart U π W ≫ (relativeSpecRestrictIso U π).hom =
      (recovery_isAffineOpen U π W).fromSpec :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (restrictedRecoveryIsColimit U π) (originalRecoveryIsColimit U π) W

/-- The recovery isomorphism respects the original morphism over the open. -/
@[reassoc]
theorem relativeSpecRestrictIso_hom_toBase :
    (relativeSpecRestrictIso U π).hom ≫ π =
      RelativeSpec.toBase (structureMap (π ≫ U.ι)) ∣_ U := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, morphismRestrict_ι]
  apply (restrictedRecoveryIsColimit U π).hom_ext
  intro W
  change restrictedRecoveryChart U π W ≫
      ((relativeSpecRestrictIso U π).hom ≫ (π ≫ U.ι)) =
    restrictedRecoveryChart U π W ≫
      ((recoveryBase U π ⁻¹ᵁ U).ι ≫ recoveryBase U π)
  rw [← Category.assoc, relativeSpecRestrictIso_chart, ← Category.assoc,
    restrictedRecoveryChart_fac]
  let A : X.AffineZariskiSite := (imageAffineFunctor U.ι).obj W
  have h := RelativeSpec.openCover_toBase (structureMap (π ≫ U.ι)) A
  refine Eq.trans ?_ h.symm
  change (recovery_isAffineOpen U π W).fromSpec ≫ (π ≫ U.ι) =
    Spec.map ((π ≫ U.ι).app A.1) ≫ A.2.fromSpec
  exact ((congrArg (fun a : Γ(X, A.1) ⟶ Γ(V, (π ≫ U.ι) ⁻¹ᵁ A.1) =>
      Spec.map a ≫ A.2.fromSpec) ((π ≫ U.ι).app_eq_appLE (U := A.1))).trans
    (IsAffineOpen.SpecMap_appLE_fromSpec (π ≫ U.ι) A.2
      (recovery_isAffineOpen U π W) le_rfl)).symm

/-- The inverse recovery map has the same original structural triangle. -/
@[reassoc]
theorem relativeSpecRestrictIso_inv_toBase :
    (relativeSpecRestrictIso U π).inv ≫
        (RelativeSpec.toBase (structureMap (π ≫ U.ι)) ∣_ U) = π := by
  rw [← relativeSpecRestrictIso_hom_toBase, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end DirectImageAlgebra

end AlgebraicGeometry.Scheme
