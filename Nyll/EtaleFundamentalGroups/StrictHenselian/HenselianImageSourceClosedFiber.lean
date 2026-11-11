/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianImageSourceResidue
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkNoetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Keeping proper models over the original henselization

The actual image quotient gives a closed immersion of spectra. Composing
a proper image-stage model with this immersion keeps its total scheme
unchanged and makes it proper over the original henselization. The native
closed fibers are canonically isomorphic, with both projections retained.

Thus applying an approximation theorem over the original henselization
does not require any permanence theorem for its image quotient.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits
open EtaleFundamentalGroups.StrictHenselian

namespace AlgebraicGeometry.HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [HenselianLocalRing A]

/-- The actual quotient embeds its spectrum as a closed subscheme of the
original henselization spectrum. -/
instance imageProjection_spec_isClosedImmersion (i : FGSubalgebra R A) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (imageProjection R A i))) :=
  IsClosedImmersion.spec_of_surjective _
    (imageProjection_surjective R A i)

/-- The same total scheme, now considered over the original henselization. -/
abbrev sourceBaseMap (i : FGSubalgebra R A) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of (image R A i))) :
    X ⟶ Spec (henselianStage R A i) :=
  f ≫ Spec.map (CommRingCat.ofHom (imageProjection R A i))

instance sourceBaseMap_isProper (i : FGSubalgebra R A) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of (image R A i))) [IsProper f] :
    IsProper (sourceBaseMap R A i f) := by
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (imageProjection R A i))) :=
    imageProjection_spec_isClosedImmersion R A i
  change IsProper (f ≫ Spec.map (CommRingCat.ofHom (imageProjection R A i)))
  infer_instance

/-- No finite-presentation hypothesis on the image-stage model is needed:
properness and the Noetherian original henselization supply it. -/
theorem sourceBaseMap_locallyOfFinitePresentation [IsNoetherianRing R]
    (i : FGSubalgebra R A) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of (image R A i))) [IsProper f] :
    LocallyOfFinitePresentation (sourceBaseMap R A i f) := by
  have : Algebra.FiniteType R i.1 := (Subalgebra.fg_iff_finiteType i.1).mp i.2
  have : IsNoetherianRing i.1 := Algebra.FiniteType.isNoetherianRing R i.1
  have : IsNoetherianRing (localStage R A i) := inferInstance
  have : IsNoetherianRing (henselianStage R A i) :=
    geometricStalk_isNoetherianRing (IsLocalRing.residue (localStage R A i))
  infer_instance

/-- The actual residue-field isomorphism on spectra. -/
def sourceImageResidueSpecIso (i : FGSubalgebra R A) :
    Spec (CommRingCat.of (IsLocalRing.ResidueField (image R A i))) ≅
      Spec (CommRingCat.of (IsLocalRing.ResidueField (henselianStage R A i))) :=
  Scheme.Spec.mapIso (sourceImageResidueEquiv R A i).toCommRingCatIso.op

@[reassoc]
theorem sourceImageResidueSpecIso_hom_base (i : FGSubalgebra R A) :
    (sourceImageResidueSpecIso R A i).hom ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue (henselianStage R A i))) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i))) ≫
        Spec.map (CommRingCat.ofHom (imageProjection R A i)) := by
  change Spec.map (sourceImageResidueEquiv R A i).toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue (henselianStage R A i))) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- The actual native closed-point square is cartesian. -/
theorem sourceImageResidue_isPullback (i : FGSubalgebra R A) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i))))
      (sourceImageResidueSpecIso R A i).hom
      (Spec.map (CommRingCat.ofHom (imageProjection R A i)))
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (henselianStage R A i)))) :=
  IsPullback.of_vert_isIso_mono
    ⟨(sourceImageResidueSpecIso_hom_base R A i).symm⟩

/-- Changing from the image quotient to its original henselization
preserves the native closed fiber and the total-space projection. -/
def sourceImageClosedFiberIso (i : FGSubalgebra R A) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of (image R A i))) :
    pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i)))) ≅
      pullback (sourceBaseMap R A i f)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (henselianStage R A i)))) :=
  ((IsPullback.of_hasPullback f
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i))))).paste_vert
      (sourceImageResidue_isPullback R A i)).isoPullback

@[reassoc]
theorem sourceImageClosedFiberIso_hom_fst (i : FGSubalgebra R A) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of (image R A i))) :
    (sourceImageClosedFiberIso R A i f).hom ≫
        pullback.fst (sourceBaseMap R A i f)
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (henselianStage R A i)))) =
      pullback.fst f
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i)))) :=
  IsPullback.isoPullback_hom_fst _

@[reassoc]
theorem sourceImageClosedFiberIso_hom_snd (i : FGSubalgebra R A) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of (image R A i))) :
    (sourceImageClosedFiberIso R A i f).hom ≫
        pullback.snd (sourceBaseMap R A i f)
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (henselianStage R A i)))) =
      pullback.snd f
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i)))) ≫
          (sourceImageResidueSpecIso R A i).hom :=
  IsPullback.isoPullback_hom_snd _

end AlgebraicGeometry.HenselianNoetherianImageStages
