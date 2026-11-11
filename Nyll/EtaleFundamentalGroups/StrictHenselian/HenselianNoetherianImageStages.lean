/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkNoetherian
public import Nyll.EtaleFundamentalGroups.StrictHenselian.OrdinaryHenselizationUniversal
public import Nyll.SchemeTheory.Descent.FGSubalgebra
public import Nyll.SchemeTheory.Descent.LocalStageResidueComparison
public import Nyll.SchemeTheory.Descent.SubalgebraStagesIsLimitCone
public import Nyll.SchemeTheory.RingTheory.Henselian.ModuleFinite
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Actual Noetherian henselian subalgebras of a henselian local algebra

For a finitely generated subalgebra `B` of a henselian local algebra `A`,
localize `B` at the contraction of the closed point of `A`, henselize that
local ring, and take the image of the canonical local map into `A`.

These images are actual subalgebras of `A`, not abstract chosen models.
They are Noetherian and henselian, their inclusions are local, they form
an increasing directed family, and every element of `A` belongs to one.
Taking images avoids any unproved injectivity of a henselization map.

This supplies a genuine henselian Noetherian approximation of the base.
It asserts neither the G-ring property of the stages nor Artin
approximation, and does not assume either of those conclusions.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open EtaleFundamentalGroups.StrictHenselian

namespace AlgebraicGeometry.HenselianNoetherianImageStages

private theorem localizationMap_isLocalHom
    {B A : Type u} [CommRing B] [CommRing A] [IsLocalRing A] (φ : B →+* A) :
    IsLocalHom (LocalStageResidue.localizationMap φ) := by
  apply ((IsLocalRing.local_hom_TFAE (LocalStageResidue.localizationMap φ)).out 5 1).mp
  apply (Localization.AtPrime.eq_maximalIdeal_iff_under_eq
    (I := LocalStageResidue.prime φ)).mp
  change ((IsLocalRing.maximalIdeal A).comap
      (LocalStageResidue.localizationMap φ)).comap
        (algebraMap B (Localization.AtPrime (LocalStageResidue.prime φ))) =
    LocalStageResidue.prime φ
  rw [Ideal.comap_comap, LocalStageResidue.localizationMap_comp]

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [HenselianLocalRing A]

/-- The localization of the actual finite-type stage at the original closed point. -/
abbrev localStage (i : FGSubalgebra R A) : Type u :=
  Localization.AtPrime (LocalStageResidue.prime i.1.val.toRingHom)

/-- The localization map still lands in the original henselian ring. -/
def localStageMap (i : FGSubalgebra R A) : localStage R A i →+* A :=
  LocalStageResidue.localizationMap i.1.val.toRingHom

instance localStageMap_isLocalHom (i : FGSubalgebra R A) :
    IsLocalHom (localStageMap R A i) :=
  localizationMap_isLocalHom i.1.val.toRingHom

theorem localStageMap_algebraMap (i : FGSubalgebra R A) (b : i.1) :
    localStageMap R A i (algebraMap i.1 (localStage R A i) b) = (b : A) :=
  RingHom.congr_fun (LocalStageResidue.localizationMap_comp i.1.val.toRingHom) b

/-- The ordinary henselization of the localized finite-type stage. -/
abbrev henselianStage (i : FGSubalgebra R A) : CommRingCat.{u} :=
  ordinaryHenselization (localStage R A i)

/-- The universal local map from the actual henselization to the original ring. -/
def henselianStageMap (i : FGSubalgebra R A) : henselianStage R A i →+* A :=
  ordinaryHenselizationLift (localStageMap R A i)

instance henselianStageMap_isLocalHom (i : FGSubalgebra R A) :
    IsLocalHom (henselianStageMap R A i) :=
  inferInstanceAs (IsLocalHom (ordinaryHenselizationLift (localStageMap R A i)))

theorem henselianStageMap_comp (i : FGSubalgebra R A) :
    (henselianStageMap R A i).comp (ordinaryHenselizationMap (localStage R A i)) =
      localStageMap R A i :=
  ordinaryHenselizationLift_comp_map (localStageMap R A i)

/-- The canonical local transition between localized original stages. -/
def localTransition {i j : FGSubalgebra R A} (h : i ≤ j) :
    localStage R A i →+* localStage R A j :=
  Localization.localRingHom
    (LocalStageResidue.prime i.1.val.toRingHom)
    (LocalStageResidue.prime j.1.val.toRingHom)
    (Subalgebra.inclusion h).toRingHom (by ext x; rfl)

instance localTransition_isLocalHom {i j : FGSubalgebra R A} (h : i ≤ j) :
    IsLocalHom (localTransition R A h) :=
  inferInstanceAs (IsLocalHom (Localization.localRingHom
    (LocalStageResidue.prime i.1.val.toRingHom)
    (LocalStageResidue.prime j.1.val.toRingHom)
    (Subalgebra.inclusion h).toRingHom (by ext x; rfl)))

theorem localStageMap_comp_transition {i j : FGSubalgebra R A} (h : i ≤ j) :
    (localStageMap R A j).comp (localTransition R A h) = localStageMap R A i := by
  apply IsLocalization.ringHom_ext
    (LocalStageResidue.prime i.1.val.toRingHom).primeCompl
  apply RingHom.ext
  intro b
  change localStageMap R A j
      (Localization.localRingHom
        (LocalStageResidue.prime i.1.val.toRingHom)
        (LocalStageResidue.prime j.1.val.toRingHom)
        (Subalgebra.inclusion h).toRingHom _ (algebraMap i.1 (localStage R A i) b)) =
    localStageMap R A i (algebraMap i.1 (localStage R A i) b)
  rw [Localization.localRingHom_to_map, localStageMap_algebraMap,
    localStageMap_algebraMap]
  rfl

/-- The local transition between actual henselizations, constructed by their
universal property. -/
def henselianTransition {i j : FGSubalgebra R A} (h : i ≤ j) :
    henselianStage R A i →+* henselianStage R A j :=
  ordinaryHenselizationLift
    ((ordinaryHenselizationMap (localStage R A j)).comp (localTransition R A h))

instance henselianTransition_isLocalHom {i j : FGSubalgebra R A} (h : i ≤ j) :
    IsLocalHom (henselianTransition R A h) :=
  inferInstanceAs (IsLocalHom (ordinaryHenselizationLift
    ((ordinaryHenselizationMap (localStage R A j)).comp (localTransition R A h))))

theorem henselianTransition_comp {i j : FGSubalgebra R A} (h : i ≤ j) :
    (henselianTransition R A h).comp (ordinaryHenselizationMap (localStage R A i)) =
      (ordinaryHenselizationMap (localStage R A j)).comp (localTransition R A h) :=
  ordinaryHenselizationLift_comp_map
    ((ordinaryHenselizationMap (localStage R A j)).comp (localTransition R A h))

/-- The henselized transitions retain the actual maps into `A`; uniqueness
of local henselian lifts proves this, without an injectivity assumption. -/
theorem henselianStageMap_comp_transition {i j : FGSubalgebra R A} (h : i ≤ j) :
    (henselianStageMap R A j).comp (henselianTransition R A h) =
      henselianStageMap R A i := by
  apply ordinaryHenselizationLift_unique (localStageMap R A i)
  rw [RingHom.comp_assoc, henselianTransition_comp, ← RingHom.comp_assoc,
    henselianStageMap_comp, localStageMap_comp_transition]

/-- The actual image of the henselized stage, with the original coefficient
subalgebra structure retained. -/
def image (i : FGSubalgebra R A) : Subalgebra R A where
  __ := (henselianStageMap R A i).rangeS
  algebraMap_mem' r := by
    refine ⟨ordinaryHenselizationMap (localStage R A i)
      (algebraMap i.1 (localStage R A i) (algebraMap R i.1 r)), ?_⟩
    exact (RingHom.congr_fun (henselianStageMap_comp R A i) _).trans
      (localStageMap_algebraMap R A i (algebraMap R i.1 r))

/-- The quotient map onto the actual image stage. -/
def imageProjection (i : FGSubalgebra R A) :
    henselianStage R A i →+* image R A i :=
  (henselianStageMap R A i).codRestrict (image R A i) (fun x => ⟨x, rfl⟩)

theorem imageProjection_surjective (i : FGSubalgebra R A) :
    Function.Surjective (imageProjection R A i) := by
  rintro ⟨a, b, hb⟩
  exact ⟨b, Subtype.ext hb⟩

instance image_isLocalRing (i : FGSubalgebra R A) : IsLocalRing (image R A i) :=
  IsLocalRing.of_surjective' (imageProjection R A i) (imageProjection_surjective R A i)

/-- Each image inherits henselianity from its actual henselization quotient. -/
theorem image_henselianLocalRing (i : FGSubalgebra R A) :
    HenselianLocalRing (image R A i) := by
  let _imageAlgebra : Algebra (henselianStage R A i) (image R A i) :=
    (imageProjection R A i).toAlgebra
  have : Module.Finite (henselianStage R A i) (image R A i) :=
    RingHom.Finite.of_surjective (imageProjection R A i) (imageProjection_surjective R A i)
  exact HenselianLocalRing.of_moduleFinite_of_isLocalRing
    (R := henselianStage R A i) (S := image R A i)

/-- The inclusion of each actual image is a local ring map. -/
instance image_val_isLocalHom (i : FGSubalgebra R A) :
    IsLocalHom (image R A i).val.toRingHom where
  map_nonunit x hx := by
    obtain ⟨b, rfl⟩ := imageProjection_surjective R A i x
    exact (isUnit_of_map_unit (henselianStageMap R A i) b hx).map
      (imageProjection R A i)

theorem image_mono {i j : FGSubalgebra R A} (h : i ≤ j) :
    image R A i ≤ image R A j := by
  rintro a ⟨b, rfl⟩
  exact ⟨henselianTransition R A h b,
    RingHom.congr_fun (henselianStageMap_comp_transition R A h) b⟩

/-- The canonical increasing family of henselian image subalgebras. -/
abbrev images : FGSubalgebra R A →o Subalgebra R A where
  toFun := image R A
  monotone' _ _ h := image_mono R A h

/-- Every coefficient in the original finite-type subalgebra belongs to
its actual henselization image. -/
theorem subalgebra_le_image (i : FGSubalgebra R A) : i.1 ≤ image R A i := by
  intro a ha
  let b : i.1 := ⟨a, ha⟩
  refine ⟨ordinaryHenselizationMap (localStage R A i)
    (algebraMap i.1 (localStage R A i) b), ?_⟩
  exact (RingHom.congr_fun (henselianStageMap_comp R A i) _).trans
    (localStageMap_algebraMap R A i b)

/-- Every original coefficient occurs in the image of its singleton-generated
finite-type stage. -/
theorem exhaustive (a : A) : ∃ i : FGSubalgebra R A, a ∈ images R A i := by
  classical
  let i : FGSubalgebra R A :=
    ⟨Algebra.adjoin R (↑({a} : Finset A) : Set A), Subalgebra.fg_adjoin_finset {a}⟩
  exact ⟨i, subalgebra_le_image R A i (Algebra.subset_adjoin (Finset.mem_singleton_self a))⟩

/-- The stages are Noetherian whenever the original coefficient ring is
Noetherian. No Noetherianity of the henselian target is assumed. -/
theorem image_isNoetherianRing [IsNoetherianRing R] (i : FGSubalgebra R A) :
    IsNoetherianRing (image R A i) := by
  have : Algebra.FiniteType R i.1 := (Subalgebra.fg_iff_finiteType i.1).mp i.2
  have : IsNoetherianRing i.1 := Algebra.FiniteType.isNoetherianRing R i.1
  have : IsNoetherianRing (localStage R A i) := inferInstance
  have : IsNoetherianRing (henselianStage R A i) :=
    geometricStalk_isNoetherianRing (IsLocalRing.residue (localStage R A i))
  exact isNoetherianRing_of_surjective (henselianStage R A i) (image R A i)
    (imageProjection R A i) (imageProjection_surjective R A i)

/-- Base change to the original henselian ring is the actual inverse limit
of base changes to its constructed henselian Noetherian image stages. -/
theorem nonempty_isLimit_baseChange {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) :
    Nonempty (IsLimit (SubalgebraStages.cone (images R A) f)) :=
  SubalgebraStages.nonempty_isLimit_cone (images R A) (exhaustive R A) f

end AlgebraicGeometry.HenselianNoetherianImageStages
