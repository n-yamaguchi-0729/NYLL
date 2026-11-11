/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.InjectiveDeckCohomology
public import Nyll.EtaleCohomology.Classical.FieldSectionRepresentations
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FieldCoverQuotient

/-!
# Higher Galois cohomology of actual injective field sections

The actual field/deck group equivalence identifies cohomology with its
geometric deck counterpart. Positive-degree vanishing therefore follows
from the proved geometric Cech comparison, without a new acyclicity hypothesis.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale

namespace EtaleCohomology

section Integral

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Actual field sections and actual opposite-deck sections have the same
integral cohomology in every universe, through their original pullback actions. -/
def fieldGaloisDeckIntegralCohomologyIso
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    IntegralGroupCohomology.cohomology (fieldGaloisSheafSectionsRep K L F) n ≅
      IntegralGroupCohomology.cohomology
        (finiteEtaleDeckSectionsRep (Spec (.of K)) F (FiniteEtale.mk (ξ K L))) n :=
  IntegralGroupCohomology.integerScalars.mapIso
    (groupCohomology.mapIso
      (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L)
      (LinearEquiv.refl (ULift.{u} ℤ) _) (fun _ => by
        apply LinearMap.ext
        intro s
        rfl) n)

/-- Actual injective field sections have vanishing integral cohomology in
positive degrees, using the geometric finite étale cover over the same fields. -/
theorem isZero_integralCohomology_injective_fieldSections_succ
    (I : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
    (n : ℕ) :
    IsZero (IntegralGroupCohomology.cohomology
      (fieldGaloisSheafSectionsRep K L I) (n + 1)) := by
  have : CategoryTheory.PreGaloisCategory.IsGalois (FiniteEtale.mk (ξ K L)) :=
    EtaleFundamentalGroups.fieldFiniteEtaleCover_isGalois K L
  exact (isZero_integralCohomology_injective_deckSections_succ
    (Spec (.of K)) I (FiniteEtale.mk (ξ K L)) n).of_iso
      (fieldGaloisDeckIntegralCohomologyIso K L I (n + 1))

end Integral

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Actual field-section and deck-section cohomology agree in every degree,
using the geometric field/deck equivalence and the actual pullback actions. -/
def fieldGaloisDeckCohomologyIso
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{0}) (n : ℕ) :
    groupCohomology (fieldGaloisSheafSectionsRep K L F) n ≅
      groupCohomology (finiteEtaleDeckSectionsRep (Spec (.of K)) F
        (FiniteEtale.mk (ξ K L))) n :=
  groupCohomology.mapIso
    (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L)
    (LinearEquiv.refl ℤ _) (fun _ => by
      apply LinearMap.ext
      intro s
      rfl) n

/-- Every positive-degree Galois cohomology group of actual sections of an
injective etale sheaf over a finite Galois field extension vanishes. -/
theorem isZero_groupCohomology_injective_fieldSections_succ
    (I : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{0}) [Injective I]
    (n : ℕ) :
    IsZero (groupCohomology (fieldGaloisSheafSectionsRep K L I) (n + 1)) :=
  (isZero_integralCohomology_injective_fieldSections_succ K L I n).of_iso
    (IntegralGroupCohomology.cohomologyIsoOriginal
      (fieldGaloisSheafSectionsRep K L I) (n + 1)).symm

end EtaleCohomology
