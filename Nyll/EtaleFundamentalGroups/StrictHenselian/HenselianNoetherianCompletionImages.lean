/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianCompletionDiagram
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.LocalRingIsAdicCompleteMapMaximalIdealQuotient
public import Nyll.SchemeTheory.RingTheory.LocalRing.FilteredColimit

/-!
# Complete Noetherian image subrings of the completion colimit

The actual image of each completed stage in the constructed colimit is a
quotient of a complete Noetherian local ring. It is therefore itself
complete, Noetherian and local. The images increase and exhaust the
colimit. Above any fixed image they are actual subalgebras over that fixed
complete Noetherian coefficient ring, ready for the existing image-limit
construction of proper schemes.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits
open AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
open IsLocalRing_isAdicComplete_map_maximalIdeal_quotient.M4cP4PS

namespace AlgebraicGeometry.HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [IsNoetherianRing R]
  [CommRing A] [Algebra R A] [HenselianLocalRing A]

/-- Locality of the actual completion colimit follows from its actual stages. -/
instance completionColimit_isLocalRing : IsLocalRing (completionColimit R A) :=
  CommRingCat.isLocalRing_of_isColimit (completionDiagram R A)
    (completionCocone R A) (completionCoconeIsColimit R A)

/-- The original completed-stage maps into the actual colimit reflect units. -/
instance completionCocone_isLocalHom (i : FGSubalgebra R A) :
    IsLocalHom ((completionCocone R A).ι.app i).hom :=
  CommRingCat.isLocalHom_ι_of_isColimit (completionDiagram R A)
    (completionCocone R A) (completionCoconeIsColimit R A)
    (fun {_ _} f => completionTransition_isLocalHom R A f.le) i

/-- The actual range of a completed stage in the constructed ring colimit. -/
def completionImage (i : FGSubalgebra R A) : Subring (completionColimit R A) :=
  ((completionCocone R A).ι.app i).hom.range

/-- The actual surjection from a completed stage to its image. -/
def completionImageProjection (i : FGSubalgebra R A) :
    completionStage R A i →+* completionImage R A i :=
  ((completionCocone R A).ι.app i).hom.codRestrict
    (completionImage R A i) (fun x => ⟨x, rfl⟩)

omit [IsNoetherianRing R] in
theorem completionImageProjection_surjective (i : FGSubalgebra R A) :
    Function.Surjective (completionImageProjection R A i) := by
  rintro ⟨x, y, hy⟩
  exact ⟨y, Subtype.ext hy⟩

/-- The actual inclusion of each completed image into the colimit is local. -/
instance completionImage_val_isLocalHom (i : FGSubalgebra R A) :
    IsLocalHom (completionImage R A i).subtype := by
  constructor
  intro x hx
  obtain ⟨b, rfl⟩ := completionImageProjection_surjective R A i x
  change IsUnit ((completionCocone R A).ι.app i b) at hx
  exact (isUnit_of_map_unit ((completionCocone R A).ι.app i).hom b hx).map
    (completionImageProjection R A i)

instance completionImage_isNoetherianRing (i : FGSubalgebra R A) :
    IsNoetherianRing (completionImage R A i) :=
  isNoetherianRing_of_surjective (completionStage R A i) (completionImage R A i)
    (completionImageProjection R A i) (completionImageProjection_surjective R A i)

instance completionImage_isLocalRing (i : FGSubalgebra R A) :
    IsLocalRing (completionImage R A i) :=
  IsLocalRing.of_surjective' (completionImageProjection R A i)
    (completionImageProjection_surjective R A i)

/-- Completeness descends along the actual surjection from the completed stage. -/
instance completionImage_isAdicComplete (i : FGSubalgebra R A) :
    IsAdicComplete (IsLocalRing.maximalIdeal (completionImage R A i))
      (completionImage R A i) := by
  have hcomplete :=
    isAdicComplete_map_of_surjective
          (IsLocalRing.maximalIdeal (completionStage R A i))
          (completionImageProjection R A i) (completionImageProjection_surjective R A i)
  rw [IsLocalRing.map_maximalIdeal_of_surjective
    (completionImageProjection R A i) (completionImageProjection_surjective R A i)] at hcomplete
  exact hcomplete

omit [IsNoetherianRing R] in
theorem completionImage_mono {i j : FGSubalgebra R A} (h : i ≤ j) :
    completionImage R A i ≤ completionImage R A j := by
  rintro x ⟨y, rfl⟩
  refine ⟨completionTransition R A h y, ?_⟩
  exact ConcreteCategory.congr_hom ((completionCocone R A).w (homOfLE h)) y

omit [IsNoetherianRing R] in
/-- Every element of the actual colimit comes from an actual complete image. -/
theorem completionImage_exhaustive (x : completionColimit R A) :
    ∃ i : FGSubalgebra R A, x ∈ completionImage R A i := by
  obtain ⟨i, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget CommRingCat.{u}) (completionCoconeIsColimit R A)) x
  exact ⟨i, y, hy⟩

/-- Indices above a supplied original stage. -/
abbrev completionImageIndex (i₀ : FGSubalgebra R A) :=
  { i : FGSubalgebra R A // i₀ ≤ i }

instance completionImageIndex_nonempty (i₀ : FGSubalgebra R A) :
    Nonempty (completionImageIndex R A i₀) := ⟨⟨i₀, le_rfl⟩⟩

instance completionImageIndex_isDirected (i₀ : FGSubalgebra R A) :
    IsDirected (completionImageIndex R A i₀) (· ≤ ·) where
  directed i j := by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.1 j.1
    exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩

/-- Above a fixed image, later images are actual subalgebras over it. -/
def completionImageAlgebra (i₀ : FGSubalgebra R A) (i : completionImageIndex R A i₀) :
    Subalgebra (completionImage R A i₀) (completionColimit R A) where
  __ := completionImage R A i.1
  algebraMap_mem' r := completionImage_mono R A i.2 r.2

/-- The increasing actual complete-Noetherian subalgebra family above a fixed stage. -/
def completionImagesAfter (i₀ : FGSubalgebra R A) :
    completionImageIndex R A i₀ →o
      Subalgebra (completionImage R A i₀) (completionColimit R A) where
  toFun := completionImageAlgebra R A i₀
  monotone' _ _ h := completionImage_mono R A h

instance completionImageAlgebra_isNoetherianRing (i₀ : FGSubalgebra R A)
    (i : completionImageIndex R A i₀) :
    IsNoetherianRing (completionImagesAfter R A i₀ i) :=
  inferInstanceAs (IsNoetherianRing (completionImage R A i.1))

instance completionImageAlgebra_isLocalRing (i₀ : FGSubalgebra R A)
    (i : completionImageIndex R A i₀) :
    IsLocalRing (completionImagesAfter R A i₀ i) :=
  inferInstanceAs (IsLocalRing (completionImage R A i.1))

instance completionImageAlgebra_val_isLocalHom (i₀ : FGSubalgebra R A)
    (i : completionImageIndex R A i₀) :
    IsLocalHom (completionImagesAfter R A i₀ i).val.toRingHom :=
  inferInstanceAs (IsLocalHom (completionImage R A i.1).subtype)

instance completionImageAlgebra_isAdicComplete (i₀ : FGSubalgebra R A)
    (i : completionImageIndex R A i₀) :
    IsAdicComplete (IsLocalRing.maximalIdeal (completionImagesAfter R A i₀ i))
      (completionImagesAfter R A i₀ i) :=
  inferInstanceAs (IsAdicComplete (IsLocalRing.maximalIdeal (completionImage R A i.1))
    (completionImage R A i.1))

omit [IsNoetherianRing R] in
/-- Passing above a chosen coefficient stage retains exhaustivity. -/
theorem completionImagesAfter_exhaustive (i₀ : FGSubalgebra R A)
    (x : completionColimit R A) :
    ∃ i : completionImageIndex R A i₀, x ∈ completionImagesAfter R A i₀ i := by
  obtain ⟨i, hi⟩ := completionImage_exhaustive R A x
  obtain ⟨j, h₀j, hij⟩ := exists_ge_ge i₀ i
  exact ⟨⟨j, h₀j⟩, completionImage_mono R A hij hi⟩

end AlgebraicGeometry.HenselianNoetherianImageStages
