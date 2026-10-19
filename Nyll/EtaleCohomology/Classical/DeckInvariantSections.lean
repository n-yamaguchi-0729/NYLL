/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.DeckSectionRepresentations
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Algebra.Homology.Additive

/-!
# Actual global sections as deck invariants

This is the degree-zero geometric identification required for descent.
The map is actual restriction to the cover, and surjectivity is actual
sheaf descent, not an assumed comparison.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

namespace EtaleCohomology

/-- Restriction of actual base sections takes values in the actual deck invariants. -/
def finiteEtaleSectionsToDeckInvariants (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (Y : FiniteEtale X) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) →+
      (finiteEtaleDeckSectionsRep X F Y).ρ.invariants where
  toFun s := ⟨F.obj.map (finiteEtaleCoverBaseMap X Y).op s, fun σ =>
    finiteEtaleSheaf_restrict_invariant X
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F)
      Y s (MulOpposite.unop σ)⟩
  map_zero' := Subtype.ext ((F.obj.map (finiteEtaleCoverBaseMap X Y).op).hom.map_zero)
  map_add' s t := Subtype.ext
    ((F.obj.map (finiteEtaleCoverBaseMap X Y).op).hom.map_add s t)

/-- Actual restriction to a Galois cover is bijective onto deck invariants. -/
theorem finiteEtaleSectionsToDeckInvariants_bijective
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] :
    Function.Bijective (finiteEtaleSectionsToDeckInvariants X F Y) := by
  let U := (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F
  have : ConnectedSpace Y.left := FiniteEtale.connectedSpace_left_of_isConnected Y
  have : Surjective Y.hom :=
    IsFiniteEtale.surjective (show Y.left ⟶ X from Y.hom)
  constructor
  · intro s t h
    exact finiteEtaleSheaf_restrict_injective X U Y (congrArg Subtype.val h)
  · intro s
    obtain ⟨t, ht, _⟩ := existsUnique_section_of_galois_invariant X U Y s.val
      (fun σ => s.property (MulOpposite.op σ))
    exact ⟨t, Subtype.ext ht⟩

/-- Actual base sections are additively equivalent to deck-invariant
sections on a finite etale Galois cover. -/
def finiteEtaleSectionsDeckInvariantsAddEquiv
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y] :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) ≃+
      (finiteEtaleDeckSectionsRep X F Y).ρ.invariants :=
  AddEquiv.ofBijective (finiteEtaleSectionsToDeckInvariants X F Y)
    (finiteEtaleSectionsToDeckInvariants_bijective X F Y)

/-- The invariant-section equivalence is the actual geometric restriction map. -/
theorem finiteEtaleSectionsDeckInvariantsAddEquiv_apply
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (Y : FiniteEtale X) [IsGalois Y]
    (s : F.obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
    (finiteEtaleSectionsDeckInvariantsAddEquiv X F Y s).val =
      F.obj.map (finiteEtaleCoverBaseMap X Y).op s := rfl

/-- The actual invariant-section comparison respects coefficient morphisms. -/
theorem finiteEtaleSectionsDeckInvariants_naturality
    (X : Scheme.{u}) [ConnectedSpace X]
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (η : F ⟶ G)
    (Y : FiniteEtale X) [IsGalois Y]
    (s : F.obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
    ((Rep.invariantsFunctor ℤ (Aut Y)ᵐᵒᵖ).map
        (finiteEtaleDeckSectionsRepMap X Y η))
      (finiteEtaleSectionsDeckInvariantsAddEquiv X F Y s) =
    finiteEtaleSectionsDeckInvariantsAddEquiv X G Y
      (η.hom.app (op (Scheme.Etale.mk (𝟙 X))) s) := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (η.hom.naturality (finiteEtaleCoverBaseMap X Y).op) s

/-- Actual deck sections form an additive coefficient functor. -/
def finiteEtaleDeckSectionsFunctor (X : Scheme.{u}) (Y : FiniteEtale X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤ Rep.{u} ℤ (Aut Y)ᵐᵒᵖ where
  obj F := finiteEtaleDeckSectionsRep X F Y
  map η := finiteEtaleDeckSectionsRepMap X Y η
  map_id F := by
    ext s
    rfl
  map_comp η θ := by
    ext s
    rfl

/-- Additivity follows from actual evaluation of coefficient morphisms. -/
instance finiteEtaleDeckSectionsFunctor_additive
    (X : Scheme.{u}) (Y : FiniteEtale X) :
    (finiteEtaleDeckSectionsFunctor X Y).Additive where
  map_add := by
    intro F G η θ
    ext s
    rfl

/-- The actual base-section functor is naturally the invariant-deck-section
functor. Every component is geometric restriction and descent. -/
def finiteEtaleBaseSectionsDeckInvariantsNatIso
    (X : Scheme.{u}) [ConnectedSpace X]
    (Y : FiniteEtale X) [IsGalois Y] :
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj
        (op (Scheme.Etale.mk (𝟙 X)))) ≅
      (finiteEtaleDeckSectionsFunctor X Y ⋙
        Rep.invariantsFunctor ℤ (Aut Y)ᵐᵒᵖ ⋙
          forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}) :=
  NatIso.ofComponents
    (fun F => (finiteEtaleSectionsDeckInvariantsAddEquiv X F Y).toAddCommGrpIso)
    (fun {F G} η => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      exact (finiteEtaleSectionsDeckInvariants_naturality X η Y s).symm)

/-- Actual complexes of base sections agree with actual complexes of deck
invariants, including all differentials. This applies to an injective resolution
without imposing a comparison hypothesis on it. -/
def finiteEtaleBaseSectionsDeckInvariantsComplexIso
    (X : Scheme.{u}) [ConnectedSpace X]
    (Y : FiniteEtale X) [IsGalois Y]
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℕ) :
    ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj
        (op (Scheme.Etale.mk (𝟙 X)))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K ≅
    ((finiteEtaleDeckSectionsFunctor X Y ⋙
      Rep.invariantsFunctor ℤ (Aut Y)ᵐᵒᵖ ⋙
        forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K :=
  (NatIso.mapHomologicalComplex
    (finiteEtaleBaseSectionsDeckInvariantsNatIso X Y)
    (ComplexShape.up ℕ)).app K

end EtaleCohomology
