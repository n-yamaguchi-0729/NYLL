/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenSubgroupFundamentalGroup
public import Nyll.EtaleFundamentalGroups.GaloisCategories.PointStabilizerMorphism
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# The actual pointed-cover diagram of open subgroups

Each open subgroup of a fiber-functor automorphism group is realized by a
connected object and a point with that exact stabilizer. Inclusions are
realized by the unique morphisms carrying those points to each other.
The identity and composition laws follow from connected pointed uniqueness.

For the actual finite étale fiber functor, this is a diagram of actual
connected finite étale covers. Restricting it to the open subgroups containing
a section supplies the covering diagram used in geometric-section detection.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

universe u v w

variable {C : Type u} [Category.{v} C] [GaloisCategory C]
  (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- The connected object realizing the specified open subgroup. -/
def openSubgroupCover (H : OpenSubgroup (Aut F)) : C :=
  (exists_connected_object_point_stabilizer_eq_any_universe F H).choose

instance openSubgroupCover_isConnected (H : OpenSubgroup (Aut F)) :
    IsConnected (openSubgroupCover F H) :=
  (exists_connected_object_point_stabilizer_eq_any_universe F H).choose_spec.choose

/-- The chosen geometric fiber point in the actual cover. -/
def openSubgroupCoverPoint (H : OpenSubgroup (Aut F)) : F.obj (openSubgroupCover F H) :=
  (exists_connected_object_point_stabilizer_eq_any_universe F H).choose_spec.choose_spec.choose

/-- The chosen point has the original open subgroup as its exact stabilizer. -/
theorem openSubgroupCoverPoint_stabilizer (H : OpenSubgroup (Aut F)) :
    MulAction.stabilizer (Aut F) (openSubgroupCoverPoint F H) = H.toSubgroup :=
  (exists_connected_object_point_stabilizer_eq_any_universe F H).choose_spec.choose_spec.choose_spec

/-- Subgroup inclusion is realized by a morphism carrying the chosen fiber points. -/
theorem exists_openSubgroupCoverMap
    {H K : OpenSubgroup (Aut F)} (h : H ≤ K) :
    ∃ f : openSubgroupCover F H ⟶ openSubgroupCover F K,
      F.map f (openSubgroupCoverPoint F H) = openSubgroupCoverPoint F K := by
  apply exists_hom_of_pointStabilizer_le F
    (openSubgroupCover F H) (openSubgroupCover F K)
    (openSubgroupCoverPoint F H) (openSubgroupCoverPoint F K)
  rw [openSubgroupCoverPoint_stabilizer, openSubgroupCoverPoint_stabilizer]
  exact h

/-- The actual pointed cover morphism realizing subgroup inclusion. -/
def openSubgroupCoverMap {H K : OpenSubgroup (Aut F)} (h : H ≤ K) :
    openSubgroupCover F H ⟶ openSubgroupCover F K :=
  (exists_openSubgroupCoverMap F h).choose

/-- Transition maps carry the specified fiber point to the specified fiber point. -/
theorem openSubgroupCoverMap_point {H K : OpenSubgroup (Aut F)} (h : H ≤ K) :
    F.map (openSubgroupCoverMap F h) (openSubgroupCoverPoint F H) =
      openSubgroupCoverPoint F K :=
  (exists_openSubgroupCoverMap F h).choose_spec

/-- Pointed connected uniqueness forces the transition at an identity to be the identity. -/
theorem openSubgroupCoverMap_refl (H : OpenSubgroup (Aut F)) :
    openSubgroupCoverMap F (le_refl H) = 𝟙 (openSubgroupCover F H) := by
  apply evaluation_injective_of_isConnected F _ _ (openSubgroupCoverPoint F H)
  change F.map (openSubgroupCoverMap F (le_refl H)) (openSubgroupCoverPoint F H) =
    F.map (𝟙 (openSubgroupCover F H)) (openSubgroupCoverPoint F H)
  rw [openSubgroupCoverMap_point, F.map_id]
  rfl

/-- Pointed connected uniqueness forces actual cover maps to compose. -/
theorem openSubgroupCoverMap_comp {H K L : OpenSubgroup (Aut F)}
    (h : H ≤ K) (k : K ≤ L) :
    openSubgroupCoverMap F h ≫ openSubgroupCoverMap F k =
      openSubgroupCoverMap F (h.trans k) := by
  apply evaluation_injective_of_isConnected F _ _ (openSubgroupCoverPoint F H)
  change F.map (openSubgroupCoverMap F h ≫ openSubgroupCoverMap F k)
      (openSubgroupCoverPoint F H) =
    F.map (openSubgroupCoverMap F (h.trans k)) (openSubgroupCoverPoint F H)
  rw [F.map_comp, FintypeCat.comp_apply, openSubgroupCoverMap_point,
    openSubgroupCoverMap_point, openSubgroupCoverMap_point]

/-- The covering diagram is constructed from actual connected objects and their
unique pointed transition maps, in arbitrary fiber and category universes. -/
def openSubgroupCoverDiagram : OpenSubgroup (Aut F) ⥤ C where
  obj := openSubgroupCover F
  map f := openSubgroupCoverMap F (leOfHom f)
  map_id H := openSubgroupCoverMap_refl F H
  map_comp f g := (openSubgroupCoverMap_comp F (leOfHom f) (leOfHom g)).symm

end CategoryTheory.PreGaloisCategory
