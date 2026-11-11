/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.CompactificationDiagram
public import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedRestriction
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Mathlib.Topology.Compactness.Compact

/-!
# A common point of the actual absolute normalization

The specified geometric generic point of each connected cover induces an
actual map from the ambient normalization in the geometric generic field.
These maps are integral and surjective and commute with pointed cover maps.

For a proper ambient scheme, a compatible family of actual rational points
in a directed covering diagram has a common lift to this one normalization.
The proof intersects nonempty closed fibers in the compact normalization.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u v

variable {X U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
  [IsLocallyNoetherian U]
  (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra U.functionField Ω]

attribute [local instance] connectedLeftIntegral

/-- The literal field spectrum map selected by the specified generic fiber point. -/
def connectedCoverGenericLift (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    Spec (.of Ω) ⟶ Spec (.of W.left.functionField) :=
  Spec.map (CommRingCat.ofHom
    (EtaleFundamentalGroups.finiteEtaleGenericHomFunctionFieldMap W
      (fiberObjEquivHom (U.genericExtensionMorphism Ω) W w)))

private theorem connectedCoverGenericLift_comp (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    connectedCoverGenericLift Ω W w ≫ connectedCoverGenericMorphism W =
      (fiberObjEquivHom (U.genericExtensionMorphism Ω) W w).left := by
  have h := EtaleFundamentalGroups.finiteEtaleGenericHomFunctionFieldAlgHom_spec W
    (fiberObjEquivHom (U.genericExtensionMorphism Ω) W w)
  unfold connectedCoverGenericMorphism Scheme.genericExtensionMorphism
  rw [show CommRingCat.ofHom
      (algebraMap W.left.functionField W.left.functionField) = 𝟙 _ from rfl,
    Spec.map_id, Category.id_comp]
  exact h

private theorem connectedCoverGenericLift_naturality
    {W V : FiniteEtale U} [IsConnected W] [IsConnected V] (f : W ⟶ V)
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    (v : (fiber (U.genericExtensionMorphism Ω)).obj V)
    (hw : (fiber (U.genericExtensionMorphism Ω)).map f w = v) :
    connectedCoverGenericLift Ω W w ≫ connectedCoverGenericMap f =
      connectedCoverGenericLift Ω V v := by
  have : Mono (connectedCoverGenericMorphism V) := by
    unfold connectedCoverGenericMorphism Scheme.genericExtensionMorphism
    rw [show CommRingCat.ofHom
        (algebraMap V.left.functionField V.left.functionField) = 𝟙 _ from rfl,
      Spec.map_id, Category.id_comp]
    infer_instance
  apply (cancel_mono (connectedCoverGenericMorphism V)).mp
  rw [Category.assoc, connectedCoverGenericMap_comp_genericMorphism,
    ← Category.assoc, connectedCoverGenericLift_comp, connectedCoverGenericLift_comp]
  have h := congrArg Over.Hom.left
    (fiberObjEquivHom_naturality (U.genericExtensionMorphism Ω) f w)
  change (fiberObjEquivHom (U.genericExtensionMorphism Ω) W w).left ≫ f.left =
    (fiberObjEquivHom (U.genericExtensionMorphism Ω) V
      ((fiber (U.genericExtensionMorphism Ω)).map f w)).left at h
  rw [hw] at h
  exact h

variable (j : U ⟶ X)

theorem connectedCoverGenericLift_over (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    connectedCoverGenericLift Ω W w ≫ (connectedCoverGenericComposite W ≫ j) =
      U.genericExtensionMorphism Ω ≫ j := by
  have hw : (fiberObjEquivHom (U.genericExtensionMorphism Ω) W w).left ≫ W.hom =
      U.genericExtensionMorphism Ω :=
    (fiberObjEquivHom (U.genericExtensionMorphism Ω) W w).w
  unfold connectedCoverGenericComposite
  rw [← Category.assoc, ← Category.assoc, connectedCoverGenericLift_comp, hw]

/-- The actual map from the normalization in the geometric generic field to
the finite-cover compactification selected by the given generic fiber point. -/
def connectedCoverAbsoluteNormalizationMap (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    (U.genericExtensionMorphism Ω ≫ j).normalization ⟶
      (connectedCoverGenericComposite W ≫ j).normalization :=
  Scheme.Hom.normalizationSourceMap
    (U.genericExtensionMorphism Ω ≫ j) (connectedCoverGenericComposite W ≫ j)
    (connectedCoverGenericLift Ω W w) (connectedCoverGenericLift_over Ω j W w)

/-- The absolute-normalization map preserves the original structural map. -/
@[reassoc]
theorem connectedCoverAbsoluteNormalizationMap_fromNormalization
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    connectedCoverAbsoluteNormalizationMap Ω j W w ≫
        (connectedCoverGenericComposite W ≫ j).fromNormalization =
      (U.genericExtensionMorphism Ω ≫ j).fromNormalization :=
  Scheme.Hom.normalizationSourceMap_fromNormalization _ _ _ _

/-- The absolute-normalization map preserves the specified generic field embedding. -/
@[reassoc]
theorem toNormalization_connectedCoverAbsoluteNormalizationMap
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    (U.genericExtensionMorphism Ω ≫ j).toNormalization ≫
        connectedCoverAbsoluteNormalizationMap Ω j W w =
      connectedCoverGenericLift Ω W w ≫
        (connectedCoverGenericComposite W ≫ j).toNormalization :=
  Scheme.Hom.toNormalization_normalizationSourceMap _ _ _ _

/-- Pointed cover transitions commute with the maps from one absolute normalization. -/
theorem connectedCoverAbsoluteNormalizationMap_naturality
    {W V : FiniteEtale U} [IsConnected W] [IsConnected V] (f : W ⟶ V)
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    (v : (fiber (U.genericExtensionMorphism Ω)).obj V)
    (hw : (fiber (U.genericExtensionMorphism Ω)).map f w = v) :
    connectedCoverAbsoluteNormalizationMap Ω j W w ≫
        connectedCoverCompactificationMap j f =
      connectedCoverAbsoluteNormalizationMap Ω j V v := by
  apply Scheme.Hom.normalization.hom_ext (U.genericExtensionMorphism Ω ≫ j)
    _ _ (connectedCoverGenericComposite V ≫ j).fromNormalization
  · rw [← Category.assoc, toNormalization_connectedCoverAbsoluteNormalizationMap,
      Category.assoc, toNormalization_connectedCoverCompactificationMap,
      ← Category.assoc, connectedCoverGenericLift_naturality Ω f w v hw,
      toNormalization_connectedCoverAbsoluteNormalizationMap]
  · rw [Category.assoc, connectedCoverCompactificationMap_fromNormalization,
      connectedCoverAbsoluteNormalizationMap_fromNormalization]
  · exact connectedCoverAbsoluteNormalizationMap_fromNormalization Ω j V v

/-- The actual absolute-normalization transition is integral. -/
theorem connectedCoverAbsoluteNormalizationMap_isIntegralHom
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    IsIntegralHom (connectedCoverAbsoluteNormalizationMap Ω j W w) := by
  unfold connectedCoverAbsoluteNormalizationMap Scheme.Hom.normalizationSourceMap
  infer_instance

/-- Every point in a finite-cover compactification lifts to the absolute normalization. -/
theorem connectedCoverAbsoluteNormalizationMap_surjective
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    Function.Surjective (connectedCoverAbsoluteNormalizationMap Ω j W w) := by
  have : IsIntegralHom (connectedCoverAbsoluteNormalizationMap Ω j W w) :=
    connectedCoverAbsoluteNormalizationMap_isIntegralHom Ω j W w
  have : Surjective (connectedCoverGenericLift Ω W w) := inferInstance
  have : IsDominant ((U.genericExtensionMorphism Ω ≫ j).toNormalization ≫
      connectedCoverAbsoluteNormalizationMap Ω j W w) := by
    rw [toNormalization_connectedCoverAbsoluteNormalizationMap]
    infer_instance
  have : IsDominant (connectedCoverAbsoluteNormalizationMap Ω j W w) :=
    IsDominant.of_comp (U.genericExtensionMorphism Ω ≫ j).toNormalization
      (connectedCoverAbsoluteNormalizationMap Ω j W w)
  have : Surjective (connectedCoverAbsoluteNormalizationMap Ω j W w) :=
    surjective_of_isDominant_of_isClosed_range _
      (connectedCoverAbsoluteNormalizationMap Ω j W w).isClosedMap.isClosed_range
  exact (connectedCoverAbsoluteNormalizationMap Ω j W w).surjective

/-- Compatible actual rational points lift simultaneously to one point of the
normalization in the geometric generic field. Every map in the conclusion
is the one selected by the original pointed cover. -/
theorem exists_absoluteNormalizationPoint_of_compatible_rationalPoints
    (k : Type u) [Field k] (c : X ⟶ Spec (.of k)) [IsProper c]
    {I : Type v} [Preorder I] [Nonempty I]
    (D : I ⥤ FiniteEtale U) [∀ i, IsConnected (D.obj i)]
    (w : ∀ i, (fiber (U.genericExtensionMorphism Ω)).obj (D.obj i))
    (hw : ∀ i l (h : i ≤ l),
      (fiber (U.genericExtensionMorphism Ω)).map (D.map (homOfLE h)) (w i) = w l)
    (y : ∀ i, Spec (.of k) ⟶ (connectedCoverGenericComposite (D.obj i) ≫ j).normalization)
    (hy : ∀ i, y i ≫ (connectedCoverGenericComposite (D.obj i) ≫ j).fromNormalization ≫
      c = 𝟙 (Spec (.of k)))
    (hcompat : ∀ i l (h : i ≤ l),
      y i ≫ connectedCoverCompactificationMap j (D.map (homOfLE h)) = y l)
    (hdir : ∀ i l : I, ∃ m, m ≤ i ∧ m ≤ l) :
    ∃ z : (U.genericExtensionMorphism Ω ≫ j).normalization, ∀ i,
      connectedCoverAbsoluteNormalizationMap Ω j (D.obj i) (w i) z =
        y i (IsLocalRing.closedPoint k) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace c
  have : CompactSpace (U.genericExtensionMorphism Ω ≫ j).normalization :=
    QuasiCompact.compactSpace_of_compactSpace
      (U.genericExtensionMorphism Ω ≫ j).fromNormalization
  let S (i : I) : Set (U.genericExtensionMorphism Ω ≫ j).normalization :=
    {z | connectedCoverAbsoluteNormalizationMap Ω j (D.obj i) (w i) z =
      y i (IsLocalRing.closedPoint k)}
  have hclosed (i : I) : IsClosed (S i) := by
    have : IsClosedImmersion (y i) := isClosedImmersion_of_comp_eq_id
      ((connectedCoverGenericComposite (D.obj i) ≫ j).fromNormalization ≫ c) (y i) (hy i)
    have hr : Set.range (y i) = {y i (IsLocalRing.closedPoint k)} :=
      Set.range_eq_singleton_iff.mpr fun a => congrArg (y i) (Subsingleton.elim _ _)
    have hp : IsClosed ({y i (IsLocalRing.closedPoint k)} :
        Set (connectedCoverGenericComposite (D.obj i) ≫ j).normalization) := by
      rw [← hr]
      exact (y i).isClosedEmbedding.isClosed_range
    exact hp.preimage (connectedCoverAbsoluteNormalizationMap Ω j (D.obj i) (w i)).continuous
  have hmono {i l : I} (hil : i ≤ l) : S i ⊆ S l := by
    intro z hz
    change connectedCoverAbsoluteNormalizationMap Ω j (D.obj i) (w i) z =
      y i (IsLocalRing.closedPoint k) at hz
    have hm := congrArg (fun q => q z)
      (connectedCoverAbsoluteNormalizationMap_naturality Ω j
        (D.map (homOfLE hil)) (w i) (w l) (hw i l hil))
    change connectedCoverCompactificationMap j (D.map (homOfLE hil))
        (connectedCoverAbsoluteNormalizationMap Ω j (D.obj i) (w i) z) =
      connectedCoverAbsoluteNormalizationMap Ω j (D.obj l) (w l) z at hm
    have hp := congrArg (fun q => q (IsLocalRing.closedPoint k)) (hcompat i l hil)
    change connectedCoverCompactificationMap j (D.map (homOfLE hil))
      (y i (IsLocalRing.closedPoint k)) = y l (IsLocalRing.closedPoint k) at hp
    exact hm.symm.trans
      ((congrArg (connectedCoverCompactificationMap j (D.map (homOfLE hil))) hz).trans hp)
  have hSdir : Directed (· ⊇ ·) S := by
    intro i l
    obtain ⟨m, hmi, hml⟩ := hdir i l
    exact ⟨m, hmono hmi, hmono hml⟩
  have hSne (i : I) : (S i).Nonempty :=
    connectedCoverAbsoluteNormalizationMap_surjective Ω j (D.obj i) (w i)
      (y i (IsLocalRing.closedPoint k))
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    S hSdir hSne (fun i => (hclosed i).isCompact) hclosed
  exact ⟨z, fun i => Set.mem_iInter.mp hz i⟩

end AlgebraicGeometry.FiniteEtale
