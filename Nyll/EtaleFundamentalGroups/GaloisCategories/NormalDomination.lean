/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCategories.GaloisObjectQuotient
public import Nyll.EtaleFundamentalGroups.GaloisCategories.PointStabilizerMorphism
public import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenNormalUniverse
public import Nyll.ProCGroups.Topologies.TopologicallyCharacteristicSubgroups
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic

/-!
# Pointed Galois domination retaining original normal kernels

The normal core of an actual fibre-point stabilizer determines a Galois
cover mapping to the original cover at that same point. Every original
normal subgroup fixing the point still fixes the new point. In particular,
taking an arithmetic Galois closure does not discard an already established
geometric commutator bound.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C] [GaloisCategory C]
  (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- The native fibre-point stabilizer of an abelian Galois object contains
the closed commutator of the original fundamental group. -/
theorem closedCommutator_le_stabilizer_of_abelian_galois
    (A : C) [IsGalois A] [IsMulCommutative (Aut A)] (x : F.obj A) :
    Subgroup.closedCommutator (Aut F) ≤ MulAction.stabilizer (Aut F) x := by
  have hcomm : commutator (Aut F) ≤ MulAction.stabilizer (Aut F) x := by
    rw [← galoisObjectQuotientMonoidHom_ker F (Aut F) A x]
    exact Abelianization.commutator_subset_ker
      (galoisObjectQuotientMonoidHom F (Aut F) A x)
  exact Subgroup.topologicalClosure_minimal (commutator (Aut F)) hcomm
    ((MulAction.stabilizer (Aut F) x).isClosed_of_isOpen
      (stabilizer_isOpen (Aut F) x))

/-- Construct a pointed Galois cover dominating the original object while
preserving any original normal subgroup that fixes its chosen fibre point.
The new stabilizer is the actual normal core, and the displayed morphism
sends the constructed point to the original point. -/
theorem exists_pointed_galois_domination_preserving_normal
    (A : C) (x : F.obj A) (N : Subgroup (Aut F)) [N.Normal]
    (hN : N ≤ MulAction.stabilizer (Aut F) x) :
    ∃ (B : C) (_ : IsGalois B) (y : F.obj B) (f : B ⟶ A),
      F.map f y = x ∧ N ≤ MulAction.stabilizer (Aut F) y ∧
      MulAction.stabilizer (Aut F) y = (MulAction.stabilizer (Aut F) x).normalCore := by
  let U : OpenSubgroup (Aut F) :=
    ⟨MulAction.stabilizer (Aut F) x, stabilizer_isOpen (Aut F) x⟩
  let V := ProCGroups.ProC.OpenNormalSubgroup.normalCore U
  have hNV : N ≤ (V : Subgroup (Aut F)) := Subgroup.normal_le_normalCore.mpr hN
  obtain ⟨B, hB, y, hy⟩ :=
    exists_galois_object_point_stabilizer_eq_any_universe F V
  let : IsGalois B := hB
  have hxy : MulAction.stabilizer (Aut F) y ≤ MulAction.stabilizer (Aut F) x := by
    rw [hy]
    exact ProCGroups.ProC.OpenNormalSubgroup.normalCore_le U
  obtain ⟨f, hf⟩ := exists_hom_of_pointStabilizer_le F B A y x hxy
  refine ⟨B, hB, y, f, hf, ?_, hy⟩
  rw [hy]
  exact hNV

/-- Two specified points of actual Galois objects admit a common pointed
Galois domination. Its stabilizer is exactly the intersection, and both
morphisms preserve the specified points. In particular the Galois covers
dominating any fixed pointed Galois cover are cofinal among actual pointed
Galois covers. -/
theorem exists_pointed_common_galois_domination
    (A B : C) [IsGalois A] [IsGalois B] (x : F.obj A) (y : F.obj B) :
    ∃ (D : C) (_ : IsGalois D) (z : F.obj D) (f : D ⟶ A) (g : D ⟶ B),
      F.map f z = x ∧ F.map g z = y ∧
      MulAction.stabilizer (Aut F) z =
        MulAction.stabilizer (Aut F) x ⊓ MulAction.stabilizer (Aut F) y := by
  have : (MulAction.stabilizer (Aut F) x).Normal := stabilizer_normal_of_isGalois F A x
  have : (MulAction.stabilizer (Aut F) y).Normal := stabilizer_normal_of_isGalois F B y
  let U : OpenNormalSubgroup (Aut F) :=
    { toOpenSubgroup :=
        ⟨MulAction.stabilizer (Aut F) x ⊓ MulAction.stabilizer (Aut F) y,
          (stabilizer_isOpen (Aut F) x).inter (stabilizer_isOpen (Aut F) y)⟩
      isNormal' := inferInstance }
  obtain ⟨D, hD, z, hz⟩ := exists_galois_object_point_stabilizer_eq_any_universe F U
  let : IsGalois D := hD
  have hzA : MulAction.stabilizer (Aut F) z ≤ MulAction.stabilizer (Aut F) x := by
    rw [hz]
    exact inf_le_left
  have hzB : MulAction.stabilizer (Aut F) z ≤ MulAction.stabilizer (Aut F) y := by
    rw [hz]
    exact inf_le_right
  obtain ⟨f, hf⟩ := exists_hom_of_pointStabilizer_le F D A z x hzA
  obtain ⟨g, hg⟩ := exists_hom_of_pointStabilizer_le F D B z y hzB
  exact ⟨D, hD, z, f, g, hf, hg, hz⟩

end CategoryTheory.PreGaloisCategory
