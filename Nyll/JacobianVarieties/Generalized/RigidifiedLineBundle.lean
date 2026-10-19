/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.SchemeTheory.Modules.Invertible.Invertible
import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor

/-!
# Line bundles with a chosen trivialization along a modulus

The morphism `i : D ⟶ X` is kept as an actual scheme morphism: in applications it is the
inclusion of the full, possibly nonreduced, modulus. The trivialization is data. An isomorphism
must preserve that data. In particular the quotient below does not identify every choice of
trivialization on the same underlying line bundle.

This file constructs objects, their compatible isomorphisms, tensor products, and pullback
along a commuting square. `Classes` denotes the naive quotient by compatible isomorphisms;
no sheafification or representability assertion is implicit in that name.
-/

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.GeneralizedJacobian

/-- A line bundle on `X` with a specified trivialization on the scheme `D`. -/
structure RigidifiedLineBundle {X D : Scheme.{u}} (i : D ⟶ X) : Type (u + 1) where
  /-- The actual sheaf of modules. -/
  L : X.Modules
  /-- Local freeness of rank one. -/
  isInvertible : Scheme.Modules.IsInvertible L
  /-- The chosen isomorphism, including all infinitesimal data on `D`. -/
  trivialization : (Scheme.Modules.pullback i).obj L ≅ (𝟙_ D.Modules)

namespace RigidifiedLineBundle

variable {X D : Scheme.{u}} {i : D ⟶ X}

/-- Isomorphisms of rigidified line bundles must commute with the chosen trivializations. -/
structure Iso (M N : RigidifiedLineBundle i) where
  /-- The underlying line bundle isomorphism. -/
  toIso : M.L ≅ N.L
  /-- Compatibility with the trivializations on `D`. -/
  compatible : (Scheme.Modules.pullback i).map toIso.hom ≫ N.trivialization.hom =
    M.trivialization.hom

namespace Iso

variable {M N P Q : RigidifiedLineBundle i}

@[ext] theorem ext {e f : Iso M N} (h : e.toIso = f.toIso) : e = f := by
  cases e
  cases f
  cases h
  rfl

/-- The identity preserves the chosen trivialization. -/
def refl (M : RigidifiedLineBundle i) : Iso M M where
  toIso := CategoryTheory.Iso.refl M.L
  compatible := by
    change (Scheme.Modules.pullback i).map (𝟙 M.L) ≫ M.trivialization.hom = _
    rw [CategoryTheory.Functor.map_id]
    exact Category.id_comp M.trivialization.hom

/-- Composition of compatible isomorphisms. -/
def trans (e : Iso M N) (f : Iso N P) : Iso M P where
  toIso := e.toIso ≪≫ f.toIso
  compatible := by
    simp only [CategoryTheory.Iso.trans_hom, Functor.map_comp, Category.assoc]
    rw [f.compatible, e.compatible]

/-- The inverse of a compatible isomorphism is compatible. -/
def symm (e : Iso M N) : Iso N M where
  toIso := e.toIso.symm
  compatible := by
    rw [CategoryTheory.Iso.symm_hom, ← e.compatible, ← Category.assoc,
      ← Functor.map_comp, e.toIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

@[simp] theorem refl_trans (e : Iso M N) : (refl M).trans e = e := by
  apply ext
  apply CategoryTheory.Iso.ext
  exact Category.id_comp e.toIso.hom

@[simp] theorem trans_refl (e : Iso M N) : e.trans (refl N) = e := by
  apply ext
  apply CategoryTheory.Iso.ext
  exact Category.comp_id e.toIso.hom

theorem trans_assoc (e : Iso M N) (f : Iso N P) (g : Iso P Q) :
    (e.trans f).trans g = e.trans (f.trans g) := by
  apply ext
  apply CategoryTheory.Iso.ext
  exact Category.assoc e.toIso.hom f.toIso.hom g.toIso.hom

@[simp] theorem trans_symm (e : Iso M N) : e.trans e.symm = refl M := by
  apply ext
  apply CategoryTheory.Iso.ext
  exact e.toIso.hom_inv_id

@[simp] theorem symm_trans (e : Iso M N) : e.symm.trans e = refl N := by
  apply ext
  apply CategoryTheory.Iso.ext
  exact e.toIso.inv_hom_id

end Iso

/-- The unit line bundle, with its canonical chosen trivialization. -/
def unit (i : D ⟶ X) : RigidifiedLineBundle i where
  L := (𝟙_ X.Modules)
  isInvertible := Scheme.Modules.isInvertible_unit X
  trivialization := Scheme.Modules.pullbackTensorUnitObjIso i

/-- Tensor product with the tensor product of the two chosen trivializations. -/
def tensor (M N : RigidifiedLineBundle i) : RigidifiedLineBundle i where
  L := M.L ⊗ N.L
  isInvertible := M.isInvertible.tensor N.isInvertible
  trivialization := Scheme.Modules.pullbackTensorObjIso i M.L N.L ≪≫
    (M.trivialization ⊗ᵢ N.trivialization) ≪≫ λ_ (𝟙_ D.Modules)

/-- The natural comparison of restrictions in a commuting square. -/
def restrictionComparison {X' D' : Scheme.{u}} {i' : D' ⟶ X'}
    (f : X' ⟶ X) (g : D' ⟶ D) (w : i' ≫ f = g ≫ i) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback i' ≅
      Scheme.Modules.pullback i ⋙ Scheme.Modules.pullback g :=
  Scheme.Modules.pullbackComp i' f ≪≫ Scheme.Modules.pullbackCongr w ≪≫
    (Scheme.Modules.pullbackComp g i).symm

/-- Pullback carries the actual chosen trivialization through a commuting square. -/
def pullback {X' D' : Scheme.{u}} {i' : D' ⟶ X'} (M : RigidifiedLineBundle i)
    (f : X' ⟶ X) (g : D' ⟶ D) (w : i' ≫ f = g ≫ i) :
    RigidifiedLineBundle i' where
  L := (Scheme.Modules.pullback f).obj M.L
  isInvertible := M.isInvertible.pullback f
  trivialization := (restrictionComparison f g w).app M.L ≪≫
    (Scheme.Modules.pullback g).mapIso M.trivialization ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso g

/-- Pullback preserves isomorphisms together with their rigidification compatibility. -/
def Iso.pullback {X' D' : Scheme.{u}} {i' : D' ⟶ X'}
    {M N : RigidifiedLineBundle i} (e : Iso M N)
    (f : X' ⟶ X) (g : D' ⟶ D) (w : i' ≫ f = g ≫ i) :
    Iso (M.pullback f g w) (N.pullback f g w) where
  toIso := (Scheme.Modules.pullback f).mapIso e.toIso
  compatible := by
    change (Scheme.Modules.pullback i').map ((Scheme.Modules.pullback f).map e.toIso.hom) ≫
      (restrictionComparison f g w).hom.app N.L ≫
      (Scheme.Modules.pullback g).map N.trivialization.hom ≫
      (Scheme.Modules.pullbackTensorUnitObjIso g).hom =
      (restrictionComparison f g w).hom.app M.L ≫
      (Scheme.Modules.pullback g).map M.trivialization.hom ≫
      (Scheme.Modules.pullbackTensorUnitObjIso g).hom
    have hn :
        (Scheme.Modules.pullback i').map ((Scheme.Modules.pullback f).map e.toIso.hom) ≫
          (restrictionComparison f g w).hom.app N.L =
        (restrictionComparison f g w).hom.app M.L ≫
          (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback i).map e.toIso.hom) :=
      (restrictionComparison f g w).hom.naturality e.toIso.hom
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, e.compatible]

/-- The equivalence relation uses compatible isomorphisms, not underlying isomorphisms. -/
instance setoid (i : D ⟶ X) : Setoid (RigidifiedLineBundle i) where
  r M N := Nonempty (Iso M N)
  iseqv := ⟨fun M => ⟨Iso.refl M⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Naive isomorphism classes, before sheafification or any representability claim. -/
def Classes (i : D ⟶ X) : Type (u + 1) := Quotient (setoid i)

/-- The quotient class of a rigidified line bundle. -/
def classOf (M : RigidifiedLineBundle i) : Classes i := Quotient.mk _ M

theorem classOf_eq_iff (M N : RigidifiedLineBundle i) :
    classOf M = classOf N ↔ Nonempty (Iso M N) := Quotient.eq

/-- Pullback on naive compatible-isomorphism classes. -/
def classesPullback {X' D' : Scheme.{u}} {i' : D' ⟶ X'}
    (f : X' ⟶ X) (g : D' ⟶ D) (w : i' ≫ f = g ≫ i) : Classes i → Classes i' :=
  Quotient.map (fun M => M.pullback f g w) (fun _ _ ⟨e⟩ => ⟨e.pullback f g w⟩)

/-- Change the trivialization on the unit bundle by an actual automorphism on `D`. -/
def unitWith (i : D ⟶ X)
    (a : (𝟙_ D.Modules) ≅ (𝟙_ D.Modules)) :
    RigidifiedLineBundle i where
  L := (𝟙_ X.Modules)
  isInvertible := Scheme.Modules.isInvertible_unit X
  trivialization := Scheme.Modules.pullbackTensorUnitObjIso i ≪≫ a

/-- Restrict an automorphism of the unit sheaf on `X` to `D`. -/
def restrictUnitAut (i : D ⟶ X)
    (a : (𝟙_ X.Modules) ≅ (𝟙_ X.Modules)) :
    (𝟙_ D.Modules) ≅ (𝟙_ D.Modules) :=
  (Scheme.Modules.pullbackTensorUnitObjIso i).symm ≪≫
    (Scheme.Modules.pullback i).mapIso a ≪≫ Scheme.Modules.pullbackTensorUnitObjIso i

/-- Two trivializations of the trivial line bundle are identified exactly when their ratio
extends to an automorphism on `X`. Thus arbitrary automorphisms on `D` are not discarded. -/
theorem unitWith_iso_iff (a b :
    (𝟙_ D.Modules) ≅ (𝟙_ D.Modules)) :
    Nonempty (Iso (unitWith i a) (unitWith i b)) ↔
      ∃ e : (𝟙_ X.Modules) ≅ (𝟙_ X.Modules),
        restrictUnitAut i e ≪≫ b = a := by
  constructor
  · rintro ⟨e⟩
    let e' : (𝟙_ X.Modules) ≅ (𝟙_ X.Modules) := e.toIso
    refine ⟨e', ?_⟩
    apply CategoryTheory.Iso.ext
    have hc : (Scheme.Modules.pullback i).map e'.hom ≫
        (Scheme.Modules.pullbackTensorUnitObjIso i).hom ≫ b.hom =
        (Scheme.Modules.pullbackTensorUnitObjIso i).hom ≫ a.hom := e.compatible
    change (Scheme.Modules.pullbackTensorUnitObjIso i).inv ≫
      (Scheme.Modules.pullback i).map e'.hom ≫
      (Scheme.Modules.pullbackTensorUnitObjIso i).hom ≫ b.hom = a.hom
    exact (congrArg (fun t : (Scheme.Modules.pullback i).obj (𝟙_ X.Modules) ⟶
      (𝟙_ D.Modules) => (Scheme.Modules.pullbackTensorUnitObjIso i).inv ≫ t) hc).trans
        ((Scheme.Modules.pullbackTensorUnitObjIso i).inv_hom_id_assoc a.hom)
  · rintro ⟨e, he⟩
    refine ⟨⟨e, ?_⟩⟩
    have hh := congrArg CategoryTheory.Iso.hom he
    change (Scheme.Modules.pullbackTensorUnitObjIso i).inv ≫
      (Scheme.Modules.pullback i).map e.hom ≫
      (Scheme.Modules.pullbackTensorUnitObjIso i).hom ≫ b.hom = a.hom at hh
    change (Scheme.Modules.pullback i).map e.hom ≫
      (Scheme.Modules.pullbackTensorUnitObjIso i).hom ≫ b.hom =
      (Scheme.Modules.pullbackTensorUnitObjIso i).hom ≫ a.hom
    exact ((Scheme.Modules.pullbackTensorUnitObjIso i).hom_inv_id_assoc
      ((Scheme.Modules.pullback i).map e.hom ≫
        (Scheme.Modules.pullbackTensorUnitObjIso i).hom ≫ b.hom)).symm.trans
      (congrArg (fun t : (𝟙_ D.Modules) ⟶ (𝟙_ D.Modules) =>
        (Scheme.Modules.pullbackTensorUnitObjIso i).hom ≫ t) hh)

end RigidifiedLineBundle

end AlgebraicGeometry.GeneralizedJacobian
