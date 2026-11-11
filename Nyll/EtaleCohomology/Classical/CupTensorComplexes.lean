/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupTensorAdditive
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Signed tensor symmetry on the original module-sheaf complexes

The actual tensor total complexes of the original étale module sheaves
have a natural symmetry. Its restriction to the original summand in
bidegree `(i, j)` is the original sheaf braiding multiplied by the Koszul
sign `(i * j).negOnePow`. Applying the symmetry twice gives the identity.

The two actual comparisons for shifting the first and second tensor
factor differ by that same sign. These statements concern the original
complex tensor. Descent through quasi-isomorphisms and identification
with arbitrary original Ext cup classes require a separate proof.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

namespace EtaleCohomology.ModuleTensor

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

local instance
    (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) ℤ) :
    HomologicalComplex.HasTensor K L := by
  intro n
  let D : Discrete (((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ)) ⁻¹' {n}) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
    Discrete.functor (fun p => K.X p.1.1 ⊗ L.X p.1.2)
  let P := D ⋙ sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} R)
  let E : Cocone P := colimit.cocone P
  exact HasColimit.mk
    ⟨Sheaf.sheafifyCocone E, Sheaf.isColimitSheafifyCocone E (colimit.isColimit P)⟩

/-- Braiding induces the componentwise isomorphism of tensor bicomplexes. -/
def tensorBicomplexBraidingIso
    {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [BraidedCategory C] (K L : CochainComplex C ℤ) :
    (((curriedTensor C).mapBifunctorHomologicalComplex
      (.up ℤ) (.up ℤ)).obj K).obj L ≅
    ((((curriedTensor C).flip).mapBifunctorHomologicalComplex
      (.up ℤ) (.up ℤ)).obj K).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => HomologicalComplex.Hom.isoOfComponents
      (fun j => β_ (K.X i) (L.X j)) (by
        intro j j' _
        change (β_ (K.X i) (L.X j)).hom ≫ (L.d j j' ▷ K.X i) =
          (K.X i ◁ L.d j j') ≫ (β_ (K.X i) (L.X j')).hom
        exact (BraidedCategory.braiding_naturality_right (K.X i) (L.d j j')).symm)) (by
      intro i i' _
      apply HomologicalComplex.hom_ext
      intro j
      change (β_ (K.X i) (L.X j)).hom ≫ (L.X j ◁ K.d i i') =
        (K.d i i' ▷ L.X j) ≫ (β_ (K.X i') (L.X j)).hom
      exact (BraidedCategory.braiding_naturality_left (K.d i i') (L.X j)).symm)

private theorem tensorBicomplexBraidingIso_hom_f_f
    {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [BraidedCategory C]
    (K L : CochainComplex C ℤ) (i j : ℤ) :
    ((tensorBicomplexBraidingIso K L).hom.f i).f j =
      (β_ (K.X i) (L.X j)).hom := rfl

/-- Symmetry of the actual tensor total complexes of the original
étale module sheaves, including the actual total-complex signs. -/
def cochainTensorSymmetry
    (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) ℤ) :
    HomologicalComplex.tensorObj K L ≅ HomologicalComplex.tensorObj L K :=
  HomologicalComplex₂.total.mapIso (tensorBicomplexBraidingIso K L) (.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K
      (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) (.up ℤ)

/-- The actual tensor of two complex morphisms acts on every original
summand by the original tensor of the corresponding morphisms. -/
@[reassoc]
theorem cochainTensor_ι_map
    {K K' L L' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj K L i j n h ≫ (HomologicalComplex.tensorHom f g).f n =
      (f.f i ⊗ₘ g.f j) ≫ HomologicalComplex.ιTensorObj K' L' i j n h := by
  rw [HomologicalComplex.ι_mapBifunctorMap]
  change (f.f i ▷ L.X j) ≫ (K'.X i ◁ g.f j) ≫
      HomologicalComplex.ιTensorObj K' L' i j n h = _
  rw [← Category.assoc, ← tensorHom_def]

/-- On each original tensor summand, the actual complex symmetry is
the original sheaf braiding with its Koszul sign. -/
@[reassoc]
theorem cochainTensorSymmetry_ι
    (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) ℤ)
    (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj K L i j n h ≫ (cochainTensorSymmetry X R K L).hom.f n =
      (i * j).negOnePow • ((β_ (K.X i) (L.X j)).hom ≫
        HomologicalComplex.ιTensorObj L K j i n ((add_comm j i).trans h)) := by
  let T := curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
  let b := tensorBicomplexBraidingIso K L
  let s := HomologicalComplex.mapBifunctorFlipIso L K T (.up ℤ)
  change HomologicalComplex.ιTensorObj K L i j n h ≫
      ((HomologicalComplex₂.total.map b.hom (.up ℤ)).f n ≫ s.hom.f n) = _
  have hb :
      HomologicalComplex.ιTensorObj K L i j n h ≫
          (HomologicalComplex₂.total.map b.hom (.up ℤ)).f n =
        (β_ (K.X i) (L.X j)).hom ≫
          HomologicalComplex.ιMapBifunctor K L T.flip (.up ℤ) i j n h := by
    have hb' := HomologicalComplex₂.ιTotal_map
      (φ := (tensorBicomplexBraidingIso K L).hom)
      (c₁₂ := .up ℤ) (i₁ := i) (i₂ := j) (i₁₂ := n) (h := h)
    change HomologicalComplex.ιTensorObj K L i j n h ≫
        (HomologicalComplex₂.total.map b.hom (.up ℤ)).f n =
      ((tensorBicomplexBraidingIso K L).hom.f i).f j ≫
        HomologicalComplex.ιMapBifunctor K L T.flip (.up ℤ) i j n h at hb'
    rw [tensorBicomplexBraidingIso_hom_f_f] at hb'
    exact hb'
  have hs :
      HomologicalComplex.ιMapBifunctor K L T.flip (.up ℤ) i j n h ≫ s.hom.f n =
        (j * i).negOnePow • HomologicalComplex.ιTensorObj L K j i n
          ((add_comm j i).trans h) :=
    HomologicalComplex.ι_mapBifunctorFlipIso_hom
      (K₁ := L) (K₂ := K) (F := T) (c := .up ℤ)
      (i₁ := j) (i₂ := i) (j := n) (hj := h)
  rw [← Category.assoc, hb, Category.assoc, hs, mul_comm j i, Linear.comp_units_smul]

/-- The actual signed tensor symmetry is natural in both original
complex morphisms. -/
theorem cochainTensorSymmetry_naturality
    {K K' L L' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    HomologicalComplex.tensorHom f g ≫ (cochainTensorSymmetry X R K' L').hom =
      (cochainTensorSymmetry X R K L).hom ≫ HomologicalComplex.tensorHom g f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  change HomologicalComplex.ιTensorObj K L i j n h ≫
      ((HomologicalComplex.tensorHom f g).f n ≫
        (cochainTensorSymmetry X R K' L').hom.f n) =
    HomologicalComplex.ιTensorObj K L i j n h ≫
      ((cochainTensorSymmetry X R K L).hom.f n ≫
        (HomologicalComplex.tensorHom g f).f n)
  rw [cochainTensor_ι_map_assoc, cochainTensorSymmetry_ι,
    Linear.comp_units_smul, cochainTensorSymmetry_ι_assoc,
    Linear.units_smul_comp, Category.assoc, cochainTensor_ι_map]
  rw [← Category.assoc, BraidedCategory.braiding_naturality, Category.assoc]

/-- Applying the actual signed symmetry twice is the identity on
the original tensor total complex. -/
theorem cochainTensorSymmetry_symmetry
    (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) ℤ) :
    (cochainTensorSymmetry X R K L).hom ≫ (cochainTensorSymmetry X R L K).hom = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  change HomologicalComplex.ιTensorObj K L i j n h ≫
      ((cochainTensorSymmetry X R K L).hom.f n ≫
        (cochainTensorSymmetry X R L K).hom.f n) =
    HomologicalComplex.ιTensorObj K L i j n h ≫ 𝟙 _
  rw [cochainTensorSymmetry_ι_assoc, Linear.units_smul_comp, Category.assoc,
    cochainTensorSymmetry_ι, Linear.comp_units_smul, smul_smul,
    mul_comm j i, Int.units_mul_self, one_smul, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp, Category.comp_id]

/-- Interchanging the two actual shift comparisons for the original
module-sheaf tensor introduces precisely the Koszul sign. -/
theorem cochainTensor_shift_interchange
    (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) ℤ) (a b : ℤ) :
    CochainComplex.mapBifunctorShift₁Iso K (L⟦b⟧)
        (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) a ≪≫
      (shiftFunctor _ a).mapIso (CochainComplex.mapBifunctorShift₂Iso K L
        (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) b) =
    (a * b).negOnePow •
      (CochainComplex.mapBifunctorShift₂Iso (K⟦a⟧) L
        (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) b ≪≫
        (shiftFunctor _ b).mapIso (CochainComplex.mapBifunctorShift₁Iso K L
          (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) a) ≪≫
        (shiftFunctorComm
          (CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) ℤ) a b).app _) :=
  CochainComplex.mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso K L
    (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) a b

end EtaleCohomology.ModuleTensor
