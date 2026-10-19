/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedLineBundle
import Nyll.AlgebraicCurves.Geometry.Sheaves.Descent.InvertibleIsoToDescentDataIsAffineHom
import Nyll.AlgebraicCurves.Geometry.Sheaves.Descent.InvertibleToDescentDataMapBijective
import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Effective descent of a chosen rigidification

A datum consists of an actual module descent datum and an isomorphism from its
restriction to the canonical descent datum of the unit on the full modulus.
The isomorphism includes its overlap compatibility. Along an affine faithfully
flat cover, both the line bundle and this particular isomorphism descend.

The proof first descends the invertible sheaf. It then descends the trivialization
and its inverse using the bijection on morphisms, and checks both inverse identities
by injectivity. No descent or representability conclusion is assumed as data.
-/

universe u

open CategoryTheory MonoidalCategory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.IsInvertible

/-- An isomorphism between canonical descent data of invertible sheaves descends
to an actual isomorphism, with the specified image. -/
theorem exists_iso_toDescentData_mapIso_eq {Y Y' : Scheme.{u}} (q : Y' ⟶ Y)
    [IsAffineHom q] [Flat q] [Surjective q]
    (L M : Y.Modules) (hL : IsInvertible L) (hM : IsInvertible M)
    (e : (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
      (fun _ : Unit => q)).obj L ≅
      (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q)).obj M) :
    ∃ t : L ≅ M,
      (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q)).mapIso t = e := by
  let F : Y.Modules ⥤
      ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData
        (fun _ : Unit => q) :=
    ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
      (fun _ : Unit => q)
  have hLM : Function.Bijective (F.map : (L ⟶ M) → (F.obj L ⟶ F.obj M)) :=
    toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective q L M hL hM
  have hML : Function.Bijective (F.map : (M ⟶ L) → (F.obj M ⟶ F.obj L)) :=
    toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective q M L hM hL
  have hLL : Function.Bijective (F.map : (L ⟶ L) → (F.obj L ⟶ F.obj L)) :=
    toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective q L L hL hL
  have hMM : Function.Bijective (F.map : (M ⟶ M) → (F.obj M ⟶ F.obj M)) :=
    toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective q M M hM hM
  obtain ⟨a, ha⟩ := hLM.2 e.hom
  obtain ⟨b, hb⟩ := hML.2 e.inv
  have hab : a ≫ b = 𝟙 L := by
    apply hLL.1
    rw [F.map_comp, ha, hb, e.hom_inv_id, F.map_id]
  have hba : b ≫ a = 𝟙 M := by
    apply hMM.1
    rw [F.map_comp, hb, ha, e.inv_hom_id, F.map_id]
  refine ⟨⟨a, b, hab, hba⟩, ?_⟩
  apply CategoryTheory.Iso.ext
  exact ha

end AlgebraicGeometry.Scheme.Modules.IsInvertible

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X D X' : Scheme.{u}} (i : D ⟶ X) (q : X' ⟶ X)

/-- Restrict a module descent datum to the complete modulus by the actual pullback square. -/
def restrictDescentData :
    ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData
      (fun _ : Unit => q) ⥤
    ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData
      (fun _ : Unit => pullback.snd q i) :=
  Pseudofunctor.DescentData.pullFunctor
    ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁)
    (f := fun _ : Unit => q) (p := i)
    (f' := fun _ : Unit => pullback.snd q i) (α := fun a => a)
    (p' := fun _ => pullback.fst q i) (fun _ => pullback.condition)

/-- The canonical comparison between restricting descent data and first restricting
the sheaf itself. Its components are supplied by the pullback pseudofunctor. -/
def restrictCanonicalDescentDataIso :
    ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q) ⋙ restrictDescentData i q ≅
      Scheme.Modules.pullback i ⋙
        ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
          (fun _ : Unit => pullback.snd q i) :=
  Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
    ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁)
    (f := fun _ : Unit => q) (p := i)
    (f' := fun _ : Unit => pullback.snd q i) (α := fun a => a)
    (p' := fun _ => pullback.fst q i) (fun _ => pullback.condition)

/-- A line-bundle descent datum with an actual, overlap-compatible trivialization
along the modulus. The trivialization is retained as data. -/
structure DescentData : Type (u + 1) where
  /-- The sheaf, transition maps, and their cocycle identities. -/
  modules : ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData
    (fun _ : Unit => q)
  /-- The sheaves on the cover are invertible. -/
  isInvertible : ∀ a : Unit, Scheme.Modules.IsInvertible (modules.obj a)
  /-- The chosen trivialization, including compatibility with all transition maps. -/
  trivialization : (restrictDescentData i q).obj modules ≅
    (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
      (fun _ : Unit => pullback.snd q i)).obj (𝟙_ D.Modules)

namespace DescentData

variable {i q}

/-- A global rigidified bundle gives its canonical descent datum, retaining its
specified trivialization rather than choosing a new one. -/
def ofBundle (M : RigidifiedLineBundle i) : DescentData i q where
  modules := (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
    (fun _ : Unit => q)).obj M.L
  isInvertible _ := M.isInvertible.pullback q
  trivialization := (restrictCanonicalDescentDataIso i q).app M.L ≪≫
    (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
      (fun _ : Unit => pullback.snd q i)).mapIso M.trivialization

/-- An affine faithfully flat rigidified descent datum is effective, preserving
the given trivialization as an equality of isomorphisms of descent data. -/
theorem effective [IsAffineHom q] [Flat q] [Surjective q] (d : DescentData i q) :
    ∃ (M : RigidifiedLineBundle i)
      (e : (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q)).obj M.L ≅ d.modules),
      (restrictDescentData i q).mapIso e ≪≫ d.trivialization =
        (restrictCanonicalDescentDataIso i q).app M.L ≪≫
          (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
            (fun _ : Unit => pullback.snd q i)).mapIso M.trivialization := by
  have affineBaseChange : MorphismProperty.IsStableUnderBaseChange
      (fun {Y Z : Scheme.{u}} (f : Y ⟶ Z) => IsAffineHom f) :=
    isAffineHom_isStableUnderBaseChange
  have : IsAffineHom (pullback.snd q i) :=
    affineBaseChange.of_isPullback (IsPullback.of_hasPullback q i) inferInstance
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    Scheme.Modules.IsInvertible.exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
      q d.modules d.isInvertible
  let τ :
      (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => pullback.snd q i)).obj ((Scheme.Modules.pullback i).obj L) ≅
      (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => pullback.snd q i)).obj (𝟙_ D.Modules) :=
    ((restrictCanonicalDescentDataIso i q).app L).symm ≪≫
      (restrictDescentData i q).mapIso e ≪≫ d.trivialization
  obtain ⟨t, ht⟩ := Scheme.Modules.IsInvertible.exists_iso_toDescentData_mapIso_eq
    (pullback.snd q i) ((Scheme.Modules.pullback i).obj L) (𝟙_ D.Modules)
    (hL.pullback i) (Scheme.Modules.isInvertible_unit D) τ
  let M : RigidifiedLineBundle i := ⟨L, hL, t⟩
  refine ⟨M, e, ?_⟩
  change (restrictDescentData i q).mapIso e ≪≫ d.trivialization =
    (restrictCanonicalDescentDataIso i q).app L ≪≫
      (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => pullback.snd q i)).mapIso t
  rw [ht]
  apply CategoryTheory.Iso.ext
  change ((restrictDescentData i q).mapIso e).hom ≫ d.trivialization.hom =
    ((restrictCanonicalDescentDataIso i q).app L).hom ≫
      ((restrictCanonicalDescentDataIso i q).app L).inv ≫
        ((restrictDescentData i q).mapIso e).hom ≫ d.trivialization.hom
  rw [CategoryTheory.Iso.hom_inv_id_assoc]

/-- A specified compatible isomorphism of canonical descent data comes from
exactly one isomorphism preserving the chosen global trivializations. -/
theorem existsUnique_iso_of_compatible_descentIso [IsAffineHom q] [Flat q] [Surjective q]
    (M N : RigidifiedLineBundle i)
    (e : (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
      (fun _ : Unit => q)).obj M.L ≅
      (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q)).obj N.L)
    (he : (restrictDescentData i q).mapIso e ≪≫ (ofBundle (q := q) N).trivialization =
      (ofBundle (q := q) M).trivialization) :
    ∃! a : Iso M N,
      (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q)).mapIso a.toIso = e := by
  have affineBaseChange : MorphismProperty.IsStableUnderBaseChange
      (fun {Y Z : Scheme.{u}} (f : Y ⟶ Z) => IsAffineHom f) :=
    isAffineHom_isStableUnderBaseChange
  have : IsAffineHom (pullback.snd q i) :=
    affineBaseChange.of_isPullback (IsPullback.of_hasPullback q i) inferInstance
  let F : X.Modules ⥤
      ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData
        (fun _ : Unit => q) :=
    ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
      (fun _ : Unit => q)
  let G : D.Modules ⥤
      ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData
        (fun _ : Unit => pullback.snd q i) :=
    ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
      (fun _ : Unit => pullback.snd q i)
  let R :
      ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData
          (fun _ : Unit => q) ⥤
        ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData
          (fun _ : Unit => pullback.snd q i) := restrictDescentData i q
  let P : X.Modules ⥤ D.Modules := Scheme.Modules.pullback i
  let κ : F ⋙ R ≅ P ⋙ G := restrictCanonicalDescentDataIso i q
  obtain ⟨t, ht⟩ := Scheme.Modules.IsInvertible.exists_iso_toDescentData_mapIso_eq
    q M.L N.L M.isInvertible N.isInvertible e
  have ht' : F.mapIso t = e := ht
  have he' : R.mapIso (F.mapIso t) ≪≫ (ofBundle (q := q) N).trivialization =
      (ofBundle (q := q) M).trivialization := by
    rw [ht']
    exact he
  have hc : R.map (F.map t.hom) ≫ κ.hom.app N.L ≫ G.map N.trivialization.hom =
      κ.hom.app M.L ≫ G.map M.trivialization.hom :=
    congrArg CategoryTheory.Iso.hom he'
  have hn : R.map (F.map t.hom) ≫ κ.hom.app N.L =
      κ.hom.app M.L ≫ G.map (P.map t.hom) := κ.hom.naturality t.hom
  have hcompat : P.map t.hom ≫ N.trivialization.hom = M.trivialization.hom := by
    have hinj : Function.Injective (G.map :
        (P.obj M.L ⟶ 𝟙_ D.Modules) → (G.obj (P.obj M.L) ⟶ G.obj (𝟙_ D.Modules))) :=
      (Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
        (pullback.snd q i) (P.obj M.L) (𝟙_ D.Modules) (M.isInvertible.pullback i)
        (Scheme.Modules.isInvertible_unit D)).1
    apply hinj
    rw [G.map_comp]
    apply (cancel_epi (κ.hom.app M.L)).mp
    have hn' := congrArg
      (fun a : R.obj (F.obj M.L) ⟶ G.obj (P.obj N.L) => a ≫ G.map N.trivialization.hom) hn
    simp only [Category.assoc] at hn'
    exact hn'.symm.trans hc
  refine ⟨⟨t, hcompat⟩, ht, ?_⟩
  intro a ha
  apply AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle.Iso.ext
  apply CategoryTheory.Iso.ext
  have hinj : Function.Injective (F.map : (M.L ⟶ N.L) → (F.obj M.L ⟶ F.obj N.L)) :=
    (Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
      q M.L N.L M.isInvertible N.isInvertible).1
  apply hinj
  exact (congrArg CategoryTheory.Iso.hom ha).trans
    (congrArg CategoryTheory.Iso.hom ht).symm

end DescentData

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
