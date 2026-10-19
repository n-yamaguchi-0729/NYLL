/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.FiniteHenselianSections
import Nyll.EtaleCohomology.Sites.FiniteStrictLocalDescent
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Conservative
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Exactness of finite direct image on étale sheaves

An epimorphism of abelian sheaves admits an affine étale lift cover on
each finite affine inverse image. A section of this cover over the strict
local base descends to an actual pointed étale neighborhood. Restriction
along that section gives a preimage of every direct-image germ.

Consequently finite direct image preserves epimorphisms, and its existing
right-adjoint limit preservation gives exactness. Forgetting module
coefficients transports the result to any commutative coefficient ring.
This is Stacks Project 59.55.2(2), without finiteness assumptions on the base.
The product description of a direct-image stalk in part (1) is separate.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

private theorem exists_pointed_etale_baseChange_cover_lift
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ X) (U : X.Etale) [IsAffine U.left]
    (u : (Scheme.pointSmallEtale t).fiber.obj U)
    (W : Y.Etale) [IsAffine W.left]
    (g : W ⟶ (etaleBaseChange q).obj U) [Surjective g.left] :
    ∃ (V : X.Etale) (v : (Scheme.pointSmallEtale t).fiber.obj V) (f : V ⟶ U),
      (Scheme.pointSmallEtale t).fiber.map f v = u ∧
      ∃ k : (etaleBaseChange q).obj V ⟶ W, k ≫ g = (etaleBaseChange q).map f := by
  let B : Y.Etale := (etaleBaseChange q).obj U
  let p : B.left ⟶ U.left := pullback.fst U.hom q
  have : IsFinite p := inferInstanceAs (IsFinite (pullback.fst U.hom q))
  change (Over.mk t ⟶ Over.mk U.hom) at u
  obtain ⟨V₀, v₀, _, s, hs⟩ :=
    exists_affine_pointed_etale_cover_lift_of_isFinite p g.left u.left
  change (Over.mk u.left ⟶ Over.mk V₀.hom) at v₀
  have hv₀ : v₀.left ≫ V₀.hom = u.left := v₀.w
  have hu : u.left ≫ U.hom = t := u.w
  let V : X.Etale := Scheme.Etale.mk (V₀.hom ≫ U.hom)
  let f : V ⟶ U := MorphismProperty.Over.homMk V₀.hom rfl
  let v : (Scheme.pointSmallEtale t).fiber.obj V := Over.homMk v₀.left (by
    exact (Category.assoc v₀.left V₀.hom U.hom).symm.trans
      ((congrArg (fun r => r ≫ U.hom) hv₀).trans hu))
  have hf : (Scheme.pointSmallEtale t).fiber.map f v = u := by
    apply Over.OverMorphism.ext
    exact hv₀
  let D : Y.Etale := (etaleBaseChange q).obj V
  let m : D.left ⟶ B.left := ((etaleBaseChange q).map f).left
  have hm : m ≫ p = pullback.fst V.hom q ≫ V₀.hom := pullback.lift_fst _ _ _
  let l : D.left ⟶ pullback V₀.hom p :=
    pullback.lift (pullback.fst V.hom q) m hm.symm
  have hlg : (l ≫ s) ≫ g.left = m := by
    rw [Category.assoc, hs]
    exact pullback.lift_snd _ _ _
  have hg : g.left ≫ B.hom = W.hom := g.w
  have hmY : m ≫ B.hom = D.hom := ((etaleBaseChange q).map f).w
  let k : D ⟶ W := MorphismProperty.Over.homMk (l ≫ s) (by
    exact (congrArg (fun r => (l ≫ s) ≫ r) hg.symm).trans
      ((Category.assoc (l ≫ s) g.left B.hom).symm.trans
        ((congrArg (fun r => r ≫ B.hom) hlg).trans hmY)))
  refine ⟨V, v, f, hf, k, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  exact hlg

private theorem exists_pointed_finite_pushforward_section_preimage
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ X) (U : X.Etale) [IsAffine U.left]
    (u : (Scheme.pointSmallEtale t).fiber.obj U)
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}} (η : F ⟶ G) [Epi η]
    (a : G.obj.obj (op ((etaleBaseChange q).obj U))) :
    ∃ (V : X.Etale) (v : (Scheme.pointSmallEtale t).fiber.obj V) (f : V ⟶ U),
      (Scheme.pointSmallEtale t).fiber.map f v = u ∧
      ∃ b : F.obj.obj (op ((etaleBaseChange q).obj V)),
        η.hom.app _ b = G.obj.map ((etaleBaseChange q).map f).op a := by
  let B : Y.Etale := (etaleBaseChange q).obj U
  let p : B.left ⟶ U.left := pullback.fst U.hom q
  have : IsFinite p := inferInstanceAs (IsFinite (pullback.fst U.hom q))
  have : IsAffine B.left := isAffine_of_isAffineHom p
  obtain ⟨W, g, hW, hsurj, b, hb⟩ := exists_affine_etale_cover_section_lift η B a
  have : IsAffine W.left := hW
  have : Surjective g.left := hsurj
  obtain ⟨V, v, f, hf, k, hk⟩ :=
    exists_pointed_etale_baseChange_cover_lift q t U u W g
  refine ⟨V, v, f, hf, F.obj.map k.op b, ?_⟩
  rw [NatTrans.naturality_apply, hb, ← G.obj.map_comp_apply, ← op_comp, hk]

/-- An epimorphism of abelian sheaves induces a surjection on every
geometric stalk of its finite direct image. -/
theorem finitePushforward_stalk_map_surjective
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ X)
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}} (η : F ⟶ G) [Epi η] :
    Function.Surjective ((Scheme.pointSmallEtale t).sheafFiber.map
      (((etaleBaseChange q).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Y.smallEtaleTopology).map η)) := by
  let Q := (etaleBaseChange q).sheafPushforwardContinuous AddCommGrpCat.{u}
    X.smallEtaleTopology Y.smallEtaleTopology
  let Φ := Scheme.pointSmallEtale t
  change Function.Surjective (Φ.presheafFiber.map (Q.map η).hom)
  intro a₀
  obtain ⟨U₀, u₀, a₀, rfl⟩ := Φ.toPresheafFiber_jointly_surjective a₀
  obtain ⟨U, u, h, hU, hu⟩ := geometricStalk_exists_affine_refinement t U₀ u₀
  have : IsAffine U.left := hU
  let a : (Q.obj G).obj.obj (op U) := (Q.obj G).obj.map h.op a₀
  obtain ⟨V, v, f, hf, b, hb⟩ :=
    exists_pointed_finite_pushforward_section_preimage q t U u η a
  let b' : (Q.obj F).obj.obj (op V) := b
  have hb' : (Q.map η).hom.app (op V) b' = (Q.obj G).obj.map f.op a := hb
  refine ⟨Φ.toPresheafFiber V v (Q.obj F).obj b', ?_⟩
  calc
    Φ.presheafFiber.map (Q.map η).hom (Φ.toPresheafFiber V v (Q.obj F).obj b') =
        Φ.toPresheafFiber V v (Q.obj G).obj ((Q.map η).hom.app (op V) b') :=
      Φ.toPresheafFiber_naturality_apply (Q.map η).hom V v b'
    _ = Φ.toPresheafFiber V v (Q.obj G).obj ((Q.obj G).obj.map f.op a) :=
      congrArg (Φ.toPresheafFiber V v (Q.obj G).obj) hb'
    _ = Φ.toPresheafFiber U (Φ.fiber.map f v) (Q.obj G).obj a :=
      Φ.toPresheafFiber_w_apply f v (Q.obj G).obj a
    _ = Φ.toPresheafFiber U u (Q.obj G).obj a :=
      congrArg (fun z => Φ.toPresheafFiber U z (Q.obj G).obj a) hf
    _ = Φ.toPresheafFiber U₀ (Φ.fiber.map h u) (Q.obj G).obj a₀ :=
      Φ.toPresheafFiber_w_apply h u (Q.obj G).obj a₀
    _ = Φ.toPresheafFiber U₀ u₀ (Q.obj G).obj a₀ :=
      congrArg (fun z => Φ.toPresheafFiber U₀ z (Q.obj G).obj a₀) hu

/-- Finite direct image on abelian sheaves preserves epimorphisms. -/
instance finitePushforward_preservesEpimorphisms
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q] :
    ((etaleBaseChange q).sheafPushforwardContinuous AddCommGrpCat.{u}
      X.smallEtaleTopology Y.smallEtaleTopology).PreservesEpimorphisms where
  preserves η _ := by
    apply (((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X).jointlyReflectEpimorphisms
      AddCommGrpCat.{u}).epi_iff _).mpr
    rintro ⟨_, ⟨x⟩⟩
    let t : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
      (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
        ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
    change Epi ((Scheme.pointSmallEtale t).sheafFiber.map _)
    exact (AddCommGrpCat.epi_iff_surjective _).mpr
      (finitePushforward_stalk_map_surjective q t η)

/-- The same finite direct image preserves epimorphisms with arbitrary
commutative module coefficients. -/
instance etalePushforwardFinite_preservesEpimorphisms
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q] (Λ : Type u) [CommRing Λ] :
    (etalePushforward q Λ).PreservesEpimorphisms where
  preserves η _ := by
    let U := forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}
    have : U.IsRightAdjoint :=
      ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.symm.toAdjunction.comp
        (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom Λ))).isRightAdjoint
    let ηAb := (sheafCompose Y.smallEtaleTopology U).map η
    have : Sheaf.IsLocallySurjective η :=
      (Sheaf.isLocallySurjective_iff_epi'
        (J := Y.smallEtaleTopology) (ModuleCat.{u} Λ) η).mpr inferInstance
    have : Sheaf.IsLocallySurjective ηAb :=
      { imageSieve_mem a := by
          change Presheaf.imageSieve η.hom a ∈ Y.smallEtaleTopology _
          exact Presheaf.imageSieve_mem Y.smallEtaleTopology η.hom a }
    have : Epi ηAb := Sheaf.epi_of_isLocallySurjective ηAb
    apply (sheafCompose X.smallEtaleTopology U).epi_of_epi_map
    change Epi (((etaleBaseChange q).sheafPushforwardContinuous AddCommGrpCat.{u}
      X.smallEtaleTopology Y.smallEtaleTopology).map ηAb)
    infer_instance

/-- Finite direct image preserves homology, hence exact sequences of
étale sheaves with arbitrary commutative module coefficients. -/
instance etalePushforwardFinite_preservesHomology
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q] (Λ : Type u) [CommRing Λ] :
    (etalePushforward q Λ).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels (etalePushforward q Λ)

end EtaleCohomology
