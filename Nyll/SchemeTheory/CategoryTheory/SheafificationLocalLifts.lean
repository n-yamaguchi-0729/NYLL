/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Transporting actual local representatives of a sheafification

An isomorphism of raw presheaves retains local representatives. Restriction
of the big fppf site to a new base also retains Zariski representatives,
using the actual unit-compatible sheafification comparison.
-/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace SchemeTheory

variable {C : Type u} [Category.{v} C]
  (J K : GrothendieckTopology C) [HasWeakSheafify K (Type w)]
  {F G : Cᵒᵖ ⥤ Type w}

/-- The canonical sheafification map retains local representatives under
an actual isomorphism of the raw presheaves. -/
theorem toSheafify_isLocallySurjective_of_iso (e : F ≅ G)
    [Presheaf.IsLocallySurjective J (toSheafify K F)] :
    Presheaf.IsLocallySurjective J (toSheafify K G) := by
  have he : toSheafify K G = e.inv ≫ toSheafify K F ≫ sheafifyMap K e.hom := by
    rw [← toSheafify_naturality, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  rw [he]
  infer_instance

variable {S S' : Scheme.{u}} (f : S' ⟶ S)
  (P : (Over S)ᵒᵖ ⥤ Type (u + 1))

/-- Zariski local representatives of an fppf sheaf survive arbitrary base
change, with the canonical sheafification map on the new base. -/
theorem toSheafify_isLocallySurjective_overMap
    [Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S)
      (toSheafify (Scheme.fppfTopology.over S) P)] :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S')
      (toSheafify (Scheme.fppfTopology.over S') ((Over.map f).op ⋙ P)) := by
  let c := (Functor.pushforwardContinuousSheafificationCompatibility
    (G := Over.map f) (A := Type (u + 1))
    (J := Scheme.fppfTopology.over S') (K := Scheme.fppfTopology.over S)).app P
  have : Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S')
      (Functor.whiskerLeft (Over.map f).op
        (toSheafify (Scheme.fppfTopology.over S) P)) :=
    Presheaf.isLocallySurjective_whisker
      (Scheme.zariskiTopology.over S') (Scheme.zariskiTopology.over S) (Over.map f) _
  let e : sheafify (Scheme.fppfTopology.over S') ((Over.map f).op ⋙ P) ≅
      (Over.map f).op ⋙ sheafify (Scheme.fppfTopology.over S) P :=
    (sheafToPresheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso c
  have hc : toSheafify (Scheme.fppfTopology.over S') ((Over.map f).op ⋙ P) ≫ e.hom =
      Functor.whiskerLeft (Over.map f).op
        (toSheafify (Scheme.fppfTopology.over S) P) :=
    Functor.toSheafify_pullbackSheafificationCompatibility
      (Over.map f) (Type (u + 1)) (Scheme.fppfTopology.over S')
      (Scheme.fppfTopology.over S) P
  have he : toSheafify (Scheme.fppfTopology.over S') ((Over.map f).op ⋙ P) =
      Functor.whiskerLeft (Over.map f).op
        (toSheafify (Scheme.fppfTopology.over S) P) ≫ e.inv := by
    rw [← hc, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [he]
  infer_instance

/-- An actual raw comparison on a slice also gives local representatives of
sections of the original sheaf restricted to that slice. -/
theorem whisker_toSheafify_isLocallySurjective_of_iso
    {Q : (Over S')ᵒᵖ ⥤ Type (u + 1)} (e : (Over.map f).op ⋙ P ≅ Q)
    [Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S')
      (toSheafify (Scheme.fppfTopology.over S') Q)] :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S')
      (Functor.whiskerLeft (Over.map f).op
        (toSheafify (Scheme.fppfTopology.over S) P)) := by
  have := toSheafify_isLocallySurjective_of_iso.{u + 1, u, u + 1}
    (Scheme.zariskiTopology.over S') (Scheme.fppfTopology.over S') e.symm
  let c := (Functor.pushforwardContinuousSheafificationCompatibility
    (G := Over.map f) (A := Type (u + 1))
    (J := Scheme.fppfTopology.over S') (K := Scheme.fppfTopology.over S)).app P
  let ec : sheafify (Scheme.fppfTopology.over S') ((Over.map f).op ⋙ P) ≅
      (Over.map f).op ⋙ sheafify (Scheme.fppfTopology.over S) P :=
    (sheafToPresheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso c
  have hc : toSheafify (Scheme.fppfTopology.over S') ((Over.map f).op ⋙ P) ≫ ec.hom =
      Functor.whiskerLeft (Over.map f).op
        (toSheafify (Scheme.fppfTopology.over S) P) :=
    Functor.toSheafify_pullbackSheafificationCompatibility
      (Over.map f) (Type (u + 1)) (Scheme.fppfTopology.over S')
      (Scheme.fppfTopology.over S) P
  rw [← hc]
  infer_instance

/-- Local surjectivity of a map on an actual open cover of the base implies
local surjectivity on the whole relative Zariski site. -/
theorem isLocallySurjective_zariski_of_openCover
    {F G : (Over S)ᵒᵖ ⥤ Type (u + 1)} (a : F ⟶ G) (U : S.OpenCover)
    (hU : ∀ i, Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over (U.X i))
      (Functor.whiskerLeft (Over.map (U.f i)).op a)) :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S) a := by
  let J := Scheme.zariskiTopology.over S
  constructor
  intro T s
  let V (i : U.I₀) : Over (U.X i) := Over.mk (pullback.snd T.hom (U.f i))
  let W (i : U.I₀) : Over S := (Over.map (U.f i)).obj (V i)
  let p (i : U.I₀) : W i ⟶ T :=
    Over.homMk (pullback.fst T.hom (U.f i)) pullback.condition
  have hp : Sieve.ofArrows W p ∈ J T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Scheme.Cover.mem_grothendieckTopology
      (P := (@IsOpenImmersion : MorphismProperty Scheme.{u})) (U.pullback₁ T.hom)
  apply J.transitive hp _
  intro Y g hg
  obtain ⟨i, h, rfl⟩ := Sieve.ofArrows.exists hg
  rw [Sieve.pullback_comp]
  apply J.pullback_stable
  have := hU i
  have hi := Presheaf.imageSieve_mem (Scheme.zariskiTopology.over (U.X i))
    (Functor.whiskerLeft (Over.map (U.f i)).op a) (G.map (p i).op s)
  apply J.superset_covering ?_
    ((Scheme.zariskiTopology.over_map_coverPreserving (U.f i)).cover_preserve hi)
  rintro Z _ ⟨Z', g', h', hg', rfl⟩
  apply ((Presheaf.imageSieve a s).pullback (p i)).downward_closed ?_ h'
  obtain ⟨x, hx⟩ := hg'
  refine ⟨x, ?_⟩
  change a.app (op ((Over.map (U.f i)).obj Z')) x =
    G.map (((Over.map (U.f i)).map g') ≫ p i).op s
  rw [op_comp, Functor.map_comp]
  exact hx

/-- Zariski local surjectivity gives an actual affine open cover carrying
raw preimages of the specified section. -/
theorem exists_affineOpenCover_lifts
    {F G : (Over S)ᵒᵖ ⥤ Type (u + 1)} (a : F ⟶ G)
    [Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S) a]
    (T : Over S) (s : G.obj (op T)) :
    ∃ U : Scheme.AffineOpenCover.{u, u} T.left, ∀ i,
      ∃ x : F.obj (op (Over.mk (U.f i ≫ T.hom))),
        a.app (op (Over.mk (U.f i ≫ T.hom))) x =
          G.map (Over.homMk (U.f i) : Over.mk (U.f i ≫ T.hom) ⟶ T).op s := by
  have hs := Presheaf.imageSieve_mem (Scheme.zariskiTopology.over S) a s
  rw [GrothendieckTopology.mem_over_iff] at hs
  obtain ⟨(U : T.left.OpenCover), hU⟩ :=
    Scheme.exists_cover_of_mem_grothendieckTopology hs
  refine ⟨U.affineRefinement, fun i => ?_⟩
  have hi : (Sieve.overEquiv T (Presheaf.imageSieve a s))
      (U.affineRefinement.f i) :=
    (Sieve.overEquiv T (Presheaf.imageSieve a s)).downward_closed
      (hU _ _ (Presieve.ofArrows.mk i.1)) ((U.X i.1).affineCover.f i.2)
  have he := congrArg
    (fun R : Sieve T => R
      (Over.homMk (U.affineRefinement.f i) :
        Over.mk (U.affineRefinement.f i ≫ T.hom) ⟶ T))
    ((Sieve.overEquiv T).symm_apply_apply (Presheaf.imageSieve a s))
  exact he.mp hi

end SchemeTheory
