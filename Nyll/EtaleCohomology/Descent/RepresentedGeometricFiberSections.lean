/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Descent.GeometricStalkRepresentableSections
public import Nyll.EtaleCohomology.Descent.RepresentedSectionEvaluationNaturality
public import Nyll.EtaleCohomology.Sites.GeometricStalkEvaluationCompatibility
public import Nyll.EtaleCohomology.Sites.GeometricStalkEvaluationSections
public import Nyll.EtaleCohomology.Sites.GeometricStalkSectionComparison
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Actual represented geometric-fiber sections over an arbitrary base

The original pointed-neighborhood germ restricts to the actual geometric
fiber by the original slice pullback functor. Over an affine base this is
exactly the already constructed strict-local comparison followed by its
original evaluation map.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

namespace EtaleCohomology

/-- Restrict an actual represented fiber section at the specified lift,
by its canonical section of the original fiber product. -/
def representedGeometricFiberRestriction
    {S Y T : Scheme.{u}} (q : Y ⟶ S) (t : T ⟶ S)
    (s : T ⟶ Y) (hs : s ≫ q = t) (W : Y.Etale) :
    (Over.mk (pullback.snd t q) ⟶ (Scheme.Etale.forget Y).obj W) ⟶
      (Over.mk s ⟶ (Scheme.Etale.forget Y).obj W) :=
  TypeCat.ofHom (fun a => Over.homMk
    (pullback.lift (𝟙 T) s ((Category.id_comp t).trans hs.symm) ≫ a.left)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k =>
        pullback.lift (𝟙 T) s ((Category.id_comp t).trans hs.symm) ≫ k) a.w).trans
          (pullback.lift_snd _ _ _))))


variable {S Y : Scheme.{u}} (q : Y ⟶ S)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (t : Spec (CommRingCat.of Ω) ⟶ S) (W : Y.Etale)

/-- An actual represented direct-image section restricts along the
original pointed neighborhood to the actual geometric fiber. -/
def representedGeometricFiberGerm (U : S.Etale)
    (v : (Scheme.pointSmallEtale t).fiber.obj U) :
    ((etaleSetPushforward q).obj (Y.smallEtaleTopology.yoneda.obj W)).obj.obj (op U) ⟶
      (Over.mk (pullback.snd t q) ⟶ (Scheme.Etale.forget Y).obj W) :=
  TypeCat.ofHom (fun a =>
    (Over.pullback q).map v ≫ (Scheme.Etale.forget Y).map a)

/-- Restriction to the actual geometric fiber respects the original
pointed-neighborhood transition maps. -/
theorem representedGeometricFiberGerm_restriction
    {U V : S.Etale} (a : U ⟶ V)
    (v : (Scheme.pointSmallEtale t).fiber.obj U) :
    ((etaleSetPushforward q).obj (Y.smallEtaleTopology.yoneda.obj W)).obj.map a.op ≫
      representedGeometricFiberGerm q t W U v =
    representedGeometricFiberGerm q t W V ((Scheme.pointSmallEtale t).fiber.map a v) := by
  apply ConcreteCategory.hom_ext
  intro b
  let av := (Scheme.Etale.forget S).map a
  let bw := (Scheme.Etale.forget Y).map b
  change (Over.pullback q).map v ≫ ((Over.pullback q).map av ≫ bw) =
    (Over.pullback q).map (v ≫ av) ≫ bw
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ bw) ((Over.pullback q).map_comp v av).symm)

/-- The original represented direct-image stalk maps to actual sections
on its geometric fiber over an arbitrary scheme base. -/
def etaleSetPushforwardRepresentableFiberSections :
    (Scheme.pointSmallEtale t).sheafFiber.obj
      ((etaleSetPushforward q).obj (Y.smallEtaleTopology.yoneda.obj W)) ⟶
        (Over.mk (pullback.snd t q) ⟶ (Scheme.Etale.forget Y).obj W) :=
  (Scheme.pointSmallEtale t).presheafFiberDesc
    (fun U v => representedGeometricFiberGerm q t W U v)
    (fun _ _ a v => representedGeometricFiberGerm_restriction q t W a v)

/-- The general-base comparison retains its original germ formula. -/
theorem toPresheafFiber_etaleSetPushforwardRepresentableFiberSections
    (U : S.Etale) (v : (Scheme.pointSmallEtale t).fiber.obj U) :
    (Scheme.pointSmallEtale t).toPresheafFiber U v
      ((etaleSetPushforward q).obj (Y.smallEtaleTopology.yoneda.obj W)).obj ≫
        etaleSetPushforwardRepresentableFiberSections q t W =
      representedGeometricFiberGerm q t W U v :=
  (Scheme.pointSmallEtale t).toPresheafFiber_presheafFiberDesc _ _ U v

/-- Coefficient maps act by literal postcomposition on actual geometric
fiber sections of the original representer. -/
theorem etaleSetPushforwardRepresentableFiberSections_naturality
    {W V : Y.Etale} (a : W ⟶ V) :
    (Scheme.pointSmallEtale t).sheafFiber.map
      ((etaleSetPushforward q).map (Y.smallEtaleTopology.yoneda.map a)) ≫
        etaleSetPushforwardRepresentableFiberSections q t V =
      etaleSetPushforwardRepresentableFiberSections q t W ≫
        TypeCat.ofHom (fun b => b ≫ (Scheme.Etale.forget Y).map a) := by
  apply (Scheme.pointSmallEtale t).presheafFiber_hom_ext
  intro U v
  let Φ := Scheme.pointSmallEtale t
  let δ := (etaleSetPushforward q).map (Y.smallEtaleTopology.yoneda.map a)
  let γW := Φ.toPresheafFiber U v ((etaleSetPushforward q).obj
    (Y.smallEtaleTopology.yoneda.obj W)).obj
  let γV := Φ.toPresheafFiber U v ((etaleSetPushforward q).obj
    (Y.smallEtaleTopology.yoneda.obj V)).obj
  let CW := etaleSetPushforwardRepresentableFiberSections q t W
  let CV := etaleSetPushforwardRepresentableFiberSections q t V
  let bW := representedGeometricFiberGerm q t W U v
  let bV := representedGeometricFiberGerm q t V U v
  let k := TypeCat.ofHom
    (fun b : Over.mk (pullback.snd t q) ⟶ (Scheme.Etale.forget Y).obj W =>
      b ≫ (Scheme.Etale.forget Y).map a)
  have hn : γW ≫ Φ.sheafFiber.map δ = δ.hom.app (op U) ≫ γV :=
    Φ.toPresheafFiber_naturality δ.hom U v
  have hW : γW ≫ CW = bW :=
    toPresheafFiber_etaleSetPushforwardRepresentableFiberSections q t W U v
  have hV : γV ≫ CV = bV :=
    toPresheafFiber_etaleSetPushforwardRepresentableFiberSections q t V U v
  have hb : δ.hom.app (op U) ≫ bV = bW ≫ k := by
    apply ConcreteCategory.hom_ext
    intro b
    exact (Category.assoc ((Over.pullback q).map v)
      ((Scheme.Etale.forget Y).map b) ((Scheme.Etale.forget Y).map a)).symm
  change γW ≫ (Φ.sheafFiber.map δ ≫ CV) = γW ≫ (CW ≫ k)
  exact (Category.assoc γW (Φ.sheafFiber.map δ) CV).symm.trans
    ((congrArg (fun d => d ≫ CV) hn).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun d => δ.hom.app (op U) ≫ d) hV).trans
          (hb.trans ((congrArg (fun d => d ≫ k) hW.symm).trans
            (Category.assoc γW CW k))))))

/-- Over an affine base, the general comparison equals the existing
strict-local comparison followed by its original geometric evaluation. -/
theorem etaleSetPushforwardRepresentableFiberSections_eq_affine
    {R : Type u} [CommRing R] (φ : R →+* Ω)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) (V : Y.Etale) :
    etaleSetPushforwardRepresentableFiberSections f (Spec.map (CommRingCat.ofHom φ)) V =
      etaleSetPushforwardRepresentableGeometricFiberSections φ f V := by
  let Φ := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))
  let P := ((etaleSetPushforward f).obj (Y.smallEtaleTopology.yoneda.obj V)).obj
  apply Φ.presheafFiber_hom_ext
  intro U v
  have hl := toPresheafFiber_etaleSetPushforwardRepresentableFiberSections
    f (Spec.map (CommRingCat.ofHom φ)) V U v
  have hr := toPresheafFiber_etaleSetPushforwardRepresentableGeometricStalkSections
    φ f V U v
  change Φ.toPresheafFiber U v P ≫ _ =
    Φ.toPresheafFiber U v P ≫
      (etaleSetPushforwardRepresentableGeometricStalkSections φ f V ≫
        geometricStalkEvaluationRepresentedSectionsMap φ f V)
  refine hl.trans (Eq.trans ?_
    ((congrArg (fun k => k ≫ geometricStalkEvaluationRepresentedSectionsMap φ f V) hr).symm.trans
      (Category.assoc _ _ _)))
  apply ConcreteCategory.hom_ext
  intro a
  apply Over.OverMorphism.ext
  change ((Over.pullback f).map v).left ≫ a.left =
    geometricStalkEvaluationBaseChangeMap φ f ≫
      (geometricStalkNeighborhoodBaseChangeMap φ f U v ≫ a.left)
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ a.left)
      (geometricStalkEvaluationBaseChangeMap_comp_neighborhood φ f U v))).symm

/-- The existing proper affine theorem applies to this same general
comparison, without constructing a second section equivalence. -/
theorem etaleSetPushforwardRepresentableFiberSections_bijective_spec
    {R : Type u} [CommRing R] (φ : R →+* Ω)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (V : FiniteEtale Y) :
    Function.Bijective (etaleSetPushforwardRepresentableFiberSections f
      (Spec.map (CommRingCat.ofHom φ)) ((finiteEtaleToEtale Y).obj V)) := by
  rw [etaleSetPushforwardRepresentableFiberSections_eq_affine]
  exact etaleSetPushforwardRepresentableGeometricFiberSections_bijective φ f V

end EtaleCohomology
