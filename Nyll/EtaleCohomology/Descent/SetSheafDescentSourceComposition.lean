/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafDescentEqualizer
public import Nyll.EtaleCohomology.Descent.SetSheafDescentAdjunctionUnit
public import Nyll.EtaleCohomology.Descent.GeometricStalkRepresentableSections
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.GeometricStalkNeighborhoodMaps
public import Nyll.EtaleCohomology.Sites.GeometricStalkSectionComparison
public import Nyll.EtaleCohomology.Sites.RepresentablePullback
public import Nyll.EtaleCohomology.Sites.SetPullbackComposition
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Nyll.EtaleCohomology.Sites.Subcanonical
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Types.Basic

/-!
# The original matching unit and source-composition germs

The first matching arrow of the constructed descent equalizer is exactly
direct image of the original overlap unit. For represented coefficients
that unit, followed by the existing Yoneda pullback isomorphism, is the
actual base-change map on sections.

The native strict-local neighborhood maps commute with source composition.
The proof uses the existing pullback-pasting isomorphism and its two
projection formulas. Consequently the original represented germ maps
commute with pulling the original representer to the new source.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

universe u

namespace EtaleCohomology

namespace SetSheafDescent

/-- The first actual equalizer arrow is direct image of the original
first-projection unit. This identifies the constructed arrow itself. -/
theorem firstArrow_eq_pushforward_unit
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    (F : Sheaf Y.smallEtaleTopology (Type u)) :
    firstArrow q F = (etaleSetPushforward q).map
      ((etaleSetPullbackPushforwardAdjunction (pullback.fst q q)).unit.app F) :=
  adjunction_composite_homEquiv_map_counit
    (etaleSetPullbackPushforwardAdjunction q)
    (etaleSetPullbackPushforwardAdjunction (pullback.fst q q)) F

end SetSheafDescent

/-- On represented sheaves the original unit followed by the existing
pullback comparison sends a section to its actual scheme base change. -/
theorem etaleSetPullback_unit_yoneda_apply
    {X Y : Scheme.{u}} (g : Y ⟶ X) (W T : X.Etale) (a : T ⟶ W) :
    (etaleSetPullbackYonedaObjIso g W).hom.hom.app
        (op ((etaleBaseChange g).obj T))
      (((etaleSetPullbackPushforwardAdjunction g).unit.app
        (X.smallEtaleTopology.yoneda.obj W)).hom.app (op T) a) =
      (etaleBaseChange g).map a := by
  let A := X.smallEtaleTopology.yoneda.obj W
  let B := (etaleSetPushforward g).obj
    (Y.smallEtaleTopology.yoneda.obj ((etaleBaseChange g).obj W))
  have h := etaleSetPullbackYonedaObjIso_hom_homEquiv g W
  rw [Adjunction.homEquiv_unit] at h
  have hvalue := ConcreteCategory.congr_hom
    (congrArg (fun m : A ⟶ B => m.hom.app (op T)) h) a
  have hy := X.smallEtaleTopology.yonedaEquiv_symm_app_apply
    (F := B) (𝟙 ((etaleBaseChange g).obj W)) (op T) a
  refine hvalue.trans (hy.trans ?_)
  change (etaleBaseChange g).map a ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The original direct-image composition comparison restricts
represented sections along its original site pullback-pasting arrow. -/
theorem etaleSetPushforwardCompIso_yoneda_app
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X)
    (W : Y.Etale) (U : S.Etale)
    (a : (etaleBaseChange g).obj ((etaleBaseChange f).obj U) ⟶ W) :
    ((etaleSetPushforwardCompIso g f).hom.app
        (Y.smallEtaleTopology.yoneda.obj W)).hom.app (op U) a =
      (MorphismProperty.Over.pullbackComp
        (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) g f).hom.app U ≫ a := rfl

/-- The original unit and original direct-image composition comparison
send a represented section to its actual source base change. -/
theorem etaleSetPushforward_unit_yoneda_comp_app
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X)
    (W : X.Etale) (U : S.Etale) (a : (etaleBaseChange f).obj U ⟶ W) :
    ((etaleSetPushforward f).map
      ((etaleSetPullbackPushforwardAdjunction g).unit.app
          (X.smallEtaleTopology.yoneda.obj W) ≫
        (etaleSetPushforward g).map (etaleSetPullbackYonedaObjIso g W).hom) ≫
      (etaleSetPushforwardCompIso g f).hom.app
        (Y.smallEtaleTopology.yoneda.obj ((etaleBaseChange g).obj W))).hom.app (op U) a =
    (MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) g f).hom.app U ≫
      (etaleBaseChange g).map a := by
  let T : X.Etale := (etaleBaseChange f).obj U
  let B : Y.Etale := (etaleBaseChange g).obj T
  let C : Y.Etale := (etaleBaseChange g).obj W
  let c : (etaleBaseChange (g ≫ f)).obj U ⟶ B :=
    (MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) g f).hom.app U
  let b : B ⟶ C := (etaleSetPullbackYonedaObjIso g W).hom.hom.app (op B)
    (((etaleSetPullbackPushforwardAdjunction g).unit.app
      (X.smallEtaleTopology.yoneda.obj W)).hom.app (op T) a)
  have hb : b = (etaleBaseChange g).map a :=
    etaleSetPullback_unit_yoneda_apply g W T a
  exact (etaleSetPushforwardCompIso_yoneda_app f g
    C U b).trans (congrArg (fun d : B ⟶ C => c ≫ d) hb)

theorem sourceComp_of_projections
    {S X Y H U : Scheme.{u}} (h : H ⟶ S) (u : U ⟶ S)
    (f : X ⟶ S) (g : Y ⟶ X) (n : H ⟶ U)
    (mX : pullback h f ⟶ pullback u f)
    (mY : pullback h (g ≫ f) ⟶ pullback u (g ≫ f))
    (e : pullback u (g ≫ f) ⟶ pullback (pullback.snd u f) g)
    (p : pullback (pullback.snd h f) g ⟶ pullback (pullback.snd u f) g)
    (he₁ : e ≫ pullback.fst (pullback.snd u f) g ≫ pullback.fst u f =
      pullback.fst u (g ≫ f))
    (he₂ : e ≫ pullback.snd (pullback.snd u f) g = pullback.snd u (g ≫ f))
    (hp₁ : p ≫ pullback.fst (pullback.snd u f) g =
      pullback.fst (pullback.snd h f) g ≫ mX)
    (hp₂ : p ≫ pullback.snd (pullback.snd u f) g =
      pullback.snd (pullback.snd h f) g)
    (hx₁ : mX ≫ pullback.fst u f = pullback.fst h f ≫ n)
    (hy₁ : mY ≫ pullback.fst u (g ≫ f) = pullback.fst h (g ≫ f) ≫ n)
    (hy₂ : mY ≫ pullback.snd u (g ≫ f) = pullback.snd h (g ≫ f)) :
    mY ≫ e = (pullbackLeftPullbackSndIso h f g).inv ≫ p := by
  let s := (pullbackLeftPullbackSndIso h f g).inv
  have hs₁ : s ≫ pullback.fst (pullback.snd h f) g ≫ pullback.fst h f =
      pullback.fst h (g ≫ f) := pullbackLeftPullbackSndIso_inv_fst h f g
  have hs₂ : s ≫ pullback.snd (pullback.snd h f) g =
      pullback.snd h (g ≫ f) := pullbackLeftPullbackSndIso_inv_snd_snd h f g
  let π := pullback.fst (pullback.snd u f) g
  let ρ := pullback.fst u f
  let δ := pullback.snd (pullback.snd u f) g
  let πH := pullback.fst (pullback.snd h f) g
  let ρH := pullback.fst h f
  have hl₁ : (mY ≫ e) ≫ π ≫ ρ = pullback.fst h (g ≫ f) ≫ n :=
    (Category.assoc mY e (π ≫ ρ)).trans
      ((congrArg (fun k => mY ≫ k) he₁).trans hy₁)
  have hs₁n : s ≫ πH ≫ ρH ≫ n = pullback.fst h (g ≫ f) ≫ n :=
    (congrArg (fun k => s ≫ k) (Category.assoc πH ρH n).symm).trans
      ((Category.assoc s (πH ≫ ρH) n).symm.trans
        (congrArg (fun k => k ≫ n) hs₁))
  have hr₁ : (s ≫ p) ≫ π ≫ ρ = pullback.fst h (g ≫ f) ≫ n :=
    (Category.assoc s p (π ≫ ρ)).trans
      ((congrArg (fun k => s ≫ k)
        ((Category.assoc p π ρ).symm.trans
          ((congrArg (fun k => k ≫ ρ) hp₁).trans
            ((Category.assoc πH mX ρ).trans
              (congrArg (fun k => πH ≫ k) hx₁))))).trans hs₁n)
  have hsnd : (mY ≫ e) ≫ δ = (s ≫ p) ≫ δ :=
    ((Category.assoc mY e δ).trans
      ((congrArg (fun k => mY ≫ k) he₂).trans hy₂)).trans
        ((Category.assoc s p δ).trans
          ((congrArg (fun k => s ≫ k) hp₂).trans hs₂)).symm
  have hmid (k : pullback h (g ≫ f) ⟶ pullback (pullback.snd u f) g) :
      (k ≫ π) ≫ pullback.snd u f = (k ≫ δ) ≫ g :=
    (Category.assoc k π (pullback.snd u f)).trans
      ((congrArg (fun l => k ≫ l)
        (pullback.condition (f := pullback.snd u f) (g := g))).trans
          (Category.assoc k δ g).symm)
  exact pullback.hom_ext
    (f := pullback.snd u f) (g := g)
    (pullback.hom_ext (f := u) (g := f)
      ((Category.assoc (mY ≫ e) π ρ).trans
        (hl₁.trans (hr₁.symm.trans (Category.assoc (s ≫ p) π ρ).symm)))
      ((hmid (mY ≫ e)).trans
        ((congrArg (fun k => k ≫ g) hsnd).trans (hmid (s ≫ p)).symm)))
    hsnd

/-- Actual source base change of a represented section over any given
base map, using the existing slice pullback and pullback-pasting iso. -/
def representedSourcePullback
    {S X Y T : Scheme.{u}} (h : T ⟶ S) (f : X ⟶ S) (g : Y ⟶ X) (W : X.Etale) :
    (Over.mk (pullback.snd h f) ⟶ (Scheme.Etale.forget X).obj W) ⟶
      (Over.mk (pullback.snd h (g ≫ f)) ⟶
        (Scheme.Etale.forget Y).obj ((etaleBaseChange g).obj W)) :=
  TypeCat.ofHom (fun a => Over.homMk
    ((pullbackLeftPullbackSndIso
      h f g).inv ≫
      ((Over.pullback g).map a).left)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun b => (pullbackLeftPullbackSndIso
        h f g).inv ≫ b)
        ((Over.pullback g).map a).w).trans
          (pullbackLeftPullbackSndIso_inv_snd_snd _ _ _))))

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω) {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ X)

/-- The original strict-local neighborhood map commutes with source
composition through the existing scheme pullback-pasting isomorphism. -/
theorem geometricStalkNeighborhoodBaseChangeMap_source_comp
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    geometricStalkNeighborhoodBaseChangeMap φ (g ≫ f) U v ≫
        ((MorphismProperty.Over.pullbackComp
          (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) g f).hom.app U).left =
    (pullbackLeftPullbackSndIso
      (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f g).inv ≫
      ((Over.pullback g).map
        (Over.homMk (geometricStalkNeighborhoodBaseChangeMap φ f U v)
          (geometricStalkNeighborhoodBaseChangeMap_snd φ f U v) :
            Over.mk (pullback.snd
              (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ⟶
                (Scheme.Etale.forget X).obj ((etaleBaseChange f).obj U))).left := by
  let h := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let n := geometricStalkNeighborhoodMap φ U v
  let mX := geometricStalkNeighborhoodBaseChangeMap φ f U v
  let mY := geometricStalkNeighborhoodBaseChangeMap φ (g ≫ f) U v
  let e : pullback U.hom (g ≫ f) ⟶ pullback (pullback.snd U.hom f) g :=
    ((MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) g f).hom.app U).left
  let p : pullback (pullback.snd h f) g ⟶ pullback (pullback.snd U.hom f) g :=
    ((Over.pullback g).map
    (Over.homMk mX (geometricStalkNeighborhoodBaseChangeMap_snd φ f U v) :
      Over.mk (pullback.snd h f) ⟶
        (Scheme.Etale.forget X).obj ((etaleBaseChange f).obj U))).left
  have he₁ : e ≫ pullback.fst (pullback.snd U.hom f) g ≫ pullback.fst U.hom f =
      pullback.fst U.hom (g ≫ f) :=
    MorphismProperty.Over.pullbackComp_left_fst_fst
      (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) g f U
  have he₂ : e ≫ pullback.snd (pullback.snd U.hom f) g =
      pullback.snd U.hom (g ≫ f) :=
    ((MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) g f).hom.app U).w
  have hp₁ : p ≫ pullback.fst (pullback.snd U.hom f) g =
      pullback.fst (pullback.snd h f) g ≫ mX := pullback.lift_fst _ _ _
  have hp₂ : p ≫ pullback.snd (pullback.snd U.hom f) g =
      pullback.snd (pullback.snd h f) g := pullback.lift_snd _ _ _
  have hx₁ : mX ≫ pullback.fst U.hom f = pullback.fst h f ≫ n :=
    geometricStalkNeighborhoodBaseChangeMap_fst φ f U v
  have hy₁ : mY ≫ pullback.fst U.hom (g ≫ f) = pullback.fst h (g ≫ f) ≫ n :=
    geometricStalkNeighborhoodBaseChangeMap_fst φ (g ≫ f) U v
  have hy₂ : mY ≫ pullback.snd U.hom (g ≫ f) = pullback.snd h (g ≫ f) :=
    geometricStalkNeighborhoodBaseChangeMap_snd φ (g ≫ f) U v
  exact sourceComp_of_projections h U.hom f g n mX mY e p
    he₁ he₂ hp₁ hp₂ hx₁ hy₁ hy₂

/-- Actual base change of a represented strict-local section along the
source map, using the existing over-category pullback and pasting iso. -/
def geometricStalkRepresentableSourcePullback (W : X.Etale) :
    (Over.mk
      (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ⟶
        (Scheme.Etale.forget X).obj W) ⟶
    (Over.mk
      (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) (g ≫ f)) ⟶
        (Scheme.Etale.forget Y).obj ((etaleBaseChange g).obj W)) :=
  representedSourcePullback
    (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f g W

/-- Pulling an original represented section to the new source commutes
with its original strict-local germ map. The source-section map uses the
same site composition isomorphism as the original direct-image functors. -/
theorem geometricStalkRepresentableSectionMap_source_comp
    (W : X.Etale) (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U)
    (a : (etaleBaseChange f).obj U ⟶ W) :
    geometricStalkRepresentableSectionMap φ (g ≫ f) ((etaleBaseChange g).obj W) U v
        ((MorphismProperty.Over.pullbackComp
          (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) g f).hom.app U ≫
          (etaleBaseChange g).map a) =
      geometricStalkRepresentableSourcePullback φ f g W
        (geometricStalkRepresentableSectionMap φ f W U v a) := by
  let h := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let m := geometricStalkNeighborhoodBaseChangeMap φ f U v
  let n : Over.mk (pullback.snd h f) ⟶ Over.mk ((etaleBaseChange f).obj U).hom :=
    Over.homMk m (geometricStalkNeighborhoodBaseChangeMap_snd φ f U v)
  let b : Over.mk ((etaleBaseChange f).obj U).hom ⟶ Over.mk W.hom :=
    (Scheme.Etale.forget X).map a
  let s : pullback h (g ≫ f) ⟶ pullback (pullback.snd h f) g :=
    (pullbackLeftPullbackSndIso h f g).inv
  let e : pullback U.hom (g ≫ f) ⟶ pullback (pullback.snd U.hom f) g :=
    ((MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) g f).hom.app U).left
  have hn : geometricStalkNeighborhoodBaseChangeMap φ (g ≫ f) U v ≫ e =
      s ≫ ((Over.pullback g).map n).left :=
    geometricStalkNeighborhoodBaseChangeMap_source_comp φ f g U v
  have hmap : ((Over.pullback g).map (n ≫ b)).left =
      ((Over.pullback g).map n).left ≫ ((Over.pullback g).map b).left :=
    congrArg (fun k => k.left) ((Over.pullback g).map_comp n b)
  apply Over.OverMorphism.ext
  change geometricStalkNeighborhoodBaseChangeMap φ (g ≫ f) U v ≫
      (e ≫ ((Over.pullback g).map b).left) =
    s ≫ ((Over.pullback g).map (n ≫ b)).left
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ ((Over.pullback g).map b).left) hn).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => s ≫ k) hmap.symm)))

/-- The actual first matching unit, after its original representable and
direct-image composition comparisons, commutes with the original germ
map. No replacement of the unit or source-composition comparison is used. -/
theorem geometricStalkRepresentableSectionMap_unit_source_comp
    (W : X.Etale) (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U)
    (a : (etaleBaseChange f).obj U ⟶ W) :
    geometricStalkRepresentableSectionMap φ (g ≫ f) ((etaleBaseChange g).obj W) U v
      (((etaleSetPushforward f).map
        ((etaleSetPullbackPushforwardAdjunction g).unit.app
            (X.smallEtaleTopology.yoneda.obj W) ≫
          (etaleSetPushforward g).map (etaleSetPullbackYonedaObjIso g W).hom) ≫
        (etaleSetPushforwardCompIso g f).hom.app
          (Y.smallEtaleTopology.yoneda.obj ((etaleBaseChange g).obj W))).hom.app (op U) a) =
    geometricStalkRepresentableSourcePullback φ f g W
      (geometricStalkRepresentableSectionMap φ f W U v a) := by
  exact (congrArg (fun b =>
    geometricStalkRepresentableSectionMap φ (g ≫ f) ((etaleBaseChange g).obj W) U v b)
      (etaleSetPushforward_unit_yoneda_comp_app f g W U a)).trans
        (geometricStalkRepresentableSectionMap_source_comp φ f g W U v a)

end EtaleCohomology
