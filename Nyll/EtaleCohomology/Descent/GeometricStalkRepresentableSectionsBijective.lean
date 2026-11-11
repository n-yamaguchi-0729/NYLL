/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.GeometricStalkRepresentableSections
public import Nyll.EtaleCohomology.Sites.GeometricStalkCoverDescent
public import Nyll.EtaleCohomology.Sites.GeometricStalkSchemeLimit
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Represented direct-image germs are strict-local sections

Equality of two represented germs descends along the existing affine-transition
limit. An affine pointed neighborhood receives a map from a coefficient stage
by finality of the existing small index. Mathlib's eventual equality theorem
then gives a later stage, and the existing affine coefficient refinement returns
an actual pointed étale neighborhood on which the sections agree.

Together with the existing existence theorem, this proves bijectivity of the
original represented direct-image stalk map for qcqs morphisms. Neither
properness nor finiteness of the étale representer is required.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

universe u

namespace EtaleCohomology

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω)

private theorem exists_coefficientStage_to_affine_neighborhood
    (U : (Spec (CommRingCat.of R)).Etale) [IsAffine U.left]
    (u : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    ∃ (i : (GeometricStalkAlgebraIndex φ)ᵒᵖ)
      (β : (geometricStalkSpecDiagram φ).obj i ⟶ Over.mk U.hom),
      ((geometricStalkSpecCone φ).π.app i).left ≫ β.left =
        geometricStalkNeighborhoodMap φ U u := by
  let Φ := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))
  let J := Φ.fiber.Elementsᵒᵖ
  let F := FinallySmall.fromFilteredFinalModel.{u} J
  let d : J := op (Functor.elementsMk Φ.fiber U u)
  let i : (GeometricStalkAlgebraIndex φ)ᵒᵖ := op (Functor.Final.lift F d)
  let Z : (Spec (CommRingCat.of R)).Etale := (F.obj i.unop).unop.obj
  let z : Φ.fiber.obj Z := (F.obj i.unop).unop.val
  let a : Z ⟶ U := (Functor.Final.homToLift F d).unop.hom
  have haz : Φ.fiber.map a z = u := (Functor.Final.homToLift F d).unop.map_val
  let b : ((geometricStalkSpecDiagram φ).obj i).left ⟶ U.left :=
    Spec.map a.left.appTop ≫ U.left.isoSpec.inv
  have hb : b ≫ U.hom = ((geometricStalkSpecDiagram φ).obj i).hom := by
    change (Spec.map a.left.appTop ≫ U.left.isoSpec.inv) ≫ U.hom =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ Z.hom.appTop)
    rw [Category.assoc,
      ← Scheme.isoSpec_inv_naturality (X := U.left) (Y := Spec (CommRingCat.of R)) U.hom,
      Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, ← Spec.map_comp]
    apply congrArg Spec.map
    exact congrArg (fun k => (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ k)
      ((Scheme.Hom.comp_appTop a.left U.hom).symm.trans
        (congrArg (fun k : Z.left ⟶ Spec (CommRingCat.of R) => k.appTop) a.w))
  have hγ : a.left.appTop ≫
      geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) Z z =
        geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) U u := by
    have h := Φ.toPresheafFiber_w a z (etaleSections (Spec (CommRingCat.of R)))
    rw [haz] at h
    exact h
  refine ⟨i, Over.homMk b hb, ?_⟩
  change Spec.map (geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) Z z) ≫
    (Spec.map a.left.appTop ≫ U.left.isoSpec.inv) = _
  rw [← Spec.map_comp_assoc, hγ]
  exact (geometricStalkNeighborhoodMap_eq_germ φ U u).symm

private theorem exists_pointed_restriction_eq_of_native_eq
    {X Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (g : Z ⟶ X) [LocallyOfFiniteType g]
    (U : (Spec (CommRingCat.of R)).Etale) [IsAffine U.left]
    (u : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U)
    (a b : ((etaleBaseChange f).obj U).left ⟶ Z)
    (ha : a ≫ g = ((etaleBaseChange f).obj U).hom)
    (hb : b ≫ g = ((etaleBaseChange f).obj U).hom)
    (hab : geometricStalkNeighborhoodBaseChangeMap φ f U u ≫ a =
      geometricStalkNeighborhoodBaseChangeMap φ f U u ≫ b) :
    ∃ (V : (Spec (CommRingCat.of R)).Etale) (α : V ⟶ U)
      (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V),
      (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map α v = u ∧
      ((etaleBaseChange f).map α).left ≫ a = ((etaleBaseChange f).map α).left ≫ b := by
  let D₀ := geometricStalkSpecDiagram φ
  let c₀ := geometricStalkSpecCone φ
  let D := geometricStalkSchemeDiagram φ f
  let c := geometricStalkSchemeCone φ f
  have : ∀ {i j : (GeometricStalkAlgebraIndex φ)ᵒᵖ} (h : i ⟶ j),
      IsAffineHom (D.map h) :=
    fun h => geometricStalkSchemeDiagram_map_isAffineHom φ f h
  have : ∀ i : (GeometricStalkAlgebraIndex φ)ᵒᵖ, CompactSpace (D.obj i) :=
    geometricStalkSchemeDiagram_obj_compactSpace φ f
  let p : D ⟶ (Functor.const ((GeometricStalkAlgebraIndex φ)ᵒᵖ)).obj X :=
    ((Over.forgetCocone X).whisker (D₀ ⋙ Over.pullback f)).ι
  obtain ⟨i, β, hβ⟩ := exists_coefficientStage_to_affine_neighborhood φ U u
  let m : D.obj i ⟶ ((etaleBaseChange f).obj U).left :=
    ((Over.pullback f).map β).left
  let τ : c₀.pt ⟶ Over.mk U.hom :=
    Over.homMk (geometricStalkNeighborhoodMap φ U u)
      (geometricStalkNeighborhoodMap_comp φ U u)
  have hτ : c₀.π.app i ≫ β = τ := Over.OverMorphism.ext hβ
  have hm : c.π.app i ≫ m = geometricStalkNeighborhoodBaseChangeMap φ f U u :=
    (congrArg (fun k => k.left) ((Over.pullback f).map_comp (c₀.π.app i) β)).symm.trans
      (congrArg (fun k => ((Over.pullback f).map k).left) hτ)
  have ha' : p.app i = (m ≫ a) ≫ g :=
    ((Category.assoc m a g).trans
      ((congrArg (fun k => m ≫ k) ha).trans (Over.w ((Over.pullback f).map β)))).symm
  have hb' : p.app i = (m ≫ b) ≫ g :=
    ((Category.assoc m b g).trans
      ((congrArg (fun k => m ≫ k) hb).trans (Over.w ((Over.pullback f).map β)))).symm
  have hab' : c.π.app i ≫ (m ≫ a) = c.π.app i ≫ (m ≫ b) := by
    simpa only [Category.assoc] using
      (congrArg (fun k => k ≫ a) hm).trans
        (hab.trans (congrArg (fun k => k ≫ b) hm).symm)
  obtain ⟨j, hji, heq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    D p g c (geometricStalkSchemeConeIsLimit φ f) (m ≫ a) (m ≫ b) ha' hb' hab'
  obtain ⟨V, v, hV, ρ, hρ, β₀, hρgerm, hβ₀, hρβ₀⟩ :=
    geometricStalk_exists_affine_coefficientFactor φ j
  have : IsAffine V.left := hV
  let βV : Over.mk V.hom ⟶ D₀.obj j := Over.homMk β₀ hβ₀
  let δ : Over.mk V.hom ⟶ Over.mk U.hom := βV ≫ D₀.map hji ≫ β
  let α : V ⟶ U := MorphismProperty.Over.homMk δ.left δ.w
  have hρnative : ρ = geometricStalkNeighborhoodMap φ V v :=
    hρgerm.trans (geometricStalkNeighborhoodMap_eq_germ φ V v).symm
  have hρδ : ρ ≫ δ.left = geometricStalkNeighborhoodMap φ U u := by
    change ρ ≫ (β₀ ≫ (D₀.map hji).left ≫ β.left) = _
    have hw : (c₀.π.app j).left ≫ (D₀.map hji).left = (c₀.π.app i).left :=
      congrArg (fun k => k.left) (c₀.w hji)
    simpa only [Category.assoc] using
      (congrArg (fun k => (k ≫ (D₀.map hji).left) ≫ β.left) hρβ₀).trans
        ((congrArg (fun k => k ≫ β.left) hw).trans hβ)
  have hv : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map α v = u := by
    apply Over.OverMorphism.ext
    let ε := Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ)))
    have hvρ : ε ≫ ρ = v.left :=
      (congrArg (fun k => ε ≫ k) hρnative).trans
        (geometricStalkNeighborhoodMap_evaluation φ V v)
    change v.left ≫ δ.left = u.left
    exact (congrArg (fun k => k ≫ δ.left) hvρ.symm).trans
      ((Category.assoc ε ρ δ.left).trans
        ((congrArg (fun k => ε ≫ k) hρδ).trans
          (geometricStalkNeighborhoodMap_evaluation φ U u)))
  let n := ((Over.pullback f).map βV).left
  have hmap : ((etaleBaseChange f).map α).left = n ≫ D.map hji ≫ m := by
    change ((Over.pullback f).map (βV ≫ D₀.map hji ≫ β)).left = _
    simp only [Functor.map_comp, Over.comp_left]
    rfl
  refine ⟨V, α, v, hv, ?_⟩
  calc
    _ = (n ≫ D.map hji ≫ m) ≫ a := congrArg (fun k => k ≫ a) hmap
    _ = n ≫ (D.map hji ≫ (m ≫ a)) := by rw [Category.assoc, Category.assoc]
    _ = n ≫ (D.map hji ≫ (m ≫ b)) := congrArg (fun k => n ≫ k) heq
    _ = (n ≫ D.map hji ≫ m) ≫ b := by rw [Category.assoc, Category.assoc]
    _ = _ := congrArg (fun k => k ≫ b) hmap.symm

/-- Equality of strict-local represented sections already holds for the
original direct-image germs. Only quasi-compactness of the source is needed. -/
theorem etaleSetPushforwardRepresentableGeometricStalkSections_injective
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (W : X.Etale) :
    Function.Injective (etaleSetPushforwardRepresentableGeometricStalkSections φ f W) := by
  let Φ := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))
  let P := ((etaleSetPushforward f).obj (X.smallEtaleTopology.yoneda.obj W)).obj
  let C := etaleSetPushforwardRepresentableGeometricStalkSections φ f W
  intro x y hxy
  obtain ⟨U, u, a, b, rfl, rfl⟩ := Φ.toPresheafFiber_jointly_surjective₂ (P := P) x y
  change (etaleBaseChange f).obj U ⟶ W at a b
  obtain ⟨V, v, j, hV, hj⟩ :=
    geometricStalk_exists_affine_refinement (Spec.map (CommRingCat.ofHom φ)) U u
  have : IsAffine V.left := hV
  have hj' : Φ.fiber.map j v = u := hj
  let aV : (etaleBaseChange f).obj V ⟶ W := (etaleBaseChange f).map j ≫ a
  let bV : (etaleBaseChange f).obj V ⟶ W := (etaleBaseChange f).map j ≫ b
  have hga : Φ.toPresheafFiber V v P aV = Φ.toPresheafFiber U u P a :=
    (ConcreteCategory.congr_hom (Φ.toPresheafFiber_w j v P) a).trans
      (congrArg (fun w => Φ.toPresheafFiber U w P a) hj')
  have hgb : Φ.toPresheafFiber V v P bV = Φ.toPresheafFiber U u P b :=
    (ConcreteCategory.congr_hom (Φ.toPresheafFiber_w j v P) b).trans
      (congrArg (fun w => Φ.toPresheafFiber U w P b) hj')
  have hxyV : C (Φ.toPresheafFiber V v P aV) = C (Φ.toPresheafFiber V v P bV) :=
    (congrArg C hga).trans (hxy.trans (congrArg C hgb).symm)
  have hca := ConcreteCategory.congr_hom
    (toPresheafFiber_etaleSetPushforwardRepresentableGeometricStalkSections φ f W V v) aV
  have hcb := ConcreteCategory.congr_hom
    (toPresheafFiber_etaleSetPushforwardRepresentableGeometricStalkSections φ f W V v) bV
  have hraw : geometricStalkNeighborhoodBaseChangeMap φ f V v ≫ aV.left =
      geometricStalkNeighborhoodBaseChangeMap φ f V v ≫ bV.left :=
    congrArg (fun k => k.left) (hca.symm.trans (hxyV.trans hcb))
  obtain ⟨T, k, t, ht, heq⟩ := exists_pointed_restriction_eq_of_native_eq
    φ f W.hom V v aV.left bV.left aV.w bV.w hraw
  have hVeq : Φ.toPresheafFiber V v P aV = Φ.toPresheafFiber V v P bV := by
    apply (Φ.toPresheafFiber_eq_iff' (P := P) V v aV bV).mpr
    refine ⟨T, k, t, ht, ?_⟩
    apply MorphismProperty.Over.Hom.ext
    exact heq
  exact hga.symm.trans (hVeq.trans hgb)

/-- For a qcqs source, the actual direct-image stalk of an étale representer
is bijective to its actual strict-local sections. -/
theorem etaleSetPushforwardRepresentableGeometricStalkSections_bijective
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [QuasiSeparated f] (W : X.Etale) :
    Function.Bijective (etaleSetPushforwardRepresentableGeometricStalkSections φ f W) :=
  ⟨etaleSetPushforwardRepresentableGeometricStalkSections_injective φ f W,
    etaleSetPushforwardRepresentableGeometricStalkSections_surjective φ f W⟩

end EtaleCohomology
