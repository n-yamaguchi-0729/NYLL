/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationHomExt
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
public import Nyll.EtaleFundamentalGroups.StrictHenselian.LocalGeometricStalkNaturality
public import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationSchemeMap
public import Nyll.SchemeTheory.LocalGeometry.PointedStalkMap
public import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Naturality of the canonical strict local specialization maps

For a morphism of schemes with squares at the special and generic geometric
points, the canonical strict local specialization maps form a commuting
square whenever the original field-valued lifts are compatible. The
compatibility is an equation between the given field-valued lifts, not an
assumed equality between the constructed strict local maps.

Both pointing fields can be extended, including by transcendental extensions.
Only the two special pointing fields must be separably closed, as required
by the specialization constructions themselves. The generic fields are arbitrary.

The proof uses the actual scheme triangles and evaluation equations.
Cancellation of the ordinary stalk spectrum map recovers the base-ring
equation required by the proved stalk rigidity theorem.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- A map from a strict local model is determined by its actual morphism
to the original scheme and its evaluation at the target pointing field. -/
theorem localGeometricStalk_hom_ext_of_toScheme_evaluation
    {S T : Scheme.{u}} {Ω Ψ : Type u} [Field Ω] [IsSepClosed Ω] [Field Ψ]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ψ) ⟶ T)
    (F G : geometricStalk
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) ⟶
      geometricStalk (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom)))
    (htriangle : Spec.map F ≫ localGeometricStalkToScheme s =
      Spec.map G ≫ localGeometricStalkToScheme s)
    (hevaluation : F ≫ geometricStalkEvaluation
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom)) =
      G ≫ geometricStalkEvaluation
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom))) :
    F = G := by
  apply geometricStalk_hom_ext_of_structure_evaluation
    (Scheme.stalkClosedPointTo s).hom
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom)) F G
  · have hcat : CommRingCat.ofHom
          (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) ≫ F =
        CommRingCat.ofHom
          (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) ≫ G := by
      apply Spec.map_injective
      apply (cancel_mono (S.fromSpecStalk (s (closedPoint Ω)))).mp
      let c : S.presheaf.stalk (s (closedPoint Ω)) ⟶ geometricStalk
          (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) :=
        CommRingCat.ofHom (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom)
      let q := S.fromSpecStalk (s (closedPoint Ω))
      have hF : Spec.map (c ≫ F) ≫ q = Spec.map F ≫ localGeometricStalkToScheme s :=
        (congrArg (fun a : Spec (geometricStalk
            (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom))) ⟶
              Spec (S.presheaf.stalk (s (closedPoint Ω))) => a ≫ q)
          (Spec.map_comp c F)).trans (Category.assoc _ _ _)
      have hG : Spec.map (c ≫ G) ≫ q = Spec.map G ≫ localGeometricStalkToScheme s :=
        (congrArg (fun a : Spec (geometricStalk
            (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom))) ⟶
              Spec (S.presheaf.stalk (s (closedPoint Ω))) => a ≫ q)
          (Spec.map_comp c G)).trans (Category.assoc _ _ _)
      exact hF.trans (htriangle.trans hG.symm)
    exact congrArg CommRingCat.Hom.hom hcat
  · exact hevaluation

/-- A morphism of pointed specialization diagrams gives a commuting square
of the actual canonical maps of strict local models. Compatibility of the
chosen field-valued lifts is retained exactly. -/
theorem localGeometricStalkSpecializationMap_naturality
    {X Y : Scheme.{u}} {Ωsx Ωsy Ωtx Ωty : Type u}
    [Field Ωsx] [IsSepClosed Ωsx] [Field Ωsy] [IsSepClosed Ωsy]
    [Field Ωtx] [Field Ωty]
    (f : X ⟶ Y)
    (sx : Spec (.of Ωsx) ⟶ X) (sy : Spec (.of Ωsy) ⟶ Y)
    (tx : Spec (.of Ωtx) ⟶ X) (ty : Spec (.of Ωty) ⟶ Y)
    (ι : Ωsy →+* Ωsx) (κ : Ωty →+* Ωtx)
    (hs : sx ≫ f = Spec.map (CommRingCat.ofHom ι) ≫ sy)
    (ht : tx ≫ f = Spec.map (CommRingCat.ofHom κ) ≫ ty)
    (hx : tx (closedPoint Ωtx) ⤳ sx (closedPoint Ωsx))
    (hy : ty (closedPoint Ωty) ⤳ sy (closedPoint Ωsy))
    (ψx : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo sx).hom)) →+* Ωtx)
    (hψx : ψx.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo sx).hom) =
      (Scheme.stalkSpecializationToField (sx (closedPoint Ωsx)) tx hx).hom)
    (ψy : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo sy).hom)) →+* Ωty)
    (hψy : ψy.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo sy).hom) =
      (Scheme.stalkSpecializationToField (sy (closedPoint Ωsy)) ty hy).hom)
    (hlifts : ψx.comp (localGeometricStalkMap f sx sy ι hs).hom = κ.comp ψy) :
    localGeometricStalkMap f sx sy ι hs ≫
        localGeometricStalkSpecializationMap sx tx hx ψx hψx =
      localGeometricStalkSpecializationMap sy ty hy ψy hψy ≫
        localGeometricStalkMap f tx ty κ ht := by
  apply localGeometricStalk_hom_ext_of_toScheme_evaluation sy tx
  · calc
      Spec.map (localGeometricStalkMap f sx sy ι hs ≫
          localGeometricStalkSpecializationMap sx tx hx ψx hψx) ≫
            localGeometricStalkToScheme sy =
          localGeometricStalkToScheme tx ≫ f := by
        rw [Spec.map_comp, Category.assoc, localGeometricStalkMap_toScheme,
          ← Category.assoc, localGeometricStalkSpecializationMap_toScheme]
      _ = Spec.map (localGeometricStalkSpecializationMap sy ty hy ψy hψy ≫
          localGeometricStalkMap f tx ty κ ht) ≫ localGeometricStalkToScheme sy := by
        rw [Spec.map_comp, Category.assoc,
          localGeometricStalkSpecializationMap_toScheme, localGeometricStalkMap_toScheme]
  · calc
      (localGeometricStalkMap f sx sy ι hs ≫
          localGeometricStalkSpecializationMap sx tx hx ψx hψx) ≫
            geometricStalkEvaluation
              (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo tx).hom)) =
          CommRingCat.ofHom (ψx.comp (localGeometricStalkMap f sx sy ι hs).hom) := by
        rw [Category.assoc, localGeometricStalkSpecializationMap_evaluation]
        rfl
      _ = CommRingCat.ofHom (κ.comp ψy) := congrArg CommRingCat.ofHom hlifts
      _ = (localGeometricStalkSpecializationMap sy ty hy ψy hψy ≫
          localGeometricStalkMap f tx ty κ ht) ≫
            geometricStalkEvaluation
              (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo tx).hom)) := by
        rw [Category.assoc, localGeometricStalkMap_evaluation, ← Category.assoc,
          localGeometricStalkSpecializationMap_evaluation]
        rfl

/-- Extending both pointing fields preserves the square of the canonical
scheme-local specialization maps for the original compatible lifts. The
extended points are the literal composites with the given field maps. -/
theorem localGeometricStalkSpecializationMap_changeField
    {S : Scheme.{u}} {Ωs Ωs' Ωt Ωt' : Type u}
    [Field Ωs] [IsSepClosed Ωs] [Field Ωs'] [IsSepClosed Ωs']
    [Field Ωt] [Field Ωt']
    (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
    (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs))
    (ι : Ωs →+* Ωs') (κ : Ωt →+* Ωt')
    (ψ : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ωt)
    (hψ : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
      (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom)
    (ψ' : geometricStalk (Spec.map (CommRingCat.ofHom
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ι) ≫ s)).hom)) →+* Ωt')
    (hψ' : ψ'.comp (geometricStalkStructureMap
        (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ι) ≫ s)).hom) =
      (Scheme.stalkSpecializationToField
        ((Spec.map (CommRingCat.ofHom ι) ≫ s) (closedPoint Ωs'))
        (Spec.map (CommRingCat.ofHom κ) ≫ t)
        (by
          change t (Spec.map (CommRingCat.ofHom κ) (closedPoint Ωt')) ⤳
            s (Spec.map (CommRingCat.ofHom ι) (closedPoint Ωs'))
          rw [Spec_closedPoint, Spec_closedPoint]
          exact h)).hom)
    (hlifts : ψ'.comp (localGeometricStalkMap (𝟙 S)
        (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι (Category.comp_id _)).hom =
      κ.comp ψ) :
    localGeometricStalkMap (𝟙 S) (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι
        (Category.comp_id _) ≫
      localGeometricStalkSpecializationMap (Spec.map (CommRingCat.ofHom ι) ≫ s)
        (Spec.map (CommRingCat.ofHom κ) ≫ t)
        (by
          change t (Spec.map (CommRingCat.ofHom κ) (closedPoint Ωt')) ⤳
            s (Spec.map (CommRingCat.ofHom ι) (closedPoint Ωs'))
          rw [Spec_closedPoint, Spec_closedPoint]
          exact h) ψ' hψ' =
      localGeometricStalkSpecializationMap s t h ψ hψ ≫
        localGeometricStalkMap (𝟙 S) (Spec.map (CommRingCat.ofHom κ) ≫ t) t κ
          (Category.comp_id _) :=
  localGeometricStalkSpecializationMap_naturality (𝟙 S)
    (Spec.map (CommRingCat.ofHom ι) ≫ s) s (Spec.map (CommRingCat.ofHom κ) ≫ t) t
    ι κ (Category.comp_id _) (Category.comp_id _)
    (by
          change t (Spec.map (CommRingCat.ofHom κ) (closedPoint Ωt')) ⤳
            s (Spec.map (CommRingCat.ofHom ι) (closedPoint Ωs'))
          rw [Spec_closedPoint, Spec_closedPoint]
          exact h) h
    ψ' hψ' ψ hψ hlifts

end EtaleFundamentalGroups.StrictHenselian
