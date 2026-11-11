/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
public import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationSchemeMap
public import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationSpecifiedLift
public import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The geometric fibers in the strict-local specialization diagram

For the original family `f : X ⟶ S`, the generic and closed geometric fibers
map to the actual pullback of `X` to the strict local model at the closed
point. The generic map retains the chosen lift of the original generic
point; both projection triangles and the corresponding cartesian square
are proved.

The specified-lift existence theorem supplies this diagram without
extending an algebraically closed generic pointing field. The diagram is
valid for arbitrary families, in particular for the proper families of
Stacks Project, Section 58.16, https://stacks.math.columbia.edu/tag/0BUP.
No closed-fiber equivalence or fundamental-group specialization is assumed.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)
  {Ωs Ωt : Type u} [Field Ωs] [Field Ωt]
  (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
  (ψ : geometricStalk
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ωt)
  (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ localGeometricStalkToScheme s = t)

/-- The actual generic geometric fiber maps to the family over the strict
local model through the chosen lift of its original field-valued point. -/
def familySpecializationGenericMap :
    pullback t f ⟶ pullback (localGeometricStalkToScheme s) f :=
  pullback.lift
    (pullback.fst t f ≫ Spec.map (CommRingCat.ofHom ψ))
    (pullback.snd t f)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q : Spec (.of Ωt) ⟶ S => pullback.fst t f ≫ q) hψ).trans
        pullback.condition))

@[reassoc (attr := simp)]
theorem familySpecializationGenericMap_fst :
    familySpecializationGenericMap f s t ψ hψ ≫
        pullback.fst (localGeometricStalkToScheme s) f =
      pullback.fst t f ≫ Spec.map (CommRingCat.ofHom ψ) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem familySpecializationGenericMap_snd :
    familySpecializationGenericMap f s t ψ hψ ≫
        pullback.snd (localGeometricStalkToScheme s) f =
      pullback.snd t f :=
  pullback.lift_snd _ _ _

/-- The original generic fiber is the base change of the actual strict-local
family along the chosen generic lift. -/
theorem familySpecializationGenericMap_isPullback :
    IsPullback (familySpecializationGenericMap f s t ψ hψ) (pullback.fst t f)
      (pullback.fst (localGeometricStalkToScheme s) f)
      (Spec.map (CommRingCat.ofHom ψ)) := by
  apply IsPullback.of_right ?_
    (familySpecializationGenericMap_fst f s t ψ hψ)
    (IsPullback.of_hasPullback (localGeometricStalkToScheme s) f).flip
  simpa only [familySpecializationGenericMap_snd, hψ] using
    (IsPullback.of_hasPullback t f).flip

/-- Evaluation gives the actual closed geometric-fiber map to the strict
local family. -/
def familySpecializationClosedMap :
    pullback s f ⟶ pullback (localGeometricStalkToScheme s) f :=
  familySpecializationGenericMap f s s
    (geometricStalkEvaluation
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))).hom
    (localGeometricStalkToScheme_evaluation s)

@[reassoc (attr := simp)]
theorem familySpecializationClosedMap_fst :
    familySpecializationClosedMap f s ≫
        pullback.fst (localGeometricStalkToScheme s) f =
      pullback.fst s f ≫ Spec.map
        (geometricStalkEvaluation
          (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))) :=
  familySpecializationGenericMap_fst _ _ _ _ _

@[reassoc (attr := simp)]
theorem familySpecializationClosedMap_snd :
    familySpecializationClosedMap f s ≫
        pullback.snd (localGeometricStalkToScheme s) f =
      pullback.snd s f :=
  familySpecializationGenericMap_snd _ _ _ _ _

/-- Evaluation exhibits the original closed geometric fiber as the base
change of the strict-local family. -/
theorem familySpecializationClosedMap_isPullback :
    IsPullback (familySpecializationClosedMap f s) (pullback.fst s f)
      (pullback.fst (localGeometricStalkToScheme s) f)
      (Spec.map (geometricStalkEvaluation
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)))) :=
  familySpecializationGenericMap_isPullback _ _ _ _ _

/-- The specified algebraically closed generic point supplies an actual
cartesian generic-fiber diagram, over the original family and without
changing either pointing field. -/
theorem exists_familySpecializationGenericMap [IsAlgClosed Ωt]
    (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs)) :
    ∃ ψ : geometricStalk
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ωt,
      ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
          (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom ∧
      ∃ hψ : Spec.map (CommRingCat.ofHom ψ) ≫ localGeometricStalkToScheme s = t,
        IsPullback (familySpecializationGenericMap f s t ψ hψ) (pullback.fst t f)
          (pullback.fst (localGeometricStalkToScheme s) f)
          (Spec.map (CommRingCat.ofHom ψ)) := by
  obtain ⟨ψ, hring, hscheme⟩ :=
    exists_localGeometricStalk_specifiedSpecializationLift s t h
  exact ⟨ψ, hring, hscheme, familySpecializationGenericMap_isPullback f s t ψ hscheme⟩

variable [IsSepClosed Ωs]
  (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs))
  (hring : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
    (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom)

/-- The canonical map between strict local models induces a map between
their actual pullbacks of the original family. -/
def familySpecializationModelMap :
    pullback (localGeometricStalkToScheme t) f ⟶
      pullback (localGeometricStalkToScheme s) f :=
  pullback.lift
    (pullback.fst (localGeometricStalkToScheme t) f ≫
      Spec.map (localGeometricStalkSpecializationMap s t h ψ hring))
    (pullback.snd (localGeometricStalkToScheme t) f)
    (by rw [Category.assoc, localGeometricStalkSpecializationMap_toScheme,
      pullback.condition])

@[reassoc (attr := simp)]
theorem familySpecializationModelMap_fst :
    familySpecializationModelMap f s t ψ h hring ≫
        pullback.fst (localGeometricStalkToScheme s) f =
      pullback.fst (localGeometricStalkToScheme t) f ≫
        Spec.map (localGeometricStalkSpecializationMap s t h ψ hring) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem familySpecializationModelMap_snd :
    familySpecializationModelMap f s t ψ h hring ≫
        pullback.snd (localGeometricStalkToScheme s) f =
      pullback.snd (localGeometricStalkToScheme t) f :=
  pullback.lift_snd _ _ _

/-- The generic-fiber arrow is the closed-fiber arrow at the generic point
followed by the canonical specialization map of strict-local families. -/
theorem familySpecializationGenericMap_factorization :
    familySpecializationClosedMap f t ≫
        familySpecializationModelMap f s t ψ h hring =
      familySpecializationGenericMap f s t ψ hψ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, familySpecializationModelMap_fst,
      familySpecializationClosedMap_fst_assoc, familySpecializationGenericMap_fst]
    rw [← Spec.map_comp,
      localGeometricStalkSpecializationMap_evaluation]
  · simp only [Category.assoc, familySpecializationModelMap_snd,
      familySpecializationClosedMap_snd, familySpecializationGenericMap_snd]

end EtaleFundamentalGroups.StrictHenselian
