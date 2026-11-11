/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomologySections
public import Nyll.EtaleCohomology.Sites.BaseChangeStalkProducts
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# Original coefficient endomorphisms on cohomology and sections

An actual scheme endomorphism and a morphism from its inverse-image sheaf
act on cohomology, sections, and geometric stalks. The original degree-zero
and germ comparisons intertwine these actions.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

section CoefficientEndomorphism

variable {Y : Scheme.{u}} (f : Y ⟶ Y) (R : Type u) [CommRing R]
variable (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))
variable (c : (etalePullback f R).obj F ⟶ F)

/-- Pullback along the original endomorphism followed by its coefficient
morphism, acting on actual global sections. -/
def etaleCoefficientGlobalSectionsEndomorphism :
    Module.End R (F.obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) :=
  (c.hom.app (op (Scheme.Etale.mk (𝟙 Y)))).hom.comp
    (etalePullbackGlobalSectionsMap f R F).hom

/-- The same original geometric and coefficient maps act on actual
classical étale cohomology in every degree. -/
def etaleCoefficientCohomologyEndomorphism (n : ℕ) :
    Module.End R (etaleCohomology Y R F n) :=
  (Classical.cohomologyMap.{u + 1, u, u, u, u} c n).comp
    (etaleCohomologyPullbackMap f R F n)

/-- The existing degree-zero equivalence intertwines these actual operators. -/
theorem etaleCoefficientCohomologyEndomorphism_zero_sections
    (x : etaleCohomology Y R F 0) :
    Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u} F
        (MorphismProperty.Over.mkIdTerminal
          (show MorphismProperty Scheme.{u} from @Etale) Y)
        (etaleCoefficientCohomologyEndomorphism f R F c 0 x) =
      etaleCoefficientGlobalSectionsEndomorphism f R F c
        (Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u} F
          (MorphismProperty.Over.mkIdTerminal
            (show MorphismProperty Scheme.{u} from @Etale) Y) x) := by
  let T : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  have hc := Classical.cohomologyZeroEquiv_naturality.{u + 1, u, u, u, u}
    c (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y)
    (etaleCohomologyPullbackMap f R F 0 x)
  have hp := etaleCohomologyPullbackMap_zero_globalSections f R F x
  exact hc.trans (congrArg (c.hom.app (op T)) hp)

/-- Every natural power of the original coefficient action has the same
trace on degree-zero cohomology and on actual global sections. The existing
cohomology comparison supplies the conjugacy; no equivariance premise is needed. -/
theorem etaleCoefficientCohomologyEndomorphism_zero_trace_pow (m : ℕ) :
    LinearMap.trace R (etaleCohomology Y R F 0)
        ((etaleCoefficientCohomologyEndomorphism f R F c 0) ^ m) =
      LinearMap.trace R (F.obj.obj (op (Scheme.Etale.mk (𝟙 Y))))
        ((etaleCoefficientGlobalSectionsEndomorphism f R F c) ^ m) := by
  let H := etaleCohomology Y R F 0
  let S := F.obj.obj (op (Scheme.Etale.mk (𝟙 Y)))
  let e : H ≃ₗ[R] S :=
    Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u} F
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) Y)
  let a : Module.End R H := etaleCoefficientCohomologyEndomorphism f R F c 0
  let b : Module.End R S := etaleCoefficientGlobalSectionsEndomorphism f R F c
  have hc : e.conjRingEquiv a = b := by
    apply LinearMap.ext
    intro s
    change e (a (e.symm s)) = b s
    exact (etaleCoefficientCohomologyEndomorphism_zero_sections
      f R F c (e.symm s)).trans (congrArg b (e.apply_symm_apply s))
  have hp : e.conj (a ^ m) = b ^ m :=
    (e.conjRingEquiv.map_pow a m).trans (congrArg (fun z : Module.End R S => z ^ m) hc)
  change LinearMap.trace R H (a ^ m) = LinearMap.trace R S (b ^ m)
  exact (LinearMap.trace_conj' (a ^ m) e).symm.trans
    (congrArg (LinearMap.trace R S) hp)

/-- The pointwise action uses the actual inverse-image stalk comparison
and the map on stalks of the original coefficient morphism. -/
def etaleCoefficientGeometricStalkMap
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    ((Scheme.pointSmallEtale (s ≫ f)).sheafFiber (A := ModuleCat.{u} R)).obj F →ₗ[R]
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} R)).obj F :=
  ((pullbackUnitGeometricStalkIso R f s F).hom ≫
    ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} R)).map c).hom

/-- The action on an original section germ is the original coefficient
stalk map applied to its germ at the image point. -/
theorem etaleCoefficientGlobalSectionsEndomorphism_germ
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (x : F.obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) :
    etaleGlobalSectionsGerm s R F (etaleCoefficientGlobalSectionsEndomorphism f R F c x) =
      etaleCoefficientGeometricStalkMap f R F c s (etaleGlobalSectionsGerm (s ≫ f) R F x) := by
  let T : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let v : (Scheme.pointSmallEtale s).fiber.obj T := Over.homMk s (Category.comp_id s)
  let G := (etalePullback f R).obj F
  have hn : etaleGlobalSectionsGerm s R G ≫
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} R)).map c =
      c.hom.app (op T) ≫ etaleGlobalSectionsGerm s R F :=
    (Scheme.pointSmallEtale s).toPresheafFiber_naturality c.hom T v
  have hp : etalePullbackGlobalSectionsMap f R F ≫ etaleGlobalSectionsGerm s R G =
      etaleGlobalSectionsGerm (s ≫ f) R F ≫ (pullbackUnitGeometricStalkIso R f s F).hom :=
    etalePullbackGlobalSectionsMap_germ f s R F
  have heq : (etalePullbackGlobalSectionsMap f R F ≫ c.hom.app (op T)) ≫
      etaleGlobalSectionsGerm s R F =
      etaleGlobalSectionsGerm (s ≫ f) R F ≫
        (pullbackUnitGeometricStalkIso R f s F).hom ≫
          ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} R)).map c := by
    calc
      _ = etalePullbackGlobalSectionsMap f R F ≫
          (c.hom.app (op T) ≫ etaleGlobalSectionsGerm s R F) := rfl
      _ = etalePullbackGlobalSectionsMap f R F ≫
          (etaleGlobalSectionsGerm s R G ≫
            ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} R)).map c) :=
        congrArg (fun t => etalePullbackGlobalSectionsMap f R F ≫ t) hn.symm
      _ = (etalePullbackGlobalSectionsMap f R F ≫ etaleGlobalSectionsGerm s R G) ≫
          ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} R)).map c := rfl
      _ = (etaleGlobalSectionsGerm (s ≫ f) R F ≫
          (pullbackUnitGeometricStalkIso R f s F).hom) ≫
          ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} R)).map c :=
        congrArg (fun t =>
          t ≫ ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} R)).map c) hp
      _ = _ := rfl
  exact congrArg (fun t => t.hom x) heq

end CoefficientEndomorphism

end EtaleCohomology
