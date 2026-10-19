/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Trace.Homotopy
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Trace of a perfect object in the actual derived category

A perfect object is an object isomorphic to a bounded complex of finite
projective modules. Native K-projectivity identifies derived morphisms out
of such a complex with homotopy classes of chain maps. This transports the
alternating trace to derived endomorphisms. Cyclicity proves independence
of every choice of finite projective model and of the isomorphism to the
derived object.

This constructs the commutative-ring case of Stacks Project 64.10.2
(https://stacks.math.columbia.edu/tag/03TI). The statement does not assert
that an étale cohomology complex is perfect; that requires its own geometric
finiteness and Tor-dimension arguments.
-/

noncomputable section

universe u v w

open CategoryTheory

namespace EtaleCohomology

variable (R : Type u) [CommRing R]
variable [HasDerivedCategory.{w} (ModuleCat.{v} R)]

private def projectiveDerivedHomEquiv
    (C : CochainComplex (ModuleCat.{v} R) ℤ) (b : ℤ) [C.IsStrictlyLE b]
    [∀ i : ℤ, Module.Projective R (C.X i)]
    (D : HomotopyCategory (ModuleCat.{v} R) (.up ℤ)) :
    ((HomotopyCategory.quotient _ _).obj C ⟶ D) ≃ₗ[R]
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj C) ⟶
        DerivedCategory.Qh.obj D) := by
  have : C.IsKProjective := CochainComplex.isKProjective_of_projective C b
  exact LinearEquiv.ofBijective (DerivedCategory.Qh.mapLinearMap R)
    (CochainComplex.IsKProjective.Qh_map_bijective C D)

section BoundedModel

variable (C : CochainComplex (ModuleCat.{v} R) ℤ)
variable [∀ i : ℤ, Module.Finite R (C.X i)]
  [∀ i : ℤ, Module.Projective R (C.X i)]
variable (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]

/-- Trace on derived endomorphisms of the image of a bounded finite projective complex. -/
def derivedBoundedComplexTrace :
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj C) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj C)) →ₗ[R] R :=
  (homotopyComplexTrace R C a b).comp
    (projectiveDerivedHomEquiv R C b ((HomotopyCategory.quotient _ _).obj C)).symm.toLinearMap

/-- The derived trace agrees with the trace of the original homotopy class. -/
@[simp]
theorem derivedBoundedComplexTrace_map
    (f : (HomotopyCategory.quotient _ _).obj C ⟶
      (HomotopyCategory.quotient _ _).obj C) :
    derivedBoundedComplexTrace R C a b (DerivedCategory.Qh.map f) =
      homotopyComplexTrace R C a b f := by
  change homotopyComplexTrace R C a b
    ((projectiveDerivedHomEquiv R C b _).symm
      ((projectiveDerivedHomEquiv R C b _) f)) = _
  rw [LinearEquiv.symm_apply_apply]

variable {C}
variable {D : CochainComplex (ModuleCat.{v} R) ℤ}
variable [∀ i : ℤ, Module.Finite R (D.X i)]
  [∀ i : ℤ, Module.Projective R (D.X i)]
variable (c d : ℤ) [D.IsStrictlyGE c] [D.IsStrictlyLE d]

/-- Cyclicity for arbitrary derived morphisms between bounded finite projective models. -/
theorem derivedBoundedComplexTrace_comp_comm
    (f : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj C) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj D))
    (g : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj D) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj C)) :
    derivedBoundedComplexTrace R C a b (f ≫ g) =
      derivedBoundedComplexTrace R D c d (g ≫ f) := by
  obtain ⟨f, rfl⟩ := (projectiveDerivedHomEquiv R C b _).surjective f
  obtain ⟨g, rfl⟩ := (projectiveDerivedHomEquiv R D d _).surjective g
  change derivedBoundedComplexTrace R C a b
      (DerivedCategory.Qh.map f ≫ DerivedCategory.Qh.map g) =
    derivedBoundedComplexTrace R D c d
      (DerivedCategory.Qh.map g ≫ DerivedCategory.Qh.map f)
  rw [← Functor.map_comp, ← Functor.map_comp,
    derivedBoundedComplexTrace_map, derivedBoundedComplexTrace_map]
  exact homotopyComplexTrace_comp_comm R a b c d f g

end BoundedModel

/-- A genuine bounded finite projective model of an object in the derived category.
The only comparison datum is an actual isomorphism in that category. -/
structure PerfectComplexModel (K : DerivedCategory (ModuleCat.{v} R)) where
  /-- The representing cochain complex. -/
  complex : CochainComplex (ModuleCat.{v} R) ℤ
  /-- A lower bound on the terms. -/
  lower : ℤ
  /-- An upper bound on the terms. -/
  upper : ℤ
  /-- Each term is a finitely generated module. -/
  finite : ∀ i : ℤ, Module.Finite R (complex.X i)
  /-- Each term is a projective module. -/
  projective : ∀ i : ℤ, Module.Projective R (complex.X i)
  /-- The terms vanish below the lower bound. -/
  boundedBelow : complex.IsStrictlyGE lower
  /-- The terms vanish above the upper bound. -/
  boundedAbove : complex.IsStrictlyLE upper
  /-- The model represents the given derived object. -/
  iso : DerivedCategory.Q.obj complex ≅ K

attribute [instance] PerfectComplexModel.finite PerfectComplexModel.projective
  PerfectComplexModel.boundedBelow PerfectComplexModel.boundedAbove

namespace PerfectComplexModel

variable {R} {K L : DerivedCategory (ModuleCat.{v} R)}

/-- The model comparison after the native factorization through the homotopy category. -/
def derivedIso (P : PerfectComplexModel R K) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P.complex) ≅ K :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).app P.complex ≪≫ P.iso

/-- The trace computed on a specified genuine finite projective model. -/
def trace (P : PerfectComplexModel R K) : (K ⟶ K) →ₗ[R] R :=
  (derivedBoundedComplexTrace R P.complex P.lower P.upper).comp
    (Linear.homCongr R P.derivedIso P.derivedIso).symm.toLinearMap

theorem trace_apply (P : PerfectComplexModel R K) (f : K ⟶ K) :
    P.trace f = derivedBoundedComplexTrace R P.complex P.lower P.upper
      (P.derivedIso.hom ≫ f ≫ P.derivedIso.inv) := rfl

/-- Cyclicity across arbitrary finite projective models of the two derived objects. -/
theorem trace_comp_comm (P : PerfectComplexModel R K) (Q : PerfectComplexModel R L)
    (f : K ⟶ L) (g : L ⟶ K) : P.trace (f ≫ g) = Q.trace (g ≫ f) := by
  rw [trace_apply, trace_apply]
  have h := derivedBoundedComplexTrace_comp_comm R P.lower P.upper Q.lower Q.upper
    (P.derivedIso.hom ≫ f ≫ Q.derivedIso.inv)
    (Q.derivedIso.hom ≫ g ≫ P.derivedIso.inv)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

/-- The trace is independent of the bounded projective model and of its representing isomorphism. -/
theorem trace_independent (P Q : PerfectComplexModel R K) : P.trace = Q.trace := by
  apply LinearMap.ext
  intro f
  simpa only [Category.comp_id, Category.id_comp] using P.trace_comp_comm Q f (𝟙 K)

/-- An actual chain representative computes the model trace by the alternating sum. -/
theorem trace_map (P : PerfectComplexModel R K) (f : P.complex ⟶ P.complex) :
    P.trace (P.iso.inv ≫ DerivedCategory.Q.map f ≫ P.iso.hom) =
      boundedComplexTrace R P.complex P.lower P.upper f := by
  rw [trace_apply]
  have h : P.derivedIso.hom ≫
        (P.iso.inv ≫ DerivedCategory.Q.map f ≫ P.iso.hom) ≫ P.derivedIso.inv =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) := by
    dsimp only [derivedIso, Iso.trans_hom, Iso.trans_inv]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [Iso.app_hom, Iso.app_inv,
      DerivedCategory.quotientCompQhIso_inv_naturality, Iso.hom_inv_id_app_assoc]
  rw [h, derivedBoundedComplexTrace_map, homotopyComplexTrace_map]

/-- Every derived endomorphism has an actual chain representative in any
bounded projective model. This follows from native K-projective localization
and fullness of the homotopy quotient. -/
theorem exists_chainMap (P : PerfectComplexModel R K) (f : K ⟶ K) :
    ∃ g : P.complex ⟶ P.complex,
      P.iso.inv ≫ DerivedCategory.Q.map g ≫ P.iso.hom = f := by
  obtain ⟨g, hg⟩ := (projectiveDerivedHomEquiv R P.complex P.upper
    ((HomotopyCategory.quotient _ _).obj P.complex)).surjective
      (P.derivedIso.hom ≫ f ≫ P.derivedIso.inv)
  change DerivedCategory.Qh.map g = P.derivedIso.hom ≫ f ≫ P.derivedIso.inv at hg
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g, ?_⟩
  apply (Linear.homCongr R P.derivedIso P.derivedIso).symm.injective
  change P.derivedIso.hom ≫
      (P.iso.inv ≫ DerivedCategory.Q.map g ≫ P.iso.hom) ≫ P.derivedIso.inv =
    P.derivedIso.hom ≫ f ≫ P.derivedIso.inv
  rw [← hg]
  dsimp only [derivedIso, Iso.trans_hom, Iso.trans_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [Iso.app_hom, Iso.app_inv,
    DerivedCategory.quotientCompQhIso_inv_naturality, Iso.hom_inv_id_app_assoc]

end PerfectComplexModel

/-- A derived object is perfect when it has a bounded finite projective representative. -/
def IsPerfectComplex (K : DerivedCategory (ModuleCat.{v} R)) : Prop :=
  Nonempty (PerfectComplexModel R K)

/-- The trace of an arbitrary endomorphism of a perfect derived object. -/
def perfectComplexTrace (K : DerivedCategory (ModuleCat.{v} R))
    (hK : IsPerfectComplex R K) : (K ⟶ K) →ₗ[R] R :=
  (Classical.choice hK).trace

/-- Every genuine model computes the intrinsic perfect-complex trace. -/
theorem perfectComplexTrace_eq_modelTrace (K : DerivedCategory (ModuleCat.{v} R))
    (hK : IsPerfectComplex R K) (P : PerfectComplexModel R K) :
    perfectComplexTrace R K hK = P.trace :=
  PerfectComplexModel.trace_independent (Classical.choice hK) P

/-- The intrinsic trace can be computed on any actual chain representative in any model. -/
theorem perfectComplexTrace_map (K : DerivedCategory (ModuleCat.{v} R))
    (hK : IsPerfectComplex R K) (P : PerfectComplexModel R K)
    (f : P.complex ⟶ P.complex) :
    perfectComplexTrace R K hK (P.iso.inv ≫ DerivedCategory.Q.map f ≫ P.iso.hom) =
      boundedComplexTrace R P.complex P.lower P.upper f := by
  rw [perfectComplexTrace_eq_modelTrace R K hK P]
  exact P.trace_map f

/-- Cyclicity for arbitrary morphisms between perfect derived objects. -/
theorem perfectComplexTrace_comp_comm
    {K L : DerivedCategory (ModuleCat.{v} R)}
    (hK : IsPerfectComplex R K) (hL : IsPerfectComplex R L)
    (f : K ⟶ L) (g : L ⟶ K) :
    perfectComplexTrace R K hK (f ≫ g) = perfectComplexTrace R L hL (g ≫ f) :=
  PerfectComplexModel.trace_comp_comm (Classical.choice hK) (Classical.choice hL) f g

/-- Isomorphism invariance of the intrinsic perfect-complex trace. -/
theorem perfectComplexTrace_iso {K L : DerivedCategory (ModuleCat.{v} R)}
    (hK : IsPerfectComplex R K) (hL : IsPerfectComplex R L)
    (e : K ≅ L) (f : K ⟶ K) :
    perfectComplexTrace R L hL (e.inv ≫ f ≫ e.hom) = perfectComplexTrace R K hK f := by
  rw [perfectComplexTrace_comp_comm R hL hK e.inv (f ≫ e.hom),
    Category.assoc, e.hom_inv_id, Category.comp_id]

end EtaleCohomology
