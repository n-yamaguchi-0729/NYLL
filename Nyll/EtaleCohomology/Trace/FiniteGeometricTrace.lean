/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CoefficientEndomorphism
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.FiniteGeometricCohomology
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Constructible.Basic
public import Nyll.EtaleCohomology.Constructible.ModuleStalkFinite
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Nyll.EtaleCohomology.Trace.FiniteFamily
public import Nyll.SchemeTheory.Etale.FiniteGeometricPoints
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Trace

/-!
# The actual point action on cohomology of a finite scheme

An endomorphism of the original scheme and a morphism from the actual
inverse-image coefficient sheaf induce an operator on cohomology. The
geometric-stalk comparison computes this operator coordinate by coordinate
using the original point map and the original coefficient morphism.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology


section FiniteAction

variable (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
variable {Y : Scheme.{u}} (q : Y ⟶ Spec (.of Ω))
variable (f : Y ⟶ Y) (hf : f ≫ q = q)
variable (R : Type u) [CommRing R]
variable (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))
variable (c : (etalePullback f R).obj F ⟶ F)

/-- The actual endomorphism acts on geometric points by postcomposition. -/
def finiteGeometricPointMap :
    {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _} →
      {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _} :=
  fun s => ⟨s.val ≫ f, by rw [Category.assoc, hf, s.property]⟩

/-- The geometric section equivalence intertwines the actual global
operator with the image-point map and actual coefficient action. -/
theorem finiteGeometricGlobalSectionsEquiv_endomorphism [IsFinite q]
    (x : F.obj.obj (op (Scheme.Etale.mk (𝟙 Y))))
    (s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _}) :
    finiteGeometricGlobalSectionsEquiv Ω q R F
        (etaleCoefficientGlobalSectionsEndomorphism f R F c x) s =
      etaleCoefficientGeometricStalkMap f R F c s.val
        (finiteGeometricGlobalSectionsEquiv Ω q R F x (finiteGeometricPointMap Ω q f hf s)) := by
  rw [finiteGeometricGlobalSectionsEquiv_apply, finiteGeometricGlobalSectionsEquiv_apply]
  exact etaleCoefficientGlobalSectionsEndomorphism_germ f R F c s.val x

/-- The actual cohomology operator has the same coordinate action under
the proved degree-zero comparison, without an equivariance assumption. -/
theorem finiteGeometricCohomologyZeroEquiv_endomorphism [IsFinite q]
    (x : etaleCohomology Y R F 0)
    (s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _}) :
    finiteGeometricCohomologyZeroEquiv Ω q R F
        (etaleCoefficientCohomologyEndomorphism f R F c 0 x) s =
      etaleCoefficientGeometricStalkMap f R F c s.val
        (finiteGeometricCohomologyZeroEquiv Ω q R F x (finiteGeometricPointMap Ω q f hf s)) := by
  change finiteGeometricGlobalSectionsEquiv Ω q R F
      (Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u} F _
        (etaleCoefficientCohomologyEndomorphism f R F c 0 x)) s = _
  rw [etaleCoefficientCohomologyEndomorphism_zero_sections]
  exact finiteGeometricGlobalSectionsEquiv_endomorphism Ω q f hf R F c _ s

/-- Conjugation by the constructed comparison gives the actual finite
family operator, with its source index determined by the geometric map. -/
theorem finiteGeometricCohomologyZeroEquiv_conj [IsFinite q] :
    (finiteGeometricCohomologyZeroEquiv Ω q R F).conj
        (etaleCoefficientCohomologyEndomorphism f R F c 0) =
      LinearMap.pi (fun s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _} =>
        (etaleCoefficientGeometricStalkMap f R F c s.val).comp
          (LinearMap.proj (finiteGeometricPointMap Ω q f hf s))) := by
  apply LinearMap.ext
  intro x
  funext s
  change finiteGeometricCohomologyZeroEquiv Ω q R F
      (etaleCoefficientCohomologyEndomorphism f R F c 0
        ((finiteGeometricCohomologyZeroEquiv Ω q R F).symm x)) s = _
  rw [finiteGeometricCohomologyZeroEquiv_endomorphism,
    LinearEquiv.apply_symm_apply]
  rfl

/-- The diagonal block of the original pointwise coefficient action. At a
fixed point its projection and single-coordinate injection give the canonical
identification of the same stalk; at every other point the block is zero. -/
def finiteGeometricStalkDiagonal
    (s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _}) :
    Module.End R (((Scheme.pointSmallEtale s.val).sheafFiber (A := ModuleCat.{u} R)).obj F) := by
  classical
  exact (etaleCoefficientGeometricStalkMap f R F c s.val).comp
    ((LinearMap.proj (finiteGeometricPointMap Ω q f hf s)).comp
      (LinearMap.single R
        (fun t : {t : Spec (.of Ω) ⟶ Y // t ≫ q = 𝟙 _} =>
          ((Scheme.pointSmallEtale t.val).sheafFiber (A := ModuleCat.{u} R)).obj F) s))

/-- The local contribution is zero at an actual nonfixed point. -/
theorem finiteGeometricStalkDiagonal_eq_zero
    (s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _})
    (hs : finiteGeometricPointMap Ω q f hf s ≠ s) :
    finiteGeometricStalkDiagonal Ω q f hf R F c s = 0 := by
  classical
  dsimp only [finiteGeometricStalkDiagonal]
  rw [LinearMap.proj_comp_single_ne _ _ _ _ hs]
  exact LinearMap.comp_zero (etaleCoefficientGeometricStalkMap f R F c s.val)

/-- Positive cohomology vanishing reduces the actual alternating
cohomological trace on a finite scheme to its degree-zero trace. -/
theorem finiteGeometricCohomology_alternatingTrace_eq_zeroTrace [IsFinite q] :
    (∑ᶠ n : ℕ, (-1 : R) ^ n *
      LinearMap.trace R (etaleCohomology Y R F n)
        (etaleCoefficientCohomologyEndomorphism f R F c n)) =
      LinearMap.trace R (etaleCohomology Y R F 0)
        (etaleCoefficientCohomologyEndomorphism f R F c 0) := by
  have hzero (n : ℕ) (hn : n ≠ 0) :
      (-1 : R) ^ n * LinearMap.trace R (etaleCohomology Y R F n)
        (etaleCoefficientCohomologyEndomorphism f R F c n) = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hmap : etaleCoefficientCohomologyEndomorphism f R F c (m + 1) = 0 := by
      apply LinearMap.ext
      intro x
      exact finiteGeometricCohomology_succ_eq_zero Ω q R F m _
    rw [hmap, map_zero, mul_zero]
  rw [finsum_eq_single _ 0 hzero, pow_zero, one_mul]

end FiniteAction

section Trace

variable (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
variable {Y : Scheme.{u}} (q : Y ⟶ Spec (.of Ω)) [IsFinite q]
variable (f : Y ⟶ Y) (hf : f ≫ q = q)
variable (K : Type u) [Field K]
variable (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} K))
variable (c : (etalePullback f K).obj F ⟶ F)

/-- The actual degree-zero cohomology trace on a finite scheme is the sum
of the original coefficient-stalk contributions at its actual fixed points.
Constructibility supplies finite-dimensional stalks, and finiteness of the
scheme supplies the finite point set. -/
theorem finiteGeometricCohomology_trace_eq_sum_fixed
    (hF : IsEtaleConstructible K F) :
    LinearMap.trace K (etaleCohomology Y K F 0)
        (etaleCoefficientCohomologyEndomorphism f K F c 0) =
      ∑ᶠ s : {s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _} //
          finiteGeometricPointMap Ω q f hf s = s},
        LinearMap.trace K
          (((Scheme.pointSmallEtale s.val.val).sheafFiber (A := ModuleCat.{u} K)).obj F)
          (finiteGeometricStalkDiagonal Ω q f hf K F c s.val) := by
  classical
  let I := {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _}
  have : Finite I := q.finite_geometricLifts_of_isFinite (𝟙 (Spec (.of Ω)))
  let : Fintype I := Fintype.ofFinite I
  let V : I → Type u := fun s =>
    ((Scheme.pointSmallEtale s.val).sheafFiber (A := ModuleCat.{u} K)).obj F
  have : ∀ s : I, Module.Finite K (V s) := fun s =>
    moduleFinite_geometricStalk_of_isEtaleConstructible F hF s.val
  let σ : I → I := finiteGeometricPointMap Ω q f hf
  let a : ∀ s : I, V (σ s) →ₗ[K] V s :=
    fun s => etaleCoefficientGeometricStalkMap f K F c s.val
  let e := finiteGeometricCohomologyZeroEquiv Ω q K F
  let E := etaleCoefficientCohomologyEndomorphism f K F c 0
  let d : I → K := fun s => LinearMap.trace K (V s)
    (finiteGeometricStalkDiagonal Ω q f hf K F c s)
  have hconj : e.conj E = LinearMap.pi (fun s => (a s).comp (LinearMap.proj (σ s))) :=
    finiteGeometricCohomologyZeroEquiv_conj Ω q f hf K F c
  calc
    LinearMap.trace K (etaleCohomology Y K F 0) E =
        LinearMap.trace K (∀ s : I, V s) (e.conj E) :=
      (LinearMap.trace_conj' E e).symm
    _ = ∑ s ∈ Finset.univ.filter (fun s => σ s = s), d s := by
      rw [hconj]
      exact trace_finiteFamily_eq_sum_fixed V σ a
    _ = ∑ s : {s : I // σ s = s}, d s.val :=
      Finset.sum_subtype _ (fun s => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]) d
    _ = ∑ᶠ s : {s : I // σ s = s}, d s.val :=
      (finsum_eq_sum_of_fintype _).symm

/-- The zero-dimensional Lefschetz formula for the original scheme and
coefficient morphism, with every actual positive cohomology group included. -/
theorem finiteGeometricCohomology_alternatingTrace_eq_sum_fixed
    (hF : IsEtaleConstructible K F) :
    (∑ᶠ n : ℕ, (-1 : K) ^ n *
      LinearMap.trace K (etaleCohomology Y K F n)
        (etaleCoefficientCohomologyEndomorphism f K F c n)) =
      ∑ᶠ s : {s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _} //
          finiteGeometricPointMap Ω q f hf s = s},
        LinearMap.trace K
          (((Scheme.pointSmallEtale s.val.val).sheafFiber (A := ModuleCat.{u} K)).obj F)
          (finiteGeometricStalkDiagonal Ω q f hf K F c s.val) := by
  rw [finiteGeometricCohomology_alternatingTrace_eq_zeroTrace Ω q f K F c]
  exact finiteGeometricCohomology_trace_eq_sum_fixed Ω q f hf K F c hF

end Trace

end EtaleCohomology
