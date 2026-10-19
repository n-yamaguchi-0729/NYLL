/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Integral group-valued series from actual affine coordinates

An injective coefficient map allows a map on a finitely generated affine
coordinate algebra to descend once the generator series have integral
coefficients. If the centered generator coefficients lie in the kernel of a
residue map, the descended point reduces to the actual group unit. Products
of these points remain in the reduction kernel by the hom-set group law.

The integrality hypotheses are explicit statements about the actual generator
series. For a valuation ring, use its coefficient inclusion and residue map;
membership in the residue kernel is membership in its maximal ideal.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.IntegralGroupPowerSeries

variable {K A O F k : Type u}
  [CommRing K] [CommRing A] [CommRing O] [CommRing F] [CommRing k]
  [Algebra K A] [Algebra K O] [Algebra K F] [Algebra K k]

private theorem exists_lift_of_generator_mem_range
    {B C : Type u} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    (j : B →ₐ[K] C) (hj : Function.Injective j) (φ : A →ₐ[K] C)
    (S : Finset A) (hS : Algebra.adjoin K (S : Set A) = ⊤)
    (hmem : ∀ a ∈ S, φ a ∈ j.range) :
    ∃ ψ : A →ₐ[K] B, j.comp ψ = φ := by
  have hle : Algebra.adjoin K (S : Set A) ≤ j.range.comap φ :=
    Algebra.adjoin_le hmem
  have hall (a : A) : φ a ∈ j.range := by
    apply hle
    rw [hS]
    trivial
  let e : B ≃ₐ[K] j.range := AlgEquiv.ofInjective j hj
  refine ⟨e.symm.toAlgHom.comp (φ.codRestrict j.range hall), ?_⟩
  apply AlgHom.ext
  intro a
  exact congrArg (fun b : j.range => (b : C))
    (e.apply_symm_apply (⟨φ a, hall a⟩ : j.range))

/-- Integral generator series construct the entire coordinate homomorphism.
Centered coefficients in the residue kernel force its whole reduction to be
the specified unit-coordinate homomorphism. -/
theorem exists_coordinate_lift_reducing_to_unit
    (j : O →ₐ[K] F) (hj : Function.Injective j) (ρ : O →ₐ[K] k)
    (φ : A →ₐ[K] PowerSeries F) (ε : A →ₐ[K] K)
    (S : Finset A) (hS : Algebra.adjoin K (S : Set A) = ⊤)
    (hgen : ∀ a ∈ S, ∃ B : PowerSeries O,
      PowerSeries.map j.toRingHom B = φ a ∧
      ∀ n : ℕ, PowerSeries.coeff n
        (B - PowerSeries.C (algebraMap K O (ε a))) ∈ RingHom.ker ρ.toRingHom) :
    ∃ ψ : A →ₐ[K] PowerSeries O,
      (PowerSeries.mapAlgHom j).comp ψ = φ ∧
      (PowerSeries.mapAlgHom ρ).comp ψ =
        (Algebra.ofId K (PowerSeries k)).comp ε := by
  have hj : Function.Injective (PowerSeries.mapAlgHom j) :=
    PowerSeries.map_injective j.toRingHom hj
  obtain ⟨ψ, hψ⟩ := exists_lift_of_generator_mem_range
    (PowerSeries.mapAlgHom j) hj φ S hS (by
      intro a ha
      obtain ⟨B, hB, _⟩ := hgen a ha
      exact ⟨B, hB⟩)
  refine ⟨ψ, hψ, ?_⟩
  apply AlgHom.ext_of_adjoin_eq_top hS
  intro a ha
  obtain ⟨B, hB, hcentered⟩ := hgen a ha
  have hψa : ψ a = B :=
    hj ((AlgHom.congr_fun hψ a).trans hB.symm)
  have hzero : PowerSeries.map ρ.toRingHom
      (B - PowerSeries.C (algebraMap K O (ε a))) = 0 := by
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_map, map_zero]
    exact hcentered n
  rw [map_sub, PowerSeries.map_C, sub_eq_zero] at hzero
  have hscalar : ρ.toRingHom (algebraMap K O (ε a)) = algebraMap K k (ε a) :=
    ρ.commutes (ε a)
  rw [hscalar] at hzero
  change PowerSeries.map ρ.toRingHom (ψ a) =
    algebraMap K (PowerSeries k) (ε a)
  rw [hψa, PowerSeries.algebraMap_apply]
  exact hzero

private abbrev scalarSpec (B : Type u) [CommRing B] [Algebra K B] :
    Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B)))

private def scalarSpecMap {B C : Type u} [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C] (f : B →ₐ[K] C) :
    scalarSpec (K := K) C ⟶ scalarSpec (K := K) B :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K B)) =
        Spec.map (CommRingCat.ofHom (algebraMap K C))
    rw [← Spec.map_comp]
    apply congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of C => Spec.map h)
    exact CommRingCat.hom_ext f.comp_algebraMap)

private theorem scalarSpecMap_comp {B C D : Type u}
    [CommRing B] [CommRing C] [CommRing D]
    [Algebra K B] [Algebra K C] [Algebra K D]
    (f : B →ₐ[K] C) (g : C →ₐ[K] D) :
    scalarSpecMap (g.comp f) = scalarSpecMap g ≫ scalarSpecMap f := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (g.comp f).toRingHom) =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
  rw [← Spec.map_comp]
  rfl

variable {G : Over (Spec (.of K))} [GrpObj G]

/-- An actual point given in an affine chart descends to the integral
power-series ring and reduces to the group unit. The chart need not itself
be a group, and no group law in chosen coordinates is assumed. -/
theorem exists_integral_point_reducing_to_unit
    (j : O →ₐ[K] F) (hj : Function.Injective j) (ρ : O →ₐ[K] k)
    (i : scalarSpec (K := K) A ⟶ G)
    (φ : A →ₐ[K] PowerSeries F) (ε : A →ₐ[K] K)
    (hε : scalarSpecMap ε ≫ i = (1 : scalarSpec (K := K) K ⟶ G))
    (S : Finset A) (hS : Algebra.adjoin K (S : Set A) = ⊤)
    (hgen : ∀ a ∈ S, ∃ B : PowerSeries O,
      PowerSeries.map j.toRingHom B = φ a ∧
      ∀ n : ℕ, PowerSeries.coeff n
        (B - PowerSeries.C (algebraMap K O (ε a))) ∈ RingHom.ker ρ.toRingHom) :
    ∃ p : scalarSpec (K := K) (PowerSeries O) ⟶ G,
      scalarSpecMap (PowerSeries.mapAlgHom j) ≫ p = scalarSpecMap φ ≫ i ∧
      scalarSpecMap (PowerSeries.mapAlgHom ρ) ≫ p = 1 := by
  obtain ⟨ψ, hψ, hψred⟩ := exists_coordinate_lift_reducing_to_unit
    j hj ρ φ ε S hS hgen
  refine ⟨scalarSpecMap ψ ≫ i, ?_, ?_⟩
  · rw [← Category.assoc, ← scalarSpecMap_comp, hψ]
  · rw [← Category.assoc, ← scalarSpecMap_comp, hψred,
      scalarSpecMap_comp, Category.assoc, hε, MonObj.comp_one]

/-- Products of integral series-valued points reducing to the unit still
reduce to the unit. This is the actual group-point reduction kernel, so
commutativity and formal-coordinate multiplication formulas are unnecessary. -/
theorem reduction_list_prod_eq_one (ρ : O →ₐ[K] k)
    (p : List (scalarSpec (K := K) (PowerSeries O) ⟶ G))
    (hp : ∀ x ∈ p, scalarSpecMap (PowerSeries.mapAlgHom ρ) ≫ x = 1) :
    scalarSpecMap (PowerSeries.mapAlgHom ρ) ≫ p.prod = 1 := by
  induction p with
  | nil =>
      rw [List.prod_nil, MonObj.comp_one]
  | cons x xs ih =>
      rw [List.prod_cons, MonObj.comp_mul,
        hp x (List.mem_cons_self),
        ih (fun y hy => hp y (List.mem_cons_of_mem x hy)), one_mul]

end AlgebraicGeometry.IntegralGroupPowerSeries
