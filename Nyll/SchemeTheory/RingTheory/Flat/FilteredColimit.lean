/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.FilteredColimitFiniteFamily
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness of actual filtered colimit maps with varying base

A finite relation in the colimit lifts to one stage, and vanishes at a
later stage. Flatness there supplies a trivialization of that relation.
Its actual images give a trivialization in the original colimit rings.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace CommRingCat

variable {I : Type u} [SmallCategory I] [IsFiltered I]

private theorem exists_trivialization_of_flat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    {n : ℕ} (a : Fin n → R) (x : Fin n → S)
    (h : ∑ i, f (a i) * x i = 0) :
    ∃ (m : ℕ) (b : Fin n → Fin m → R) (y : Fin m → S),
      (∀ i, x i = ∑ j, f (b i j) * y j) ∧ ∀ j, ∑ i, a i * b i j = 0 := by
  let _fAlgebra : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hf
  exact Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h

/-- A natural map of filtered ring diagrams whose components are flat
induces a flat map on the actual colimits. Both base and target may vary. -/
theorem flat_of_isColimits
    (A B : I ⥤ CommRingCat.{u}) (φ : A ⟶ B)
    (cA : Cocone A) (cB : Cocone B) (hA : IsColimit cA) (hB : IsColimit cB)
    (f : cA.pt ⟶ cB.pt)
    (hf : ∀ i, cA.ι.app i ≫ f = φ.app i ≫ cB.ι.app i)
    (hflat : ∀ i, (φ.app i).hom.Flat) : f.hom.Flat := by
  classical
  let _fAlgebra : Algebra cA.pt cB.pt := f.hom.toAlgebra
  apply Module.Flat.of_forall_isTrivialRelation
  intro n a x hax
  change ∑ k, f (a k) * x k = 0 at hax
  obtain ⟨iA, a₀, ha₀⟩ := lift_finite_family A cA hA a
  obtain ⟨iB, x₀, hx₀⟩ := lift_finite_family B cB hB x
  let i := IsFiltered.max iA iB
  let p : iA ⟶ i := IsFiltered.leftToMax iA iB
  let q : iB ⟶ i := IsFiltered.rightToMax iA iB
  let ai : Fin n → A.obj i := fun k => A.map p (a₀ k)
  let xi : Fin n → B.obj i := fun k => B.map q (x₀ k)
  have hai (k) : cA.ι.app i (ai k) = a k :=
    (ConcreteCategory.congr_hom (cA.w p) (a₀ k)).trans (ha₀ k)
  have hxi (k) : cB.ι.app i (xi k) = x k :=
    (ConcreteCategory.congr_hom (cB.w q) (x₀ k)).trans (hx₀ k)
  have hzero : cB.ι.app i (∑ k, φ.app i (ai k) * xi k) = cB.ι.app i 0 := by
    rw [map_sum, map_zero]
    have hφ (k) : cB.ι.app i (φ.app i (ai k)) = f (a k) :=
      (ConcreteCategory.congr_hom (hf i) (ai k)).symm.trans (congrArg f (hai k))
    simpa only [map_mul, hφ, hxi] using hax
  obtain ⟨j, t, ht⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget _) hB) _ _).mp hzero
  let aj : Fin n → A.obj j := fun k => A.map t (ai k)
  let xj : Fin n → B.obj j := fun k => B.map t (xi k)
  have haj (k) : cA.ι.app j (aj k) = a k :=
    (ConcreteCategory.congr_hom (cA.w t) (ai k)).trans (hai k)
  have hxj (k) : cB.ι.app j (xj k) = x k :=
    (ConcreteCategory.congr_hom (cB.w t) (xi k)).trans (hxi k)
  have hφt (k) : B.map t (φ.app i (ai k)) = φ.app j (aj k) :=
    (ConcreteCategory.congr_hom (φ.naturality t) (ai k)).symm
  have hrel : ∑ k, φ.app j (aj k) * xj k = 0 := by
    change B.map t (∑ k, φ.app i (ai k) * xi k) = B.map t 0 at ht
    simpa only [map_sum, map_mul, map_zero, hφt] using ht
  obtain ⟨m, b, y, hxy, hab⟩ :=
    exists_trivialization_of_flat (φ.app j).hom (hflat j) aj xj hrel
  refine ⟨m, fun k l => cA.ι.app j (b k l), fun l => cB.ι.app j (y l), ?_, ?_⟩
  · intro k
    change x k = ∑ l : Fin m, f (cA.ι.app j (b k l)) *
      (show cB.pt from cB.ι.app j (y l))
    have hφb (l) : cB.ι.app j (φ.app j (b k l)) = f (cA.ι.app j (b k l)) :=
      (ConcreteCategory.congr_hom (hf j) (b k l)).symm
    have he := congrArg (fun z => cB.ι.app j z) (hxy k)
    simpa only [map_sum, map_mul, hφb, hxj] using he
  · intro l
    have he := congrArg (fun z => cA.ι.app j z) (hab l)
    simpa only [map_sum, map_mul, map_zero, haj] using he

end CommRingCat
