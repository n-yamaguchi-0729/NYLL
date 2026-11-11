/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.FilteredColimitFiniteFamily
public import Nyll.SchemeTheory.RingTheory.LocalRing.FilteredColimit
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Henselian

/-!
# Henselianity of actual filtered colimits of local rings

A monic polynomial and an approximate simple root descend to one actual
stage. Localness of the original cocone map reflects the derivative unit
and preserves the maximal ideal. Henselianity at that stage therefore
supplies the root in the supplied colimit ring.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Polynomial

namespace CommRingCat

variable {I : Type u} [SmallCategory I] [IsFiltered I]

/-- A monic polynomial over the supplied filtered colimit is the image
of a monic polynomial at an actual stage. -/
theorem monic_exists_representative_of_isColimit (D : I ⥤ CommRingCat.{u})
    (c : Cocone D) (hc : IsColimit c) (p : c.pt[X]) (hp : p.Monic) :
    ∃ (i : I) (q : (D.obj i)[X]), q.Monic ∧ q.map (c.ι.app i).hom = p := by
  classical
  obtain ⟨i, a, ha⟩ := lift_finite_family D c hc
    (fun k : Fin p.natDegree => p.coeff k)
  let q : (D.obj i)[X] := X ^ p.natDegree +
    ∑ k : Fin p.natDegree, C (a k) * X ^ (k : ℕ)
  refine ⟨i, q, monic_X_pow_add (degree_sum_fin_lt a), ?_⟩
  change (X ^ p.natDegree + ∑ k : Fin p.natDegree, C (a k) * X ^ (k : ℕ)).map
    (c.ι.app i).hom = p
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, ha]
  change (X : c.pt[X]) ^ p.natDegree +
    ∑ k : Fin p.natDegree, C (p.coeff (k : ℕ)) * (X : c.pt[X]) ^ (k : ℕ) = p
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => C (p.coeff k) * (X : c.pt[X]) ^ k) p.natDegree]
  exact hp.as_sum.symm

/-- A filtered colimit of henselian local rings along local homomorphisms
is henselian for the actual colimit ring and its actual cocone maps. -/
theorem henselianLocalRing_of_isColimit (D : I ⥤ CommRingCat.{u})
    [∀ i, HenselianLocalRing (D.obj i)] (c : Cocone D) (hc : IsColimit c)
    (hlocal : ∀ {i j : I} (f : i ⟶ j), IsLocalHom (D.map f).hom) :
    HenselianLocalRing c.pt := by
  have : IsLocalRing c.pt := isLocalRing_of_isColimit D c hc
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro p hp a₀ hroot hderivative
  obtain ⟨i, q₀, hq₀, hq₀p⟩ := monic_exists_representative_of_isColimit D c hc p hp
  have hrep : ∃ (j : I) (b₀ : D.obj j), c.ι.app j b₀ = a₀ := by
    exact Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget CommRingCat.{u}) hc) a₀
  obtain ⟨j, b₀, hb₀⟩ := hrep
  let k := IsFiltered.max i j
  let f : i ⟶ k := IsFiltered.leftToMax i j
  let g : j ⟶ k := IsFiltered.rightToMax i j
  let q : (D.obj k)[X] := q₀.map (D.map f).hom
  let b : D.obj k := D.map g b₀
  let e : D.obj k →+* c.pt := (c.ι.app k).hom
  have : IsLocalHom e := isLocalHom_ι_of_isColimit D c hc hlocal k
  have hq : q.Monic := hq₀.map (D.map f).hom
  have hqp : q.map e = p := by
    change (q₀.map (D.map f).hom).map (c.ι.app k).hom = p
    rw [Polynomial.map_map]
    have he : (c.ι.app k).hom.comp (D.map f).hom = (c.ι.app i).hom :=
      congrArg (fun t : D.obj i ⟶ c.pt => t.hom) (c.w f)
    rw [he]
    exact hq₀p
  have hb : e b = a₀ :=
    (ConcreteCategory.congr_hom (c.w g) b₀).trans hb₀
  have hrootk : q.eval b ∈ IsLocalRing.maximalIdeal (D.obj k) := by
    rw [← IsLocalRing.maximalIdeal_comap e]
    change e (q.eval b) ∈ IsLocalRing.maximalIdeal c.pt
    rw [← Polynomial.eval_map_apply, hqp, hb]
    exact hroot
  have hderivativek : IsUnit (q.derivative.eval b) := by
    apply isUnit_of_map_unit e
    rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, hqp, hb]
    exact hderivative
  obtain ⟨a, ha, hab⟩ := HenselianLocalRing.is_henselian q hq b hrootk hderivativek
  refine ⟨e a, ?_, ?_⟩
  · change p.eval (e a) = 0
    rw [← hqp, Polynomial.eval_map_apply, ha, map_zero]
  · have hm := map_nonunit e (a - b) hab
    rwa [map_sub, hb] at hm

end CommRingCat
