/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.EqSndCompCompEqConst
import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveSpaceIntegral
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import Mathlib.Tactic.FinCases

/-! # Morphisms from the projective line to a separated group scheme

The multiplicative parameter acts by `[x:y] ↦ [a*x:y]`. Rigidity applied to
the quotient of the translated map by the original map makes this quotient
constant on each projective-line fibre. The fixed point `[0:1]` makes it the
identity. The orbit of `[1:1]` is dense, proving constancy of the original map.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
open scoped CategoryTheory.MonObj
open AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjectiveLineGroupConstancy

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev grading (R : Type u) [CommRing R] :=
  MvPolynomial.homogeneousSubmodule (Fin 2) R

private abbrev line (R : Type u) [CommRing R] : Scheme.{u} := Proj (grading R)

private instance chartIndexUnique : Unique {i : Fin 2 // i ≠ 1} where
  default := ⟨0, by decide⟩
  uniq := by
    rintro ⟨i, hi⟩
    apply Subtype.ext
    fin_cases i
    · rfl
    · exact (hi rfl).elim

private def chartEquiv (R : Type u) [CommRing R] :
    Polynomial R ≃ₐ[R] Away (grading R) (MvPolynomial.X (1 : Fin 2)) :=
  (MvPolynomial.uniqueAlgEquiv R {i : Fin 2 // i ≠ 1}).symm.trans
    (awayChartEquiv (S := R) 1 1)

private theorem chartEquiv_X (R : Type u) [CommRing R] :
    chartEquiv R Polynomial.X = ProjSpace.ratio R 1 1 0 := by
  change awayChartEquiv (S := R) 1 1
    (Polynomial.eval₂ MvPolynomial.C
      (MvPolynomial.X (default : {i : Fin 2 // i ≠ 1})) Polynomial.X) = _
  rw [Polynomial.eval₂_X]
  exact awayChartEquiv_X (S := R) 1 1 ⟨0, by decide⟩

private theorem chartEquiv_C (R : Type u) [CommRing R] (r : R) :
    chartEquiv R (Polynomial.C r) = algebraMap R _ r := by
  change chartEquiv R (algebraMap R (Polynomial R) r) = _
  exact (chartEquiv R).commutes r

private def chart (R : Type u) [CommRing R] : Spec (.of (Polynomial R)) ⟶ line R :=
  Spec.map (CommRingCat.ofHom (chartEquiv R).symm.toRingHom) ≫
    Proj.awayι (grading R) (MvPolynomial.X (1 : Fin 2))
      (ProjSpace.X_mem_one R 1 1) one_pos

private instance chart_isOpenImmersion (R : Type u) [CommRing R] :
    IsOpenImmersion (chart R) := by
  unfold chart
  have : IsIso (Spec.map (CommRingCat.ofHom (chartEquiv R).symm.toRingHom)) :=
    inferInstanceAs (IsIso (Spec.map (chartEquiv R).symm.toRingEquiv.toCommRingCatIso.hom))
  infer_instance

private theorem chart_comp_π (R : Type u) [CommRing R] :
    chart R ≫ ProjSpace.π R 1 = Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R))) := by
  unfold chart
  rw [Category.assoc, ProjSpace.awayι_comp_π, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (chartEquiv R).symm.toAlgHom.comp_algebraMap

private def point (R : Type u) [CommRing R] (a : R) : Spec (.of R) ⟶ line R :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫ chart R

private theorem point_comp_π (R : Type u) [CommRing R] (a : R) :
    point R a ≫ ProjSpace.π R 1 = 𝟙 _ := by
  rw [point, Category.assoc, chart_comp_π, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : (Polynomial.evalRingHom a).comp (algebraMap R (Polynomial R)) = RingHom.id R := by
    apply RingHom.ext
    intro r
    exact Polynomial.eval_C
  rw [h]
  exact Spec.map_id _

private def scaledGraded {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) : grading R →+*ᵍ grading S where
  toRingHom := (MvPolynomial.aeval
    (fun i => if i = 0 then MvPolynomial.C (a : S) * MvPolynomial.X 0
      else MvPolynomial.X 1)).toRingHom.comp (MvPolynomial.map f)
  map_mem {i} {p} hp := by
    have hhom (j : Fin 2) :
        (if j = 0 then MvPolynomial.C (a : S) * MvPolynomial.X 0
          else MvPolynomial.X 1 : MvPolynomial (Fin 2) S).IsHomogeneous 1 := by
      split_ifs
      · exact MvPolynomial.isHomogeneous_C_mul_X _ _
      · exact MvPolynomial.isHomogeneous_X _ _
    change (MvPolynomial.aeval _ (MvPolynomial.map f p)) ∈ grading S i
    apply (MvPolynomial.mem_homogeneousSubmodule i _).mpr
    have h := (((MvPolynomial.mem_homogeneousSubmodule i p).mp hp).map f).aeval _ hhom
    simpa only [one_mul] using h

private theorem scaledGraded_C {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) (r : R) :
    scaledGraded f a (MvPolynomial.C r) = MvPolynomial.C (f r) := by
  change MvPolynomial.aeval _ (MvPolynomial.map f (MvPolynomial.C r)) = _
  rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
  rfl

private theorem scaledGraded_X_zero {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) :
    scaledGraded f a (MvPolynomial.X (0 : Fin 2)) =
      MvPolynomial.C (a : S) * MvPolynomial.X 0 := by
  change MvPolynomial.aeval _ (MvPolynomial.map f (MvPolynomial.X (0 : Fin 2))) = _
  rw [MvPolynomial.map_X, MvPolynomial.aeval_X, ite_eq_left rfl]

private theorem scaledGraded_X_one {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) :
    scaledGraded f a (MvPolynomial.X (1 : Fin 2)) = MvPolynomial.X 1 := by
  change MvPolynomial.aeval _ (MvPolynomial.map f (MvPolynomial.X (1 : Fin 2))) = _
  rw [MvPolynomial.map_X, MvPolynomial.aeval_X,
    ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]

private theorem scaledGraded_irrelevant {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) :
    HomogeneousIdeal.irrelevant (grading S) ≤
      HomogeneousIdeal.map (scaledGraded f a) (HomogeneousIdeal.irrelevant (grading R)) := by
  change (HomogeneousIdeal.irrelevant (grading S)).toIdeal ≤ _
  apply (ProjSpace.irrelevant_le_span_X S 1).trans
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have hi : scaledGraded f a (MvPolynomial.X i) ∈
      (HomogeneousIdeal.map (scaledGraded f a)
        (HomogeneousIdeal.irrelevant (grading R))).toIdeal :=
    Ideal.mem_map_of_mem (scaledGraded f a).toRingHom
    (HomogeneousIdeal.mem_irrelevant_of_mem (grading R) one_pos
      (ProjSpace.X_mem_one R 1 i))
  fin_cases i
  · change scaledGraded f a (MvPolynomial.X (0 : Fin 2)) ∈ _ at hi
    rw [scaledGraded_X_zero] at hi
    have hm := Ideal.mul_mem_left
      (HomogeneousIdeal.map (scaledGraded f a)
        (HomogeneousIdeal.irrelevant (grading R))).toIdeal
      (MvPolynomial.C ((a⁻¹ : Sˣ) : S)) hi
    change MvPolynomial.X (0 : Fin 2) ∈
      (HomogeneousIdeal.map (scaledGraded f a)
        (HomogeneousIdeal.irrelevant (grading R))).toIdeal
    simpa only [← mul_assoc, ← map_mul,
      Units.inv_mul, map_one, one_mul] using hm
  · change scaledGraded f a (MvPolynomial.X (1 : Fin 2)) ∈ _ at hi
    rw [scaledGraded_X_one] at hi
    exact hi

private def scaledMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) : line S ⟶ line R :=
  Proj.map (scaledGraded f a) (scaledGraded_irrelevant f a)

private def chartMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) : Polynomial R →+* Polynomial S :=
  Polynomial.eval₂RingHom (Polynomial.C.comp f) (Polynomial.C (a : S) * Polynomial.X)

private def scaledAway {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) :
    Away (grading R) (MvPolynomial.X (1 : Fin 2)) →+*
      Away (grading S) (MvPolynomial.X (1 : Fin 2)) :=
  scaledGraded_X_one f a ▸ Away.map (scaledGraded f a) (MvPolynomial.X (1 : Fin 2))

private theorem scaledAway_mk {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) (d : ℕ) (p : MvPolynomial (Fin 2) R)
    (hp : p ∈ grading R (d • 1)) :
    scaledAway f a (Away.mk (grading R) (ProjSpace.X_mem_one R 1 1) d p hp) =
      Away.mk (grading S) (ProjSpace.X_mem_one S 1 1) d
        (scaledGraded f a p) ((scaledGraded f a).map_mem hp) := by
  have haux : ∀ {y : MvPolynomial (Fin 2) S}
      (h : scaledGraded f a (MvPolynomial.X (1 : Fin 2)) = y)
      (hy : y ∈ grading S 1),
      (h ▸ Away.map (scaledGraded f a) (MvPolynomial.X (1 : Fin 2)))
        (Away.mk (grading R) (ProjSpace.X_mem_one R 1 1) d p hp) =
      Away.mk (grading S) hy d (scaledGraded f a p) ((scaledGraded f a).map_mem hp) := by
    intro y h hy
    subst h
    exact Away.map_mk (scaledGraded f a) (MvPolynomial.X (1 : Fin 2))
      (ProjSpace.X_mem_one R 1 1) d p hp
  exact haux (scaledGraded_X_one f a) (ProjSpace.X_mem_one S 1 1)

private theorem scaledAway_algebraMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) (r : R) :
    scaledAway f a (algebraMap R _ r) = algebraMap S _ (f r) := by
  rw [algebraMap_eq_mk_zero 1 1, scaledAway_mk, algebraMap_eq_mk_zero 1 1]
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, Away.val_mk, scaledGraded_C]

private theorem scaledAway_ratio {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) :
    scaledAway f a (ProjSpace.ratio R 1 1 0) =
      algebraMap S _ (a : S) * ProjSpace.ratio S 1 1 0 := by
  rw [ProjSpace.ratio, scaledAway_mk]
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, scaledGraded_X_zero,
    HomogeneousLocalization.val_mul, ProjSpace.val_algebraMap,
    ProjSpace.ratio, Away.val_mk, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul]
  simp only [one_mul]

private theorem scaledAway_chartEquiv {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) :
    (scaledAway f a).comp (chartEquiv R).toRingHom =
      (chartEquiv S).toRingHom.comp (chartMap f a) := by
  apply Polynomial.ringHom_ext
  · intro r
    change scaledAway f a (chartEquiv R (Polynomial.C r)) =
      chartEquiv S (chartMap f a (Polynomial.C r))
    rw [chartMap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      RingHom.comp_apply, chartEquiv_C, scaledAway_algebraMap, chartEquiv_C]
  · change scaledAway f a (chartEquiv R Polynomial.X) =
      chartEquiv S (chartMap f a Polynomial.X)
    rw [chartEquiv_X, scaledAway_ratio, chartMap, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, map_mul, chartEquiv_C, chartEquiv_X]

private theorem scaledMap_chart {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) :
    chart S ≫ scaledMap f a = Spec.map (CommRingCat.ofHom (chartMap f a)) ≫ chart R := by
  have haway :
      Proj.awayι (grading S) (MvPolynomial.X (1 : Fin 2))
        (ProjSpace.X_mem_one S 1 1) one_pos ≫ scaledMap f a =
      Spec.map (CommRingCat.ofHom (scaledAway f a)) ≫
        Proj.awayι (grading R) (MvPolynomial.X (1 : Fin 2))
          (ProjSpace.X_mem_one R 1 1) one_pos := by
    have haux : ∀ {y : MvPolynomial (Fin 2) S}
        (h : scaledGraded f a (MvPolynomial.X (1 : Fin 2)) = y)
        (hy : y ∈ grading S 1),
        Proj.awayι (grading S) y hy one_pos ≫ scaledMap f a =
        Spec.map (CommRingCat.ofHom
          (h ▸ Away.map (scaledGraded f a) (MvPolynomial.X (1 : Fin 2)))) ≫
          Proj.awayι (grading R) (MvPolynomial.X (1 : Fin 2))
            (ProjSpace.X_mem_one R 1 1) one_pos := by
      intro y h hy
      subst h
      exact Proj.awayι_comp_map (scaledGraded f a) (scaledGraded_irrelevant f a)
        one_pos (MvPolynomial.X (1 : Fin 2)) (ProjSpace.X_mem_one R 1 1)
    exact haux (scaledGraded_X_one f a) (ProjSpace.X_mem_one S 1 1)
  have heq : (chartEquiv S).symm.toRingHom.comp (scaledAway f a) =
      (chartMap f a).comp (chartEquiv R).symm.toRingHom := by
    apply RingHom.ext
    intro z
    apply (chartEquiv S).injective
    change chartEquiv S ((chartEquiv S).symm (scaledAway f a z)) =
      chartEquiv S (chartMap f a ((chartEquiv R).symm z))
    have h := RingHom.congr_fun (scaledAway_chartEquiv f a) ((chartEquiv R).symm z)
    change scaledAway f a (chartEquiv R ((chartEquiv R).symm z)) =
      chartEquiv S (chartMap f a ((chartEquiv R).symm z)) at h
    simpa only [AlgEquiv.apply_symm_apply] using h
  rw [chart, Category.assoc, haway, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, heq, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rfl

private theorem projMap_congr {R S : Type u} [CommRing R] [CommRing S]
    (f g : grading R →+*ᵍ grading S)
    (hf : HomogeneousIdeal.irrelevant (grading S) ≤
      HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant (grading R)))
    (hg : HomogeneousIdeal.irrelevant (grading S) ≤
      HomogeneousIdeal.map g (HomogeneousIdeal.irrelevant (grading R)))
    (h : f = g) : Proj.map f hf = Proj.map g hg := by
  cases h
  rfl

private theorem scaledMap_coefficient {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] : scaledMap (algebraMap R S) 1 = ProjSpace.map R S 1 := by
  have h : scaledGraded (algebraMap R S) 1 = ProjSpace.mvMapGraded R S 1 := by
    apply GradedRingHom.ext
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
      change scaledGraded (algebraMap R S) 1 (MvPolynomial.C r) =
        MvPolynomial.map (algebraMap R S) (MvPolynomial.C r)
      rw [scaledGraded_C, MvPolynomial.map_C]
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, hp]
      congr 1
      fin_cases i
      · change scaledGraded (algebraMap R S) 1 (MvPolynomial.X (0 : Fin 2)) =
          ProjSpace.mvMapGraded R S 1 (MvPolynomial.X (0 : Fin 2))
        rw [scaledGraded_X_zero, Units.val_one, map_one, one_mul,
          ProjSpace.mvMapGraded_X]
      · change scaledGraded (algebraMap R S) 1 (MvPolynomial.X (1 : Fin 2)) =
          ProjSpace.mvMapGraded R S 1 (MvPolynomial.X (1 : Fin 2))
        rw [scaledGraded_X_one, ProjSpace.mvMapGraded_X]
  unfold scaledMap
  rw [ProjSpace.map_eq]
  exact projMap_congr _ _ _ _ h

private theorem scaledMap_id (R : Type u) [CommRing R] :
    scaledMap (RingHom.id R) 1 = 𝟙 (line R) := by
  have h : scaledGraded (RingHom.id R) 1 = GradedRingHom.id (grading R) := by
    apply GradedRingHom.ext
    intro p
    induction p using MvPolynomial.induction_on with
    | C r => exact scaledGraded_C _ _ _
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, hp]
      congr 1
      fin_cases i
      · change scaledGraded (RingHom.id R) 1 (MvPolynomial.X (0 : Fin 2)) =
          MvPolynomial.X (0 : Fin 2)
        rw [scaledGraded_X_zero, Units.val_one, map_one, one_mul]
      · change scaledGraded (RingHom.id R) 1 (MvPolynomial.X (1 : Fin 2)) =
          MvPolynomial.X (1 : Fin 2)
        exact scaledGraded_X_one _ _
  unfold scaledMap
  exact (projMap_congr _ _ _
    (le_of_eq (HomogeneousIdeal.map_id (I := HomogeneousIdeal.irrelevant (grading R))).symm)
    h).trans Proj.map_id

private theorem scaledGraded_comp {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (a : Sˣ) (b : Tˣ) :
    (scaledGraded g b).comp (scaledGraded f a) =
      scaledGraded (g.comp f) (Units.map g.toMonoidHom a * b) := by
  have h : (scaledGraded g b).toRingHom.comp (scaledGraded f a).toRingHom =
      (scaledGraded (g.comp f) (Units.map g.toMonoidHom a * b)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change scaledGraded g b (scaledGraded f a (MvPolynomial.C r)) =
        scaledGraded (g.comp f) (Units.map g.toMonoidHom a * b) (MvPolynomial.C r)
      rw [scaledGraded_C, scaledGraded_C, scaledGraded_C]
      rfl
    · intro i
      fin_cases i
      · change scaledGraded g b (scaledGraded f a (MvPolynomial.X (0 : Fin 2))) =
          scaledGraded (g.comp f) (Units.map g.toMonoidHom a * b)
            (MvPolynomial.X (0 : Fin 2))
        rw [scaledGraded_X_zero, map_mul, scaledGraded_C, scaledGraded_X_zero,
          scaledGraded_X_zero, Units.val_mul, Units.coe_map, map_mul, mul_assoc]
        rfl
      · change scaledGraded g b (scaledGraded f a (MvPolynomial.X (1 : Fin 2))) =
          scaledGraded (g.comp f) (Units.map g.toMonoidHom a * b)
            (MvPolynomial.X (1 : Fin 2))
        rw [scaledGraded_X_one, scaledGraded_X_one, scaledGraded_X_one]
  exact GradedRingHom.ext (RingHom.congr_fun h)

private theorem scaledMap_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (a : Sˣ) (b : Tˣ) :
    scaledMap g b ≫ scaledMap f a =
      scaledMap (g.comp f) (Units.map g.toMonoidHom a * b) := by
  unfold scaledMap
  rw [← Proj.map_comp]
  exact projMap_congr _ _ _ _ (scaledGraded_comp f g a b)

private theorem scaledMap_comp_π {R S : Type u} [CommRing R] [CommRing S] [IsDomain S]
    (f : R →+* S) (a : Sˣ) :
    scaledMap f a ≫ ProjSpace.π R 1 =
      ProjSpace.π S 1 ≫ Spec.map (CommRingCat.ofHom f) := by
  have : IsIntegral (line S) := ProjSpace.projectiveSpace_isIntegral S 1
  have : IsDominant (chart S) :=
    ⟨(chart S).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace (chart S)⟩
  apply ext_of_isDominant (chart S)
  rw [← Category.assoc, scaledMap_chart, Category.assoc, chart_comp_π,
    ← Category.assoc, chart_comp_π, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun h => Spec.map (CommRingCat.ofHom h))
  apply RingHom.ext
  intro r
  exact Polynomial.eval₂_C _ _

private theorem scaledMap_point {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) (b : S) :
    point S b ≫ scaledMap f a =
      Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom f ((a : S) * b))) ≫ chart R := by
  rw [point, Category.assoc, scaledMap_chart, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change Polynomial.eval b (chartMap f a (Polynomial.C r)) =
      Polynomial.eval₂ f ((a : S) * b) (Polynomial.C r)
    rw [chartMap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      RingHom.comp_apply, Polynomial.eval_C, Polynomial.eval₂_C]
  · change Polynomial.eval b (chartMap f a Polynomial.X) =
      Polynomial.eval₂ f ((a : S) * b) Polynomial.X
    rw [chartMap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval₂_X]

private theorem scaledMap_zero {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Sˣ) :
    point S 0 ≫ scaledMap f a = Spec.map (CommRingCat.ofHom f) ≫ point R 0 := by
  rw [scaledMap_point, mul_zero, point, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change Polynomial.eval₂ f 0 (Polynomial.C r) = f (Polynomial.eval 0 (Polynomial.C r))
    rw [Polynomial.eval₂_C, Polynomial.eval_C]
  · change Polynomial.eval₂ f 0 Polynomial.X = f (Polynomial.eval 0 Polynomial.X)
    rw [Polynomial.eval₂_X, Polynomial.eval_X, map_zero]

private theorem coefficient_point_one {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    point S 1 ≫ scaledMap f 1 = Spec.map (CommRingCat.ofHom f) ≫ point R 1 := by
  rw [scaledMap_point, Units.val_one, one_mul, point, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change Polynomial.eval₂ f 1 (Polynomial.C r) = f (Polynomial.eval 1 (Polynomial.C r))
    rw [Polynomial.eval₂_C, Polynomial.eval_C]
  · change Polynomial.eval₂ f 1 Polynomial.X = f (Polynomial.eval 1 Polynomial.X)
    rw [Polynomial.eval₂_X, Polynomial.eval_X, map_one]

private theorem one_left {S T : Scheme.{u}} (G : Over S) [GrpObj G]
    (t : T ⟶ S) :
    (1 : Over.mk t ⟶ G).left = t ≫ (1 : Over.mk (𝟙 S) ⟶ G).left := by
  have h := MonObj.comp_one (M := G)
    (Over.homMk t : Over.mk t ⟶ Over.mk (𝟙 S))
  exact (congrArg (fun a : Over.mk t ⟶ G => a.left) h).symm

private theorem rigid_action_invariant
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (.of K)) [IsProper fX] [IsIntegral X]
    (fY : Y ⟶ Spec (.of K)) [ConnectedSpace Y]
    (G : Over (Spec (.of K))) [GrpObj G] [IsSeparated G.hom]
    (x₀ : Spec (.of K) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (y₀ : Spec (.of K) ⟶ Y) (hy₀ : y₀ ≫ fY = 𝟙 _)
    (action : pullback fX fY ⟶ X) (haction : action ≫ fX = pullback.fst fX fY ≫ fX)
    (hidentity : pullback.lift (𝟙 X) (fX ≫ y₀)
      (by rw [Category.id_comp, Category.assoc, hy₀, Category.comp_id]) ≫ action = 𝟙 X)
    (hfixed : pullback.lift (fY ≫ x₀) (𝟙 Y)
      (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp]) ≫ action = fY ≫ x₀)
    (q : Over.mk fX ⟶ G) : action ≫ q.left = pullback.fst fX fY ≫ q.left := by
  let p := pullback.fst fX fY ≫ fX
  let a : Over.mk p ⟶ Over.mk fX := Over.homMk action haction
  let b : Over.mk p ⟶ Over.mk fX := Over.homMk (pullback.fst fX fY) rfl
  let d : Over.mk p ⟶ G := (a ≫ q) * (b ≫ q)⁻¹
  let σ := pullback.lift (𝟙 X) (fX ≫ y₀)
    (by rw [Category.id_comp, Category.assoc, hy₀, Category.comp_id])
  let ε := pullback.lift (fY ≫ x₀) (𝟙 Y)
    (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp])
  let σo : Over.mk fX ⟶ Over.mk p := Over.homMk σ
    (by
      change σ ≫ (pullback.fst fX fY ≫ fX) = fX
      rw [← Category.assoc, pullback.lift_fst, Category.id_comp])
  let εo : Over.mk fY ⟶ Over.mk p := Over.homMk ε
    (by
      change ε ≫ (pullback.fst fX fY ≫ fX) = fY
      rw [← Category.assoc, pullback.lift_fst, Category.assoc, hx₀, Category.comp_id])
  have hσa : σo ≫ a = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact hidentity
  have hσb : σo ≫ b = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have hεab : εo ≫ a = εo ≫ b := by
    apply Over.OverMorphism.ext
    exact hfixed.trans (pullback.lift_fst _ _ _).symm
  have hσd : σo ≫ d = 1 := by
    dsimp only [d]
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
      hσa, hσb, Category.id_comp, mul_inv_cancel]
  have hεd : εo ≫ d = 1 := by
    dsimp only [d]
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
      hεab, mul_inv_cancel]
  let e := (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left
  have hσ : σ ≫ d.left = fX ≫ e := by
    change (σo ≫ d).left = _
    rw [hσd, one_left]
  have hε : ε ≫ d.left = fY ≫ e := by
    change (εo ≫ d).left = _
    rw [hεd, one_left]
  have hr := exists_eq_snd_comp_of_comp_eq_const_of_isProper K fX fY inferInstance
    G.hom x₀ hx₀ y₀ hy₀ d.left (Over.w d) e hσ
  have hd : d = 1 := by
    apply Over.OverMorphism.ext
    rw [one_left, hr]
    change pullback.snd fX fY ≫ ε ≫ d.left = p ≫ e
    rw [hε, ← Category.assoc, ← pullback.condition]
  have heq : a ≫ q = b ≫ q := mul_inv_eq_one.mp hd
  exact congrArg (fun f : Over.mk p ⟶ G => f.left) heq

end AlgebraicGeometry.ProjectiveLineGroupConstancy

attribute [local instance] MvPolynomial.gradedAlgebra

open ProjectiveLineGroupConstancy in
/-- Every morphism from the projective line to a separated group scheme over a
field is constant. The group need not be proper, smooth, commutative or connected. -/
theorem AlgebraicGeometry.exists_eq_const_of_projectiveLine_group
    (K : Type u) [Field K] (G : Over (Spec (.of K))) [GrpObj G] [IsSeparated G.hom]
    (q : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K) ⟶ G.left)
    (hq : q ≫ G.hom = ProjSpace.π K 1) :
    ∃ a : Spec (.of K) ⟶ G.left,
      a ≫ G.hom = 𝟙 _ ∧ q = ProjSpace.π K 1 ≫ a := by
  let B := Localization.Away (Polynomial.X : Polynomial K)
  have : IsDomain B := Localization.Away.isDomain Polynomial.X_ne_zero
  have : IsIntegral (line K) := ProjSpace.projectiveSpace_isIntegral K 1
  let κ : K →+* B := algebraMap K B
  let θ : Polynomial K →+* B := algebraMap (Polynomial K) B
  have hκ : θ.comp (algebraMap K (Polynomial K)) = κ := by
    apply RingHom.ext
    intro r
    exact (IsScalarTower.algebraMap_apply K (Polynomial K) B r).symm
  have hu : IsUnit (θ Polynomial.X) := IsLocalization.Away.algebraMap_isUnit Polynomial.X
  let u : Bˣ := hu.unit
  have huval : (u : B) = θ Polynomial.X := hu.unit_spec
  have hone : IsUnit ((Polynomial.evalRingHom (1 : K)) Polynomial.X) := by
    rw [Polynomial.coe_evalRingHom, Polynomial.eval_X]
    exact isUnit_one
  let ev : B →+* K := IsLocalization.Away.lift Polynomial.X hone
  have hevθ : ev.comp θ = Polynomial.evalRingHom (1 : K) :=
    IsLocalization.Away.lift_comp Polynomial.X hone
  have hevκ : ev.comp κ = RingHom.id K := by
    rw [← hκ, ← RingHom.comp_assoc, hevθ]
    apply RingHom.ext
    intro r
    exact Polynomial.eval_C
  have hevu : Units.map ev.toMonoidHom u = 1 := by
    apply Units.ext
    change ev (u : B) = 1
    rw [huval]
    exact (RingHom.congr_fun hevθ Polynomial.X).trans (Polynomial.eval_X)
  let fY := Spec.map (CommRingCat.ofHom κ)
  let y₀ := Spec.map (CommRingCat.ofHom ev)
  have hy₀ : y₀ ≫ fY = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hevκ]
    exact Spec.map_id _
  let E := (ProjSpace.isPullback_map K B 1).isoPullback
  let r := scaledMap κ u
  let d := ProjSpace.map K B 1
  have hd : d = scaledMap κ 1 := scaledMap_coefficient.symm
  have hEf : E.hom ≫ pullback.fst (ProjSpace.π K 1) fY = d :=
    (ProjSpace.isPullback_map K B 1).isoPullback_hom_fst
  have hEs : E.hom ≫ pullback.snd (ProjSpace.π K 1) fY = ProjSpace.π B 1 :=
    (ProjSpace.isPullback_map K B 1).isoPullback_hom_snd
  have hEis : E.inv ≫ ProjSpace.π B 1 = pullback.snd (ProjSpace.π K 1) fY :=
    (ProjSpace.isPullback_map K B 1).isoPullback_inv_snd
  let action := E.inv ≫ r
  have haction : action ≫ ProjSpace.π K 1 =
      pullback.fst (ProjSpace.π K 1) fY ≫ ProjSpace.π K 1 := by
    rw [Category.assoc, scaledMap_comp_π, ← Category.assoc, hEis, ← pullback.condition]
  let s₀ := scaledMap ev 1
  have hs₀d : s₀ ≫ d = 𝟙 _ := by
    rw [hd, scaledMap_comp, hevκ, map_one, one_mul, scaledMap_id]
  have hs₀r : s₀ ≫ r = 𝟙 _ := by
    rw [scaledMap_comp, hevκ, hevu, one_mul, scaledMap_id]
  have hidentity :
      pullback.lift (𝟙 (line K)) (ProjSpace.π K 1 ≫ y₀)
        (by rw [Category.id_comp, Category.assoc, hy₀, Category.comp_id]) ≫ action = 𝟙 _ := by
    have hsection :
        pullback.lift (𝟙 (line K)) (ProjSpace.π K 1 ≫ y₀)
          (by rw [Category.id_comp, Category.assoc, hy₀, Category.comp_id]) = s₀ ≫ E.hom := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, hEf, hs₀d]
      · rw [pullback.lift_snd, Category.assoc, hEs, scaledMap_comp_π]
    rw [hsection, Category.assoc, Iso.hom_inv_id_assoc]
    exact hs₀r
  have hfixed :
      pullback.lift (fY ≫ point K 0) (𝟙 (Spec (.of B)))
        (by rw [Category.assoc, point_comp_π, Category.comp_id, Category.id_comp]) ≫ action =
      fY ≫ point K 0 := by
    have hsection :
        pullback.lift (fY ≫ point K 0) (𝟙 (Spec (.of B)))
          (by rw [Category.assoc, point_comp_π, Category.comp_id, Category.id_comp]) =
        point B 0 ≫ E.hom := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, hEf, hd, scaledMap_zero]
      · rw [pullback.lift_snd, Category.assoc, hEs, point_comp_π]
    rw [hsection, Category.assoc, Iso.hom_inv_id_assoc, scaledMap_zero]
  have hinvariant := rigid_action_invariant K (ProjSpace.π K 1) fY G
    (point K 0) (point_comp_π K 0) y₀ hy₀ action haction hidentity hfixed (Over.homMk q hq)
  let j := Spec.map (CommRingCat.ofHom θ) ≫ chart K
  have hOrbit : point B 1 ≫ r = j := by
    rw [scaledMap_point, mul_one]
    have he : Polynomial.eval₂RingHom κ (u : B) = θ := by
      apply Polynomial.ringHom_ext
      · intro a
        rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        exact (RingHom.congr_fun hκ a).symm
      · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
        exact huval
    rw [he]
  have hconstant : j ≫ q = fY ≫ point K 1 ≫ q := by
    have h := congrArg (fun f => point B 1 ≫ E.hom ≫ f) hinvariant
    simp only [action, Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% hEf] at h
    rw [← Category.assoc, hOrbit, ← Category.assoc, hd,
      coefficient_point_one, Category.assoc] at h
    exact h
  have hj : j ≫ ProjSpace.π K 1 = fY := by
    change (Spec.map (CommRingCat.ofHom θ) ≫ chart K) ≫ ProjSpace.π K 1 = fY
    rw [Category.assoc, chart_comp_π, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hκ]
  let a := point K 1 ≫ q
  have ha : a ≫ G.hom = 𝟙 _ := by
    rw [Category.assoc, hq, point_comp_π]
  refine ⟨a, ha, ?_⟩
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom θ)) := inferInstance
  have : IsOpenImmersion j := inferInstance
  have : IsDominant j :=
    ⟨j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j⟩
  apply ext_of_isDominant_of_isSeparated G.hom
    (by rw [hq, Category.assoc, ha, Category.comp_id]) j
  rw [← Category.assoc, hj]
  exact hconstant
