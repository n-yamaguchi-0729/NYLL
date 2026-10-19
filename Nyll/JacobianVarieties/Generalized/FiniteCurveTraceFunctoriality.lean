/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FiniteCurveTrace
import Nyll.SchemeTheory.GroupSchemes.GeometricPointHom
import Nyll.JacobianVarieties.Albanese.FiniteSums
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Group operations and target functoriality of the regular trace

On a reduced target curve, equality on geometric points identifies the
actual regular trace maps. Their fibre formulas use the same full Cartier
tuple, so the trace preserves group operations, commutes with group
homomorphisms, and is independent of the point used in its construction.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem relativeHom_ext_geometric
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsReduced X] (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (f g : SchemeHomOver x G.X.hom)
    (h : ∀ (L : Type u) [Field L] [IsAlgClosed L] (a : Spec (CommRingCat.of L) ⟶ X),
      GoodReductionJacobian.schemeHomOverComp a rfl f =
        GoodReductionJacobian.schemeHomOverComp a rfl g) : f = g := by
  have : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced X)
  apply (commGroupPointEquiv G x).injective
  apply GroupSchemes.hom_ext_geometricPoints
  intro L fieldL closedL t a
  apply Over.OverMorphism.ext
  exact congrArg Subtype.val (h L a.left)

private theorem pointEquiv_one
    {K : Type u} [Field K] (G : CommGrp (Over (Spec (CommRingCat.of K))))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    commGroupPointEquiv G t ((commGroupRelativeLaw G).one t) = 1 := by
  exact (commGroupPointEquiv G t).apply_symm_apply 1

private theorem pointEquiv_mul
    {K : Type u} [Field K] (G : CommGrp (Over (Spec (CommRingCat.of K))))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t G.X.hom) :
    commGroupPointEquiv G t ((commGroupRelativeLaw G).mul t x y) =
      commGroupPointEquiv G t x * commGroupPointEquiv G t y := by
  exact (commGroupPointEquiv G t).apply_symm_apply _

private theorem pointEquiv_sumList
    {K : Type u} [Field K] (G : CommGrp (Over (Spec (CommRingCat.of K))))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (xs : List (SchemeHomOver t G.X.hom)) :
    commGroupPointEquiv G t ((commGroupRelativeLaw G).sumList t xs) =
      (xs.map (commGroupPointEquiv G t)).prod := by
  induction xs with
  | nil => exact pointEquiv_one G t
  | cons x xs ih =>
      rw [RelativeGroupLaw.sumList_cons, pointEquiv_mul, ih, List.map_cons, List.prod_cons]

private theorem sumList_map_one
    {K : Type u} [Field K] {B T : Scheme.{u}} {b : B ⟶ Spec (CommRingCat.of K)}
    (G : RelativeGroupLaw K b) (t : T ⟶ Spec (CommRingCat.of K))
    {J : Type*} (xs : List J) : G.sumList t (xs.map fun _ => G.one t) = G.one t := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, G.sumList_cons, ih, G.one_mul]

private theorem sumList_map_mul
    {K : Type u} [Field K] (G : CommGrp (Over (Spec (CommRingCat.of K))))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    {J : Type*} (xs : List J) (f g : J → SchemeHomOver t G.X.hom) :
    (commGroupRelativeLaw G).sumList t
        (xs.map fun i => (commGroupRelativeLaw G).mul t (f i) (g i)) =
      (commGroupRelativeLaw G).mul t
        ((commGroupRelativeLaw G).sumList t (xs.map f))
        ((commGroupRelativeLaw G).sumList t (xs.map g)) := by
  apply (commGroupPointEquiv G t).injective
  rw [pointEquiv_mul, pointEquiv_sumList, pointEquiv_sumList, pointEquiv_sumList]
  simp only [List.map_map, Function.comp_def, pointEquiv_mul]
  exact List.prod_map_mul

private theorem sumList_postcomp
    {K : Type u} [Field K] (G H : CommGrp (Over (Spec (CommRingCat.of K))))
    (φ : G ⟶ H) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (xs : List (SchemeHomOver t G.X.hom)) :
    let φ₀ : SchemeHomOver G.X.hom H.X.hom :=
      ⟨φ.hom.hom.hom.left, Over.w φ.hom.hom.hom⟩
    NeronModelInfra.schemeHomOverComp ((commGroupRelativeLaw G).sumList t xs) φ₀ =
      (commGroupRelativeLaw H).sumList t
        (xs.map fun x => NeronModelInfra.schemeHomOverComp x φ₀) := by
  intro φ₀
  have hφ (x : SchemeHomOver t G.X.hom) :
      commGroupPointEquiv H t (NeronModelInfra.schemeHomOverComp x φ₀) =
        commGroupPointEquiv G t x ≫ φ.hom.hom.hom := rfl
  have hm (z : Over.mk t ⟶ G.X) :
      IsMonHom.monoidHom φ.hom.hom.hom (Over.mk t) z = z ≫ φ.hom.hom.hom := rfl
  apply (commGroupPointEquiv H t).injective
  rw [hφ, pointEquiv_sumList, pointEquiv_sumList]
  simpa only [List.map_map, Function.comp_def, hφ, hm] using
    map_list_prod (IsMonHom.monoidHom φ.hom.hom.hom (Over.mk t))
      (xs.map (commGroupPointEquiv G t))

variable {K : Type u} [Field K] {C B : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (b : B ⟶ Spec (CommRingCat.of K)) [IsSeparated b] [IsReduced B]
  (π : C ⟶ B) (hπ : π ≫ b = c)
  [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
  (n : ℕ) (hn : ∀ y : B, π.finrank y = n) (U : C.Opens)
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ c))
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]

/-- The regular trace does not depend on the rational point used to construct its sum map. -/
theorem finiteCurveTrace_independent_basepoint
    (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ c))
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom) :
    finiteCurveTrace c b π hπ n hn U ε G q =
      finiteCurveTrace c b π hπ n hn U ε' G q := by
  apply relativeHom_ext_geometric _ G
  intro L fieldL closedL a
  obtain ⟨xs, hxs, he⟩ := finiteCurveTrace_geometric_fibre c b π hπ n hn U ε G q a
  exact he.trans (finiteCurveTrace_evaluate_tuple c b π hπ n hn U ε' G q a xs hxs).symm

/-- The regular trace of the identity-valued map is the identity-valued map. -/
theorem finiteCurveTrace_one :
    finiteCurveTrace c b π hπ n hn U ε G ((commGroupRelativeLaw G).one (U.ι ≫ c)) =
      (commGroupRelativeLaw G).one ((finiteMapTraceLocus c b π hπ n hn U).ι ≫ b) := by
  apply relativeHom_ext_geometric _ G
  intro L fieldL closedL a
  obtain ⟨xs, _, he⟩ := finiteCurveTrace_geometric_fibre c b π hπ n hn U ε G
    ((commGroupRelativeLaw G).one (U.ι ≫ c)) a
  rw [he, (commGroupRelativeLaw G).one_natural]
  have hp (i : Fin n) : NeronModelInfra.schemeHomOverComp (xs i)
      ((commGroupRelativeLaw G).one (U.ι ≫ c)) =
      (commGroupRelativeLaw G).one (a ≫ ((finiteMapTraceLocus c b π hπ n hn U).ι ≫ b)) :=
    (commGroupRelativeLaw G).one_natural _ _ (xs i).1 (xs i).2
  simp only [hp]
  simpa only [List.map_ofFn, Function.comp_def] using
    sumList_map_one (commGroupRelativeLaw G) _ (List.ofFn fun i : Fin n => i)

/-- The regular trace preserves multiplication of maps to the given commutative group. -/
theorem finiteCurveTrace_mul (q₁ q₂ : SchemeHomOver (U.ι ≫ c) G.X.hom) :
    finiteCurveTrace c b π hπ n hn U ε G ((commGroupRelativeLaw G).mul (U.ι ≫ c) q₁ q₂) =
      (commGroupRelativeLaw G).mul ((finiteMapTraceLocus c b π hπ n hn U).ι ≫ b)
        (finiteCurveTrace c b π hπ n hn U ε G q₁)
        (finiteCurveTrace c b π hπ n hn U ε G q₂) := by
  apply relativeHom_ext_geometric _ G
  intro L fieldL closedL a
  obtain ⟨xs, hxs, he₁⟩ := finiteCurveTrace_geometric_fibre c b π hπ n hn U ε G q₁ a
  have he₂ := finiteCurveTrace_evaluate_tuple c b π hπ n hn U ε G q₂ a xs hxs
  have he := finiteCurveTrace_evaluate_tuple c b π hπ n hn U ε G
    ((commGroupRelativeLaw G).mul (U.ι ≫ c) q₁ q₂) a xs hxs
  rw [he, (commGroupRelativeLaw G).mul_natural, he₁, he₂]
  have hp (i : Fin n) : NeronModelInfra.schemeHomOverComp (xs i)
      ((commGroupRelativeLaw G).mul (U.ι ≫ c) q₁ q₂) =
      (commGroupRelativeLaw G).mul (a ≫ ((finiteMapTraceLocus c b π hπ n hn U).ι ≫ b))
        (NeronModelInfra.schemeHomOverComp (xs i) q₁)
        (NeronModelInfra.schemeHomOverComp (xs i) q₂) :=
    (commGroupRelativeLaw G).mul_natural _ _ (xs i).1 (xs i).2 q₁ q₂
  simp only [hp]
  simpa only [List.map_ofFn, Function.comp_def] using
    sumList_map_mul G _ (List.ofFn fun i : Fin n => i)
    (fun i => NeronModelInfra.schemeHomOverComp (xs i) q₁)
    (fun i => NeronModelInfra.schemeHomOverComp (xs i) q₂)

/-- The actual regular trace commutes with homomorphisms of its target group. -/
theorem finiteCurveTrace_postcomp
    (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated H.X.hom]
    (φ : G ⟶ H) (q : SchemeHomOver (U.ι ≫ c) G.X.hom) :
    let φ₀ : SchemeHomOver G.X.hom H.X.hom :=
      ⟨φ.hom.hom.hom.left, Over.w φ.hom.hom.hom⟩
    finiteCurveTrace c b π hπ n hn U ε H (NeronModelInfra.schemeHomOverComp q φ₀) =
      NeronModelInfra.schemeHomOverComp (finiteCurveTrace c b π hπ n hn U ε G q) φ₀ := by
  intro φ₀
  apply relativeHom_ext_geometric _ H
  intro L fieldL closedL a
  obtain ⟨xs, hxs, heG⟩ := finiteCurveTrace_geometric_fibre c b π hπ n hn U ε G q a
  have heH := finiteCurveTrace_evaluate_tuple c b π hπ n hn U ε H
    (NeronModelInfra.schemeHomOverComp q φ₀) a xs hxs
  have hcomp : GoodReductionJacobian.schemeHomOverComp a rfl
      (NeronModelInfra.schemeHomOverComp (finiteCurveTrace c b π hπ n hn U ε G q) φ₀) =
      NeronModelInfra.schemeHomOverComp
        (GoodReductionJacobian.schemeHomOverComp a rfl
          (finiteCurveTrace c b π hπ n hn U ε G q)) φ₀ := by
    apply Subtype.ext
    exact (Category.assoc _ _ _).symm
  rw [heH, hcomp, heG, sumList_postcomp]
  congr 1
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.GeneralizedJacobian
