/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Schemes.Points.SchemeHomOverExtAlgebraicClosurePoint
public import Nyll.SchemeTheory.Morphisms.AlgebraicPointFiniteField
public import Nyll.SchemeTheory.BaseChange.SchemeHomOver

/-!
# Scheme rigidity from closed points after finite extensions of constants

A rational point over an arbitrary field is determined by its center and
its structural morphism. An algebraic point has a finite field of definition.
Consequently equality on closed points of every finite constant base change
implies equality of the original morphisms, including their residue maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicCurves.Geometry.Schemes.Proofs
open SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

namespace AlgebraicGeometry

universe u

/-- Over any field, two rational sections with the same center coincide. -/
theorem rationalPoint_eq_of_center_eq
    {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (.of k))
    (p q : Spec (.of k) ⟶ X)
    (hp : p ≫ c = 𝟙 _) (hq : q ≫ c = 𝟙 _)
    (h : p (IsLocalRing.closedPoint k) = q (IsLocalRing.closedPoint k)) : p = q := by
  obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective p
  obtain ⟨⟨y, b⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective q
  change (Spec.map a ≫ X.fromSpecResidueField x) ≫ c = 𝟙 _ at hp
  change (Spec.map b ≫ X.fromSpecResidueField y) ≫ c = 𝟙 _ at hq
  change (Spec.map a ≫ X.fromSpecResidueField x) (IsLocalRing.closedPoint k) =
    (Spec.map b ≫ X.fromSpecResidueField y) (IsLocalRing.closedPoint k) at h
  have hx : (Spec.map a ≫ X.fromSpecResidueField x) (IsLocalRing.closedPoint k) = x :=
    (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply x _)
  have hy : (Spec.map b ≫ X.fromSpecResidueField y) (IsLocalRing.closedPoint k) = y :=
    (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply y _)
  have hxy : x = y := hx.symm.trans (h.trans hy)
  subst y
  let s := Spec.preimage (X.fromSpecResidueField x ≫ c)
  have ha : s ≫ a = 𝟙 (CommRingCat.of k) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_id]
    exact (Category.assoc _ _ _).symm.trans hp
  have hb : s ≫ b = 𝟙 (CommRingCat.of k) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_id]
    exact (Category.assoc _ _ _).symm.trans hq
  have hs : Function.Surjective s := by
    intro z
    refine ⟨a z, a.hom.injective ?_⟩
    exact congrArg (fun t : CommRingCat.of k ⟶ CommRingCat.of k => t (a z)) ha
  have : Epi s := ConcreteCategory.epi_of_surjective s hs
  have hab : a = b := (cancel_epi s).mp (ha.trans hb.symm)
  change Spec.map a ≫ X.fromSpecResidueField x = Spec.map b ≫ X.fromSpecResidueField x
  rw [hab]

/-- Actual points over finite subfields of a fixed algebraic closure detect
morphisms of reduced separated schemes locally of finite type over the base. -/
theorem SchemeHomOver.ext_of_finiteIntermediateField_points
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    {Y X : Scheme.{u}} (t : Y ⟶ Spec (.of k)) (s : X ⟶ Spec (.of k))
    [Flat t] [LocallyOfFiniteType t] [IsSeparated t] [IsReduced Y] [IsSeparated s]
    (φ ψ : SchemeHomOver t s)
    (h : ∀ (E : IntermediateField k Ω), Module.Finite k E →
      ∀ q : Spec (.of E) ⟶ Y,
        q ≫ t = Spec.map (CommRingCat.ofHom (algebraMap k E)) → q ≫ φ.val = q ≫ ψ.val) :
    φ = ψ := by
  apply Subtype.ext
  apply RigKerGeomPoints.ext_of_forall_geometric_point
    (L := Ω) (algebraMap k Ω).injective t s φ.val ψ.val φ.property ψ.property
  intro p hp
  obtain ⟨E, hE, q, hq, he⟩ :=
    exists_finite_intermediateField_point_factorization k Ω t p hp
  rw [← he, Category.assoc, Category.assoc, h E hE q hq]

/-- Closed centers on every finite constant extension determine the actual
original scheme morphism. The point comparison is imposed on the literal
base changes, so residue-field embeddings are retained. -/
theorem SchemeHomOver.ext_of_finiteIntermediateField_closedPoints
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    {Y X : Scheme.{u}} (t : Y ⟶ Spec (.of k)) (s : X ⟶ Spec (.of k))
    [Flat t] [LocallyOfFiniteType t] [IsSeparated t] [IsReduced Y] [IsSeparated s]
    (φ ψ : SchemeHomOver t s)
    (h : ∀ (E : IntermediateField k Ω), Module.Finite k E →
      ∀ z : (pullback t (Spec.map (CommRingCat.ofHom (algebraMap k E))) : Scheme.{u}),
        IsClosed {z} →
        (fibreRestrictAlong (Spec.map (CommRingCat.ofHom (algebraMap k E))) s t φ).val z =
          (fibreRestrictAlong (Spec.map (CommRingCat.ofHom (algebraMap k E))) s t ψ).val z) :
    φ = ψ := by
  apply SchemeHomOver.ext_of_finiteIntermediateField_points k Ω t s φ ψ
  intro E hE q hq
  let b := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let qE : Spec (.of E) ⟶ pullback t b :=
    pullback.lift q (𝟙 _) (hq.trans (Category.id_comp b).symm)
  have hqE : qE ≫ pullback.snd t b = 𝟙 _ := pullback.lift_snd _ _ _
  have : IsClosedImmersion qE := isClosedImmersion_of_comp_eq_id _ _ hqE
  let zE : Spec (.of E) := IsLocalRing.closedPoint E
  have hzE : IsClosed ({zE} : Set (Spec (.of E))) :=
    IsLocalRing.isClosed_singleton_closedPoint E
  have hz : IsClosed ({qE zE} : Set (pullback t b : Scheme.{u})) := by
    rw [← Set.image_singleton]
    exact qE.isClosedMap _ hzE
  let φE := fibreRestrictAlong b s t φ
  let ψE := fibreRestrictAlong b s t ψ
  have he : qE ≫ φE.val = qE ≫ ψE.val :=
    rationalPoint_eq_of_center_eq (pullback.snd s b) _ _
      (by rw [Category.assoc, φE.property, hqE])
      (by rw [Category.assoc, ψE.property, hqE])
      (h E hE (qE zE) hz)
  have hp := congrArg (fun a => a ≫ pullback.fst s b) he
  simpa only [φE, ψE, Category.assoc, fibreRestrictAlong_coe_comp_fst,
    qE, pullback.lift_fst_assoc] using hp

end AlgebraicGeometry
