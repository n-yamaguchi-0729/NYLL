/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Geometry.RelativeGroupLawPullbackCompEqMulEq
public import Nyll.AbelianVarieties.Basic
public import Nyll.AbelianVarieties.Reduction.Inertia
public import Nyll.AbelianVarieties.Reduction.GoodModelPointComparison
public import Nyll.AbelianVarieties.Tate.Representation
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Good reduction and the unramified Tate representation

Good reduction means existence of an actual abelian scheme with a group isomorphism
from its generic fiber to the given group. The forward inertia criterion is proved
for this original group, using the equivariant comparison with the model.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq.DescB

namespace GoodReductionJacobian.RelativeGroupLaw

/-- An abelian scheme model, together with a group isomorphism of its generic fiber
with the given group over the fraction field. -/
def HasGoodReduction (R : Type u) [CommRing R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)} (L : RelativeGroupLaw K f) : Prop :=
  ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
    (e : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) f),
    AbelianSchemePropertyBundle R g ∧ LB.IsCommutative ∧ IsIso e.1 ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e =
          L.mul t (NeronModelInfra.schemeHomOverComp x e)
            (NeronModelInfra.schemeHomOverComp y e)

/-- Good reduction implies that inertia acts trivially on the Tate module of the
original abelian variety. This uses the actual model and its generic-fiber group
isomorphism; finite-level fixedness is derived from properness. -/
theorem HasGoodReduction.inertiaSubgroupIn_le_primePowerTateKer
    {R K Ω : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    {L : RelativeGroupLaw K f} (hgood : L.HasGoodReduction R K) (hc : L.IsCommutative)
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : R))
    (W : ValuationSubring Ω) (hW : ∀ r : R, algebraMap R Ω r ∈ W) :
    W.inertiaSubgroupIn K ≤ (TateModule.rep p (L.AlgPoints hc Ω) (Ω ≃ₐ[K] Ω)).ker := by
  obtain ⟨B, g, LB, e, hB, hcB, he, hemul⟩ := hgood
  have : IsProper g := hB.proper
  have : IsIso e.1 := he
  have hid : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (CommRingCat.of K)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hsquare : IsPullback e.1 (pullback.snd g (specGenericFibreInclusion R K)) f
      (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
    have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
      rw [hid]
      infer_instance
    apply IsPullback.of_horiz_isIso
    constructor
    rw [hid, Category.comp_id]
    exact e.2
  have hmul (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))) :
      ((LB.baseChange (specGenericFibreInclusion R K)).mul t x y).1 ≫ e.1 =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap K K)))
          ⟨x.1 ≫ e.1, by rw [Category.assoc, hsquare.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ e.1, by rw [Category.assoc, hsquare.w, ← Category.assoc, y.2]⟩).1 := by
    refine (congrArg Subtype.val (hemul t x y)).trans ?_
    exact mul_val_congr L (by rw [hid, Category.comp_id]) _ _ _ _ rfl rfl
  intro σ hσ
  change TateModule.rep p (L.AlgPoints hc Ω) (Ω ≃ₐ[K] Ω) σ = 1
  have hmodel : TateModule.rep p (LB.AlgPoints hcB Ω) (Ω ≃ₐ[R] Ω)
      (σ.restrictScalars R) = 1 := by
    apply TateModule.rep_eq_one_of_forall_torsionBy
    intro n x hx
    apply AlgPoints.toPoint_injective
    apply Subtype.ext
    rw [AlgPoints.toPoint_smul_coe]
    refine LB.specMap_comp_eq_self_of_mem_inertiaSubgroupIn_of_isTorsionPoint
      K hcB (p ^ n) ?_ W hW σ hσ (AlgPoints.toPoint x) ?_
    · simpa only [Nat.cast_pow] using hp.pow n
    · exact (AlgPoints.mem_torsionBy_iff (p ^ n) x).mp hx
  exact (LB.goodModelPrimePowerTateRep_eq_one_iff (R := R) (H := K) (S := K)
    hcB L hc e.1 hsquare hmul Ω p σ).mp hmodel

end GoodReductionJacobian.RelativeGroupLaw
