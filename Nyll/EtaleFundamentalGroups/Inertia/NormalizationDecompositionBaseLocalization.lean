/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaBaseLocalization
public import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Original decomposition groups under base localization

The literal normalization inclusion is equivariant for the original absolute
Galois actions. Contraction along the localization is injective on ideals and
recovers the given prime. Thus its full decomposition subgroup, as well as its
full inertia subgroup, survives unchanged in the actual local ring.
-/

@[expose] public section

noncomputable section

open SchemeTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] normalizationCommAlgGaloisAction

/-- Localizing the actual base at the contracted prime preserves the literal
absolute-Galois decomposition stabilizer, without a comparison premise. -/
theorem normalizationDecomposition_eq_of_primeLocalization
    (A R K L : Type u)
    [CommRing A] [CommRing R] [IsLocalRing R] [Field K] [Field L]
    [Algebra A R] [Algebra A K] [Algebra R K]
    [IsFractionRing A K] [IsFractionRing R K]
    [Algebra K L] [Algebra A L] [Algebra R L]
    [IsScalarTower A K L] [IsScalarTower R K L] [IsScalarTower A R L]
    [IsGalois K L]
    (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsPrime] [Q.LiesOver P] :
    let q := Q.map (normalizationBaseLocalizationRingMap A R L)
    q.IsMaximal ∧
      MulAction.stabilizer Gal(L/K) Q = MulAction.stabilizer Gal(L/K) q := by
  intro q
  let B := normalizationCommAlgCat A L
  let C := integralClosure R L
  let f : B →+* C := normalizationBaseLocalizationRingMap A R L
  let : Algebra B C := f.toAlgebra
  let : Algebra (integralClosure A L) (integralClosure R L) :=
    (normalizationBaseLocalizationRingMap A R L).toAlgebra
  let : Algebra A C := inferInstanceAs (Algebra A (integralClosure R L))
  let : Algebra B L := inferInstanceAs (Algebra (integralClosure A L) L)
  let : Algebra C L := inferInstanceAs (Algebra (integralClosure R L) L)
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A (integralClosure A L) (integralClosure R L) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower B C L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (integralClosure A L) (integralClosure R L) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A R C := IsScalarTower.of_algebraMap_eq fun a =>
    Subtype.ext (IsScalarTower.algebraMap_apply A R L a)
  have hQrawPrime : (show Ideal (integralClosure A L) from Q).IsPrime := ‹Q.IsPrime›
  have hQrawOver : (show Ideal (integralClosure A L) from Q).LiesOver P := ‹Q.LiesOver P›
  let M := Algebra.algebraMapSubmonoid B P.primeCompl
  have : IsLocalization (Algebra.algebraMapSubmonoid L P.primeCompl) L :=
    IsLocalization.of_le_isUnit fun y hy => by
      obtain ⟨a, ha, rfl⟩ := hy
      change IsUnit (algebraMap A L a)
      rw [isUnit_iff_ne_zero, IsScalarTower.algebraMap_apply A K L,
        map_ne_zero_iff _ (algebraMap K L).injective,
        map_ne_zero_iff _ (IsFractionRing.injective A K)]
      exact fun h => ha (h ▸ P.zero_mem)
  have : IsLocalization M C :=
    IsLocalization.integralClosure (R := A) (S := L) (Rf := R) (Sf := L) P.primeCompl
  have hdisj : Disjoint (M : Set B) (Q : Set B) :=
    Set.disjoint_image_left.mpr (Set.disjoint_compl_left_iff_subset.mpr
      (show Q.under A ≤ P by rw [Q.over_def P]))
  have hunder : q.under B = Q :=
    IsLocalization.under_map_of_isPrime_disjoint M C inferInstance hdisj
  have hmap_smul (σ : Gal(L/K)) (b : B) :
      algebraMap B C (σ • b) = σ • algebraMap B C b := by
    apply Subtype.ext
    have hB := DFunLike.congr_fun
      (normalizationCommAlg_action_comp_inclusion A K L σ) b
    exact hB.symm
  have hcomap_smul (σ : Gal(L/K)) (I : Ideal C) :
      (σ • I).under B = σ • I.under B := by
    ext b
    simp only [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
    change (σ⁻¹ • algebraMap B C b) ∈ I ↔ algebraMap B C (σ⁻¹ • b) ∈ I
    rw [hmap_smul]
  refine ⟨(originalNormalizationInertia_eq_of_primeLocalization A R K L P Q).1, ?_⟩
  ext σ
  change σ • Q = Q ↔ σ • q = q
  constructor
  · intro h
    apply (IsLocalization.orderEmbedding M C).injective
    change (σ • q).under B = q.under B
    calc
      (σ • q).under B = σ • q.under B := hcomap_smul σ (show Ideal C from q)
      _ = σ • Q := congrArg (fun I : Ideal B => σ • I) hunder
      _ = Q := h
      _ = q.under B := hunder.symm
  · intro h
    calc
      σ • Q = σ • q.under B := congrArg (fun I : Ideal B => σ • I) hunder.symm
      _ = (σ • q).under B := (hcomap_smul σ (show Ideal C from q)).symm
      _ = q.under B := congrArg (fun I : Ideal (integralClosure R L) => I.under B) h
      _ = Q := hunder

end EtaleFundamentalGroups.Inertia
