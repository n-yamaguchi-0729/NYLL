/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository: https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusIdeal
import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusResidue
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.IdealProductDivisor
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivSum
import Nyll.SchemeTheory.Sheaves.IdealSheafComap
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Scheme ranks and the weighted degree of a modulus

The rank of a closed point divisor is its actual residue-field degree. Products
of divisor ideals then add ranks, retaining each multiplicity of the modulus.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RelEffCartierDiv

/-- If the actual divisor subscheme is the spectrum of a field extension,
its finite flat rank is the degree of that extension. The isomorphism with
the divisor is constructed from the given closed immersion and ideal equality. -/
theorem rank_eq_finrank_of_spec {K L : Type u} [Field K] [Field L] [Algebra K L]
    {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of K)} {r : ℕ}
    (E : RelEffCartierDiv c r (𝟙 (Spec (CommRingCat.of K))))
    (j : Spec (CommRingCat.of L) ⟶ pullback c (𝟙 (Spec (CommRingCat.of K))))
    [IsClosedImmersion j] (hI : E.I = j.ker)
    (hbase : j ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of K))) =
      Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    r = Module.finrank K L := by
  have hker : E.I.subschemeι.ker = j.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hI]
  let e : Spec (CommRingCat.of L) ⟶ E.I.subscheme :=
    IsClosedImmersion.lift E.I.subschemeι j hker.le
  have _ : IsIso e := IsClosedImmersion.isIso_lift E.I.subschemeι j hker
  have he : e ≫ E.I.subschemeι = j := IsClosedImmersion.lift_fac _ _ _
  have _ : IsFinite (E.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of K)))) :=
    E.isFinite
  have _ : Flat (E.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of K)))) := E.flat
  have hcomp : e ≫ (E.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of K)))) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [← Category.assoc, he, hbase]
  have hfinite : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
    rw [← hcomp]
    infer_instance
  have _ : Module.Finite K L := by
    have hh := (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap K L))).mp hfinite
    exact (RingHom.finite_algebraMap).mp hh
  have hdegree : (Spec.map (CommRingCat.ofHom (algebraMap K L))).finrank =
      (E.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of K)))).finrank := by
    rw [← hcomp]
    exact Scheme.Hom.finrank_comp_left_of_isIso e
      (E.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of K))))
  calc
    r = (E.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of K)))).finrank
        (IsLocalRing.closedPoint K) := (E.finrank_eq _).symm
    _ = (Spec.map (CommRingCat.ofHom (algebraMap K L))).finrank
        (IsLocalRing.closedPoint K) := (congrFun hdegree (IsLocalRing.closedPoint K)).symm
    _ = Module.finrank K L := by
      rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
      rfl

end AlgebraicGeometry.RelEffCartierDiv

namespace AlgebraicCurve.Modulus

private theorem degree_single {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (n : ℕ) :
    degree (Finsupp.single v n : Modulus K F) = (n : ℤ) * v.deg := by
  rw [degree, toDivisor, Finsupp.mapRange_single, Divisor.degree_single]

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- The one-fold point ideal is the actual kernel of the residue point. -/
theorem residuePoint_ker :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField,
      (residuePoint c v).ker = curveIdeal c (Finsupp.single v 1) := by
  intro _functionFieldAlgebra v
  classical
  rw [residuePoint, Scheme.Hom.ker_comp_of_isIso]
  have hsingle : curveIdeal c (Finsupp.single v 1) =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨{pointOfPlace c v}, pointOfPlace_closed c v⟩ := by
    change (Finsupp.single v 1).prod (fun w n =>
      Scheme.IdealSheafData.vanishingIdeal
        ⟨{pointOfPlace c w}, pointOfPlace_closed c w⟩ ^ n) = _
    rw [Finsupp.prod_single_index
      (h := fun w n => Scheme.IdealSheafData.vanishingIdeal
        ⟨{pointOfPlace c w}, pointOfPlace_closed c w⟩ ^ n) (pow_zero _), pow_one]
  rw [hsingle, ← Scheme.IdealSheafData.map_bot,
    ← Scheme.nilradical_eq_bot (X := Spec (C.residueField (pointOfPlace c v))),
    ← Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  apply TopologicalSpace.Closeds.ext
  change closure ((C.fromSpecResidueField (pointOfPlace c v)) '' Set.univ) =
    {pointOfPlace c v}
  rw [Set.image_univ, C.range_fromSpecResidueField, (pointOfPlace_closed c v).closure_eq]

/-- A single closed point is realized with rank equal to its residue degree,
using the actual residue point and its kernel. -/
theorem exists_relativeDivisor_single_one_degree :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField,
      ∃ E : RelEffCartierDiv c v.deg (𝟙 (Spec (CommRingCat.of K))),
        E.I = (curveIdeal c (Finsupp.single v 1)).comap
          (pullback.fst c (𝟙 (Spec (CommRingCat.of K)))) := by
  intro _functionFieldAlgebra v
  let f := pullback.fst c (𝟙 (Spec (CommRingCat.of K)))
  have _ : IsClosedImmersion (residuePoint c v) := residuePoint_isClosedImmersion c v
  let j : Spec (CommRingCat.of v.ResidueField) ⟶ pullback c (𝟙 (Spec (CommRingCat.of K))) :=
    inv (pullback.snd f (residuePoint c v)) ≫ pullback.fst f (residuePoint c v)
  have _ : IsClosedImmersion j := inferInstance
  have hjker : j.ker = (curveIdeal c (Finsupp.single v 1)).comap f := by
    dsimp only [j]
    rw [Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, residuePoint_ker]
  have hjf : j ≫ f = residuePoint c v := by
    dsimp only [j]
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  have hbase : j ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of K))) =
      Spec.map (CommRingCat.ofHom (algebraMap K v.ResidueField)) := by
    have hf : f ≫ c = pullback.snd c (𝟙 (Spec (CommRingCat.of K))) := by
      change pullback.fst c (𝟙 (Spec (CommRingCat.of K))) ≫ c = _
      rw [pullback.condition, Category.comp_id]
    rw [← hf, ← Category.assoc, hjf, residuePoint_comp]
  obtain ⟨r, E, hI, _⟩ := exists_relativeDivisor_curveIdeal c (Finsupp.single v 1)
  have hr : r = v.deg :=
    E.rank_eq_finrank_of_spec j (hI.trans hjker.symm) hbase
  subst r
  exact ⟨E, hI⟩

/-- A closed point with multiplicity `n` has finite scheme rank `n` times its
residue-field degree. -/
theorem exists_relativeDivisor_single_degree :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ (v : Place K C.functionField) (n : ℕ),
      ∃ E : RelEffCartierDiv c (n * v.deg) (𝟙 (Spec (CommRingCat.of K))),
        E.I = (curveIdeal c (Finsupp.single v n)).comap
          (pullback.fst c (𝟙 (Spec (CommRingCat.of K)))) := by
  intro _functionFieldAlgebra v n
  induction n with
  | zero =>
    rw [Nat.zero_mul]
    refine ⟨RelEffCartierDiv.empty c (𝟙 (Spec (CommRingCat.of K))), ?_⟩
    rw [RelEffCartierDiv.empty_I, Finsupp.single_zero, curveIdeal_zero,
      Scheme.IdealSheafData.comap_top]
  | succ n ih =>
    obtain ⟨E, hE⟩ := ih
    obtain ⟨P, hP⟩ := exists_relativeDivisor_single_one_degree c v
    obtain ⟨Q, hQ⟩ := RelEffCartierDiv.exists_I_eq_mul E P
    rw [Nat.succ_mul]
    refine ⟨Q, ?_⟩
    rw [hQ, hE, hP, ← Scheme.IdealSheafData.comap_mul, ← curveIdeal_add,
      ← Finsupp.single_add]

/-- Every modulus is realized by an actual effective Cartier divisor whose
finite flat rank is exactly its weighted function-field degree. -/
theorem exists_relativeDivisor_degree :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ D : Modulus K C.functionField,
      ∃ (r : ℕ) (E : RelEffCartierDiv c r (𝟙 (Spec (CommRingCat.of K)))),
        E.I = (curveIdeal c D).comap (pullback.fst c (𝟙 (Spec (CommRingCat.of K)))) ∧
          (r : ℤ) = D.degree ∧ E.I.IsInvertible := by
  intro _functionFieldAlgebra D
  induction D using Finsupp.induction with
  | zero =>
    refine ⟨0, RelEffCartierDiv.empty c (𝟙 (Spec (CommRingCat.of K))), ?_, ?_, ?_⟩
    · rw [RelEffCartierDiv.empty_I, curveIdeal_zero, Scheme.IdealSheafData.comap_top]
    · exact degree_zero.symm
    · exact (RelEffCartierDiv.empty c (𝟙 (Spec (CommRingCat.of K)))).isInvertible_I
  | single_add v n D _ _ ih =>
    obtain ⟨r, E, hE, hr, _⟩ := ih
    obtain ⟨P, hP⟩ := exists_relativeDivisor_single_degree c v n
    obtain ⟨Q, hQ⟩ := RelEffCartierDiv.exists_I_eq_mul P E
    refine ⟨n * v.deg + r, Q, ?_, ?_, Q.isInvertible_I⟩
    · rw [hQ, hP, hE, ← Scheme.IdealSheafData.comap_mul, ← curveIdeal_add]
    · rw [Nat.cast_add, Nat.cast_mul, hr, degree_add, degree_single]

end AlgebraicCurve.Modulus
