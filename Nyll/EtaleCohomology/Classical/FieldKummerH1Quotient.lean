/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FieldEtaleDimensionShift
public import Nyll.EtaleCohomology.Classical.FieldHilbert90
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Actual field Kummer H1 as the cokernel of the unit power map

Geometric Hilbert 90 and the actual Kummer sequence identify derived
roots-of-unity H1 with the cokernel of multiplication by n on the
additive form of the field's unit group.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace EtaleCohomology

/-- The actual Kummer sequence presents derived H1 as the cokernel of
the power map on actual global unit sections. -/
def fieldKummerSectionCokernelIso
    (K : Type u) [Field K] {n : ℕ}
    (hn : 0 < n) (hnK : IsUnit (n : Γ(Spec (.of K), ⊤))) :
    cokernel ((etaleMultiplicativeGroupPower (Spec (.of K)) n).hom.app
      (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))) ≅
      AddCommGrpCat.of (Sheaf.H.{u}
        (etaleRootsOfUnitySheaf (Spec (.of K)) n) 1) :=
  fieldEtaleH1CokernelIso_of_H1_eq_zero K
    (etaleKummerComplex (Spec (.of K)) n)
    (etaleKummerComplex_shortExact (Spec (.of K)) hn hnK)
    (etaleMultiplicativeGroup_H1_eq_zero_of_field K)

/-- Actual derived Kummer H1 is the cokernel of the nth-power map on
the original field's units, written additively. -/
def fieldKummerUnitCokernelIso
    (K : Type u) [Field K] {n : ℕ}
    (hn : 0 < n) (hnK : IsUnit (n : Γ(Spec (.of K), ⊤))) :
    cokernel (n • 𝟙 (AddCommGrpCat.of (Additive Kˣ))) ≅
      AddCommGrpCat.of (Sheaf.H.{u}
        (etaleRootsOfUnitySheaf (Spec (.of K)) n) 1) := by
  let X := Spec (.of K)
  let V := Scheme.Etale.mk (𝟙 X)
  let A := (etaleMultiplicativeGroupSheaf X).obj.obj (op V)
  let e : A ≅ AddCommGrpCat.of (Additive Kˣ) :=
    (etaleMultiplicativeGroupSpecSectionsEquiv X (.of K) (𝟙 X)).toAddCommGrpIso
  let f : A ⟶ A := (etaleMultiplicativeGroupPower X n).hom.app (op V)
  let g := n • 𝟙 (AddCommGrpCat.of (Additive Kˣ))
  have he : f ≫ e.hom = e.hom ≫ g := by
    change (n • 𝟙 A) ≫ e.hom = e.hom ≫ (n • 𝟙 _)
    rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, Category.comp_id]
  exact (cokernel.mapIso (f := f) g e e he).symm ≪≫
    fieldKummerSectionCokernelIso K hn hnK

/-- An exponent invertible in an algebra base is invertible in the actual
field-spectrum sections, through the algebra map and the spectrum sections isomorphism. -/
theorem fieldSections_natCast_isUnit_of_algebra
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    {n : ℕ} (hnR : IsUnit (n : R)) :
    IsUnit (n : Γ(Spec (.of K), ⊤)) := by
  let e := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  have h : IsUnit (n : K) := by
    simpa only [map_natCast] using hnR.map (algebraMap R K)
  simpa only [map_natCast] using h.map e.symm.toRingHom

/-- The actual derived Kummer class of a field unit for an explicitly
invertible exponent. -/
def fieldKummerUnitClassOfIsUnit
    (K : Type u) [Field K] {n : ℕ} (hn : 0 < n)
    (hnK : IsUnit (n : Γ(Spec (.of K), ⊤))) :
    Additive Kˣ →+
      Sheaf.H.{u} (etaleRootsOfUnitySheaf (Spec (.of K)) n) 1 :=
  (fieldKummerUnitCokernelIso K hn hnK).hom.hom.comp
    (cokernel.π (n • 𝟙 (AddCommGrpCat.of (Additive Kˣ)))).hom

/-- Every actual roots-of-unity H1 class for an invertible exponent
comes from the actual Kummer class of a field unit. -/
theorem fieldKummerUnitClassOfIsUnit_surjective
    (K : Type u) [Field K] {n : ℕ} (hn : 0 < n)
    (hnK : IsUnit (n : Γ(Spec (.of K), ⊤))) :
    Function.Surjective (fieldKummerUnitClassOfIsUnit K hn hnK) := by
  let e := fieldKummerUnitCokernelIso K hn hnK
  exact ((AddCommGrpCat.epi_iff_surjective e.hom).mp inferInstance).comp
    ((AddCommGrpCat.epi_iff_surjective
      (cokernel.π (n • 𝟙 (AddCommGrpCat.of (Additive Kˣ))))).mp inferInstance)

/-- An nth power has zero actual derived Kummer class. -/
theorem fieldKummerUnitClassOfIsUnit_nsmul_eq_zero
    (K : Type u) [Field K] {n : ℕ} (hn : 0 < n)
    (hnK : IsUnit (n : Γ(Spec (.of K), ⊤)))
    (a : Additive Kˣ) : fieldKummerUnitClassOfIsUnit K hn hnK (n • a) = 0 := by
  let f := n • 𝟙 (AddCommGrpCat.of (Additive Kˣ))
  have h := ConcreteCategory.congr_hom (cokernel.condition f) a
  change (cokernel.π f).hom (n • a) = 0 at h
  change (fieldKummerUnitCokernelIso K hn hnK).hom.hom ((cokernel.π f).hom (n • a)) = 0
  rw [h, map_zero]

/-- A field unit has zero actual derived Kummer class precisely when it
is an nth power, in additive notation on the group of units. -/
theorem fieldKummerUnitClassOfIsUnit_eq_zero_iff
    (K : Type u) [Field K] {n : ℕ} (hn : 0 < n)
    (hnK : IsUnit (n : Γ(Spec (.of K), ⊤)))
    (x : Additive Kˣ) :
    fieldKummerUnitClassOfIsUnit K hn hnK x = 0 ↔ ∃ y : Additive Kˣ, n • y = x := by
  let f := n • 𝟙 (AddCommGrpCat.of (Additive Kˣ))
  let e := fieldKummerUnitCokernelIso K hn hnK
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.Exact := ShortComplex.exact_cokernel f
  constructor
  · intro hx
    have hπ : (cokernel.π f).hom x = 0 := by
      apply (AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance
      change fieldKummerUnitClassOfIsUnit K hn hnK x = e.hom.hom 0
      rw [hx, map_zero]
    obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff S).mp hS x hπ
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    exact fieldKummerUnitClassOfIsUnit_nsmul_eq_zero K hn hnK y

/-- A positive integer is a unit in the global sections of a characteristic-zero field. -/
theorem fieldSections_natCast_isUnit
    (K : Type u) [Field K] [CharZero K] {n : ℕ} (hn : 0 < n) :
    IsUnit (n : Γ(Spec (.of K), ⊤)) :=
  fieldSections_natCast_isUnit_of_algebra K K
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)))

/-- The actual derived Kummer class of a field unit, with invertibility
of the coefficient integer supplied by characteristic zero. -/
def fieldKummerUnitClass
    (K : Type u) [Field K] [CharZero K] {n : ℕ} (hn : 0 < n) :
    Additive Kˣ →+
      Sheaf.H.{u} (etaleRootsOfUnitySheaf (Spec (.of K)) n) 1 :=
  fieldKummerUnitClassOfIsUnit K hn (fieldSections_natCast_isUnit K hn)

/-- Every actual roots-of-unity H1 class over a characteristic-zero field
comes from the actual Kummer class of a field unit. -/
theorem fieldKummerUnitClass_surjective
    (K : Type u) [Field K] [CharZero K] {n : ℕ} (hn : 0 < n) :
    Function.Surjective (fieldKummerUnitClass K hn) :=
  fieldKummerUnitClassOfIsUnit_surjective K hn (fieldSections_natCast_isUnit K hn)

/-- An nth power has zero actual derived Kummer class. -/
theorem fieldKummerUnitClass_nsmul_eq_zero
    (K : Type u) [Field K] [CharZero K] {n : ℕ} (hn : 0 < n)
    (a : Additive Kˣ) : fieldKummerUnitClass K hn (n • a) = 0 :=
  fieldKummerUnitClassOfIsUnit_nsmul_eq_zero K hn
    (fieldSections_natCast_isUnit K hn) a

/-- A field unit has zero actual derived Kummer class precisely when it
is an nth power, in additive notation on the group of units. -/
theorem fieldKummerUnitClass_eq_zero_iff
    (K : Type u) [Field K] [CharZero K] {n : ℕ} (hn : 0 < n)
    (x : Additive Kˣ) :
    fieldKummerUnitClass K hn x = 0 ↔ ∃ y : Additive Kˣ, n • y = x :=
  fieldKummerUnitClassOfIsUnit_eq_zero_iff K hn (fieldSections_natCast_isUnit K hn) x

end EtaleCohomology
